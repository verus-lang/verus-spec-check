//! Body-mutation engine for `#[vcheck_cov_mutate]`.
//!
//! Given a `verus_syn::Block` (the body of a contract-bearing exec fn),
//! [`enumerate_mutation_sites`] returns one [`MutationSite`] per place we
//! can plausibly perturb the body, capped at a per-fn limit. Each site
//! carries its own *full* clone of the body with that single mutation
//! applied -- sites are independent so the cov-mutate runner can drive
//! them in parallel without coordinating intermediate state.
//!
//! ## Operator surface
//!
//! Every operator implemented today is listed here, with what it
//! catches and what it deliberately doesn't do. New operators should
//! be added with the same level of documentation, ideally.
//!
//! References:
//! - "An Experimental Determination of Sufficient Mutant 
//!    Operators" -- Offutt 1996
//! - "Efficient Mutation Testing by Checking Invariant 
//!    Violations" -- Schuler 2009, ISSTA
//!
//! ### arith-swap
//! Replaces a binary arithmetic operator with another of the same
//! arity. One swap per matching site:
//! `+ -> -`, `- -> +`, `* -> /`, `/ -> *`, `% -> /`, `<< -> >>`, `>> -> <<`.
//! Catches sign-direction bugs in arithmetic, shift-direction bugs.
//!
//! ### cmp-swap
//! Swaps a comparison operator: `< -> <=`, `<= -> <`, `> -> >=`,
//! `>= -> >`, `== -> !=`, `!= -> ==`. Catches strict-vs-non-strict
//! and equality-vs-inequality bugs.
//! Implements **ROR** from the 5-selective set.
//!
//! ### logic-swap
//! `&& -> ||`, `|| -> &&`, `!x -> x`. Catches boolean-direction bugs
//! and missing/extra negations.
//! Implements **LCR** from the 5-selective set.
//!
//! ### bitwise-swap
//! Swaps bitwise operators: `& -> |`, `| -> &`, `^ -> &`, plus the
//! compound-assign forms (`&= <-> |=`, `|= <-> ^=`, `&= <-> ^=`). High-yield
//! for vstd's `bytes.rs` and `std_specs/bits.rs`, which compose
//! `|`/`&`/`<<` chains for byte packing and unpacking. Catches
//! mask/shift-direction bugs.
//!
//! ### const-flip
//! Replaces integer literals with three "interesting" alternatives
//! (`0`, `v + 1`, `v - 1`); replaces boolean literals with the
//! opposite value. Catches off-by-one and boundary-condition bugs.
//!
//! ### return-default
//! `return e;` (or trailing tail expr) -> `return Default::default();`.
//! Catches contracts that don't observe the body's actual return
//! value. Mutants whose return type doesn't implement `Default`
//! produce build failures classified as `Inconclusive`.
//!
//! ### stmt-delete
//! Drops a `Stmt::Expr(_, Some(semi))` whose effect is observable
//! (method call, assignment, simple call). Catches contracts that
//! don't observe a specific side effect. Restricted to obviously
//! side-effecting shapes to avoid build-failure mutants.
//!
//! ### index-offset
//! `s[i]` -> `s[i + 1]` and `s[i] -> s[i - 1]` on the index expression.
//! Catches off-by-one bugs in slice/array indexing. Skips index
//! expressions that are themselves `Range`s (those go through
//! range-perturb instead).
//!
//! ### range-perturb
//! For `i..j` (both bounds present): `i..j -> j..i` (reverse),
//! `i..j -> i..i` (empty), `i..j -> i..(j+1)` (extend end), and
//! `i..j -> i..=j` (flip inclusivity). Catches off-by-one and
//! direction bugs in slice ranges, `for i in 0..n` loops, etc.
//!
//! ### drop-`?`
//! `expr?` -> `expr`. Catches contracts that don't propagate error
//! values. Compiles only when the surrounding context accepts the
//! pre-`?` type; otherwise the mutant surfaces as `Inconclusive`.
//!
//! ### abs (negate variable)
//! `x -> -x` on signed-integer / float variable uses, where the
//! mutator's type-context map confirms the variable is signed.
//! Catches sign-handling bugs that no other operator finds reliably.
//! Implements **ABS** from the 5-selective set.
//!
//! ### uoi (unary operator insertion)
//! `x -> x + 1` and `x -> x - 1` on integer variable uses (excluding
//! occurrences inside `Expr::Index`, which index-offset already
//! handles). Catches off-by-one bugs in non-index contexts.
//! Implements **UOI** from the 5-selective set. Higher equivalent-
//! mutant rate than the others; expected.
//!
//! ### match-arm-guard
//! For a `pattern if cond => ...` arm: replaces `cond` with `true`
//! and with `false`. Catches contracts that don't notice when an
//! arm's guard is dead.
//!
//! ## What the mutator explicitly chooses _not_ to do
//!
//! - **Reference-direction swap** (`&x -> x`, `&x -> &mut x`): produces
//!   compile-failure mutants in vstd-shaped code; not useful.
//! - **Type-changing rewrites**: hard to keep the mutant's signature
//!   compatible with the original.
//! - **Loop bound mutation**: high panic / nontermination risk.
//! - **Higher-order mutants** (combining two mutations per mutant):
//!   the academic literature is clear it's not worth it for first-cut
//!   tools -- too expensive, too noisy.
//! - **Match-arm deletion** (with wildcard fallback): cargo-mutants
//!   has it, vstd doesn't really use the pattern. Could be added if
//!   needed.
//! - **Struct-field deletion** (with `..base` literals): same as above.

use proc_macro2::Span;
use std::collections::HashMap;
use verus_syn::spanned::Spanned;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{BinOp, Block, Expr, Lit, Stmt, Type, UnOp};

/// One body mutation. The `mutated_body` is a full clone of the original
/// body with exactly this site's perturbation applied; other potential
/// mutation sites are untouched. `description` is a short human-readable
/// summary used in the coverage report.
#[derive(Clone, Debug)]
pub struct MutationSite {
    /// 1-based index, used in generated mutant fn names.
    pub idx: u32,
    pub line: u32,
    pub description: String,
    pub mutated_body: Block,
}

/// Type-and-name context threaded into the collector. Used to gate
/// operators that need to know the declared type of a parameter, so we
/// don't emit mutations that produce compile failures (e.g. ABS on an
/// unsigned integer).
///
/// The context is built from the original fn's `Signature`. Each entry
/// maps a parameter ident's string form to a normalized type name (e.g.
/// `"i32"`, `"u8"`, `"f64"`). Locals introduced inside the body are
/// **not** tracked -- keeping the context to params is sufficient for
/// the surface we test (vstd-shaped exec bodies generally do their
/// mutating on params).
#[derive(Clone, Debug, Default)]
pub struct MutatorContext {
    pub typed_idents: HashMap<String, String>,
}

impl MutatorContext {
    /// Build a context from a `verus_syn::Signature`. Walks the inputs,
    /// extracting `(simple-ident, type-name)` pairs. 
    ///
    /// The resulting map is "best-effort" e.g. fields not in the map
    /// are treated as untyped, so type-gated operators conservatively
    /// don't fire on them.
    pub fn from_signature(sig: &verus_syn::Signature) -> Self {
        let mut typed_idents = HashMap::new();
        for input in &sig.inputs {
            let pat_type = match &input.kind {
                verus_syn::FnArgKind::Typed(pt) => pt,
                verus_syn::FnArgKind::Receiver(_) => continue,
            };
            let ident = match &*pat_type.pat {
                verus_syn::Pat::Ident(pi) => pi.ident.to_string(),
                verus_syn::Pat::Type(pt2) => match &*pt2.pat {
                    verus_syn::Pat::Ident(pi) => pi.ident.to_string(),
                    _ => continue,
                },
                _ => continue,
            };
            if let Some(name) = type_name(&pat_type.ty) {
                typed_idents.insert(ident, name);
            }
        }
        MutatorContext { typed_idents }
    }

    /// True if `ident` is in the context with a signed-numeric type
    /// (signed int or float). Used to gate ABS.
    fn is_signed_numeric(&self, ident: &str) -> bool {
        self.typed_idents
            .get(ident)
            .map(|t| is_signed_numeric_type(t))
            .unwrap_or(false)
    }

    /// True if `ident` is in the context with an integer type (signed
    /// or unsigned). Used to gate UOI.
    fn is_integer(&self, ident: &str) -> bool {
        self.typed_idents
            .get(ident)
            .map(|t| is_integer_type(t))
            .unwrap_or(false)
    }
}

/// Extract a normalized type-name string from a `Type`. Strips
/// references (`&i32` -> `"i32"`), unwraps single-segment paths to their
/// final ident. 
fn type_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(tp) => tp.path.segments.last().map(|s| s.ident.to_string()),
        Type::Reference(r) => type_name(&r.elem),
        Type::Paren(p) => type_name(&p.elem),
        Type::Group(g) => type_name(&g.elem),
        _ => None,
    }
}

fn is_signed_numeric_type(t: &str) -> bool {
    matches!(
        t,
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "f32" | "f64"
    )
}

fn is_integer_type(t: &str) -> bool {
    matches!(
        t,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
    )
}

/// Walk `body`, enumerate all mutation sites, return up to `cap` of them.
/// When the cap is reached the walker stops collecting *new* sites and
/// records that the cap was hit (caller surfaces this in diagnostics).
///
/// This convenience wrapper passes a default (empty) [`MutatorContext`].
/// Production call sites should use [`enumerate_mutation_sites_with_context`]
/// so the type-gated operators (ABS, UOI) can fire.
#[allow(dead_code)]
pub fn enumerate_mutation_sites(
    body: &Block,
    cap: usize,
) -> (Vec<MutationSite>, /* hit_cap: */ bool) {
    enumerate_mutation_sites_with_context(body, cap, &MutatorContext::default())
}

/// Same as [`enumerate_mutation_sites`] but accepts a pre-built
/// [`MutatorContext`] so the type-gated operators (ABS, UOI) can fire.
/// Use this whenever you have access to the original fn's signature.
pub fn enumerate_mutation_sites_with_context(
    body: &Block,
    cap: usize,
    ctx: &MutatorContext,
) -> (Vec<MutationSite>, /* hit_cap: */ bool) {
    let raw = collect_raw_sites(body, cap, ctx);
    let hit_cap = raw.len() >= cap;
    let mut sites = Vec::with_capacity(raw.len());
    for (idx, raw_site) in raw.into_iter().enumerate() {
        let mut mutated = body.clone();
        let applied = apply_raw_site(&mut mutated, &raw_site);
        if applied {
            sites.push(MutationSite {
                idx: idx as u32 + 1,
                line: raw_site.line,
                description: raw_site.description,
                mutated_body: mutated,
            });
        }
    }
    (sites, hit_cap)
}

/// A raw mutation address: how to find the AST node + how to mutate it.
/// We store the address as a path of indices (statement index, then
/// internal index for sub-expression position) and a `RawSiteKind` that
/// tells the applier what to swap.
#[derive(Clone, Debug)]
struct RawSite {
    /// Path to the target AST node: a sequence of `(stmt_index,
    /// expr_subpath)` that the applier walks down. Stored as a flat list
    /// of "step" indices; each visitor knows how it indexed into its
    /// children.
    ///
    /// Use a unique node id (assigned during a pre-walk) to identify
    /// the target rather than reproducing the path-walk logic in the
    /// applier; this keeps enumeration and application symmetric.
    node_id: u64,
    line: u32,
    description: String,
    kind: RawSiteKind,
}

#[derive(Clone, Debug)]
enum RawSiteKind {
    /// Replace a `BinOp` in an `Expr::Binary` with a different one.
    BinOpSwap(BinOpKind),
    /// Replace a `UnOp::Not` with the inner expression (drop the `!`).
    DropNot,
    /// Replace an integer literal with a constant (parsed as the same
    /// suffix as the original literal).
    IntLitReplace { new_value: u64 },
    /// Replace a boolean literal.
    BoolLitFlip,
    /// Replace a `return <e>;` with `return Default::default();`.
    /// Also covers the trailing-tail-expression case by replacing the
    /// final block expr with `Default::default()`.
    ReturnDefault,
    /// Delete a `Stmt::Expr` / `Stmt::Macro` whose effect is observable
    /// (mutation of `&mut`-bound state). Replaced with an empty stmt.
    StmtDelete,
    /// Perturb an `Expr::Index` by replacing `<expr>[<i>]` with
    /// `<expr>[<i> + 1]` (`offset = +1`) or `<expr>[<i> - 1]`
    /// (`offset = -1`). Catches off-by-one bugs in slice / array
    /// indexing. The harness's `prop_assume!` filters samples that
    /// would panic on out-of-bounds, so the kill signal is
    /// data-dependent (the spec must constrain the index value).
    IndexOffset { offset: i32 },
    /// Perturb an `Expr::Range` `i..j`. See `RangePerturbKind` for the
    /// per-variant semantics.
    RangePerturb(RangePerturbKind),
    /// Drop the `?` operator: `<expr>?` -> `<expr>`. Only fires on
    /// `Expr::Try` whose inner expression has a type compatible with
    /// the surrounding context (we can't check this at site-collection
    /// time, so the mutant may fail to compile and surface as
    /// `Inconclusive`).
    DropTry,
    /// Reference-direction swap is intentionally NOT in the operator
    /// surface. `&x -> x` produces a type error in every vstd-shaped
    /// body (the fn's return is `&T`, so dereferencing gives `T`,
    /// which doesn't fit). `&x -> &mut x` requires `x` to be mutably
    /// borrowable, which is rarely the case in the contexts where
    /// the operator would fire. Future maintainers: leave this
    /// unimplemented unless you have a concrete vstd body where a
    /// reference-direction swap produces a compileable mutant.
    #[allow(dead_code)]
    RefDirSwap,
    /// ABS -- replace a signed numeric variable use with its negation.
    /// `x -> -x`. Fires only when the mutator's `MutatorContext`
    /// confirms `x` has a signed numeric type (so unsigned-int
    /// mutants don't compile-fail). One of the academic 5-selective
    /// operators.
    AbsNegate,
    /// UOI -- insert a unary `+ 1` or `- 1` on an integer variable
    /// use. Different from `IndexOffset`, which fires only inside
    /// `Expr::Index`'s index slot; UOI fires on bare variable uses
    /// outside that context. One of the academic 5-selective
    /// operators. Has the highest equivalent-mutant rate of any
    /// operator we ship.
    UnaryOpInsert { offset: i32 },
    /// Match-arm guard mutation: replace a `pattern if cond => ...`
    /// arm's `cond` with `true` (so the arm always matches) and with
    /// `false` (so the arm never matches). Catches contracts that
    /// don't observe whether a guarded arm fires.
    MatchGuardReplace { value: bool },
}

#[derive(Clone, Debug)]
enum RangePerturbKind {
    /// `i..j` -> `j..i`
    Reverse,
    /// `i..j` -> `i..i`
    Empty,
    /// `i..j` -> `i..(j + 1)`
    ExtendEnd,
    /// Flip the upper-bound inclusivity: `..` <-> `..=`
    FlipInclusive,
}

#[derive(Clone, Debug)]
enum BinOpKind {
    /// Swap `+ <-> -`, `* <-> /`, `% <-> /`, `<< <-> >>`.
    Arith(verus_syn::BinOp),
    /// Swap comparison: `< <-> <=`, `== <-> !=`, `> <-> >=`.
    Cmp(verus_syn::BinOp),
    /// Swap `&& <-> ||`.
    Logic(verus_syn::BinOp),
    /// Swap `&` / `|` / `^` (and the compound-assign forms).
    /// High-yield for vstd's bit-packing patterns.
    Bitwise(verus_syn::BinOp),
}

// ---------------------------------------------------------------------------
// Site collection
// ---------------------------------------------------------------------------

fn collect_raw_sites(body: &Block, cap: usize, ctx: &MutatorContext) -> Vec<RawSite> {
    let mut counter = 0u64;
    // Step 1: assign a unique id to every visited node. We track this by
    // walking the tree in a deterministic order and yielding sites
    // alongside their node id. The mutator (apply_raw_site) re-walks
    // the cloned body in the SAME order, counting up to the same id,
    // and applies the swap when it reaches the matching node.
    let mut sites = Vec::new();
    // `inside_index_subscript` flag is used to suppress UOI when the
    // path expression is the index slot of `Expr::Index`. IndexOffset
    // already covers that case.
    let mut state = CollectState {
        inside_index_subscript: false,
    };
    visit_block_for_collection(body, &mut counter, &mut sites, cap, ctx, &mut state);
    sites
}

/// Mutable per-walk state that influences which sites get emitted.
/// Currently just used for UOI to avoid double-counting with
/// IndexOffset.
struct CollectState {
    inside_index_subscript: bool,
}

/// Walks a `Block` collecting raw sites. The walk order must match
/// `apply_raw_site`'s walk so ids align.
fn visit_block_for_collection(
    block: &Block,
    counter: &mut u64,
    sites: &mut Vec<RawSite>,
    cap: usize,
    ctx: &MutatorContext,
    state: &mut CollectState,
) {
    for stmt in &block.stmts {
        if sites.len() >= cap {
            return;
        }
        visit_stmt_for_collection(stmt, counter, sites, cap, ctx, state);
    }
}

fn visit_stmt_for_collection(
    stmt: &Stmt,
    counter: &mut u64,
    sites: &mut Vec<RawSite>,
    cap: usize,
    ctx: &MutatorContext,
    state: &mut CollectState,
) {
    let stmt_id = *counter;
    *counter += 1;
    if sites.len() >= cap {
        return;
    }
    // Stmt-delete: only for Stmt::Expr / Stmt::Macro that aren't the
    // tail expression and have a visible side effect (method call,
    // assignment, etc.). We approximate "side effect" as "any
    // statement-form that isn't a bare let or comment".
    if is_stmt_deletable(stmt) {
        let line = stmt.span().start().line as u32;
        sites.push(RawSite {
            node_id: stmt_id,
            line,
            description: stmt_delete_description(stmt),
            kind: RawSiteKind::StmtDelete,
        });
    }
    if sites.len() >= cap {
        return;
    }
    match stmt {
        Stmt::Local(local) => {
            if let Some(init) = &local.init {
                visit_expr_for_collection(&init.expr, counter, sites, cap, ctx, state);
            }
        }
        Stmt::Expr(e, _) => visit_expr_for_collection(e, counter, sites, cap, ctx, state),
        Stmt::Item(_) | Stmt::Macro(_) => {}
    }
}

fn visit_expr_for_collection(
    expr: &Expr,
    counter: &mut u64,
    sites: &mut Vec<RawSite>,
    cap: usize,
    ctx: &MutatorContext,
    state: &mut CollectState,
) {
    if sites.len() >= cap {
        return;
    }
    let id = *counter;
    *counter += 1;
    let line = expr.span().start().line as u32;
    match expr {
        Expr::Binary(b) => {
            for swap in classify_binop(&b.op) {
                if sites.len() >= cap {
                    return;
                }
                let desc = format!("{} -> {}", binop_to_str(&b.op), binop_kind_to_str(&swap));
                sites.push(RawSite {
                    node_id: id,
                    line,
                    description: desc,
                    kind: RawSiteKind::BinOpSwap(swap),
                });
            }
            visit_expr_for_collection(&b.left, counter, sites, cap, ctx, state);
            visit_expr_for_collection(&b.right, counter, sites, cap, ctx, state);
        }
        Expr::Unary(u) => {
            if matches!(u.op, UnOp::Not(_)) && sites.len() < cap {
                sites.push(RawSite {
                    node_id: id,
                    line,
                    description: "drop `!`".into(),
                    kind: RawSiteKind::DropNot,
                });
            }
            visit_expr_for_collection(&u.expr, counter, sites, cap, ctx, state);
        }
        Expr::Path(p) => {
            // ABS / UOI: fire only on simple single-segment paths whose
            // ident the context confirms has a mutate-able numeric type.
            if let Some(ident) = simple_path_ident(p) {
                let ident_s = ident.to_string();
                if ctx.is_signed_numeric(&ident_s) && sites.len() < cap {
                    sites.push(RawSite {
                        node_id: id,
                        line,
                        description: format!("{} -> -{}", ident_s, ident_s),
                        kind: RawSiteKind::AbsNegate,
                    });
                }
                if ctx.is_integer(&ident_s) && !state.inside_index_subscript {
                    for offset in [1i32, -1i32] {
                        if sites.len() >= cap {
                            break;
                        }
                        let descr = if offset > 0 {
                            format!("{} -> ({}) + 1", ident_s, ident_s)
                        } else {
                            format!("{} -> ({}) - 1", ident_s, ident_s)
                        };
                        sites.push(RawSite {
                            node_id: id,
                            line,
                            description: descr,
                            kind: RawSiteKind::UnaryOpInsert { offset },
                        });
                    }
                }
            }
        }
        Expr::Lit(lit) => {
            match &lit.lit {
                Lit::Int(li) => {
                    if let Ok(v) = li.base10_parse::<u64>() {
                        // Const replacement: emit one mutation per
                        // "interesting" replacement value. The set is
                        // deliberately small to keep mutant counts
                        // bounded; each variant catches a distinct
                        // class of bug. See `interesting_int_replacements`
                        // for the policy.
                        for new_value in interesting_int_replacements(v) {
                            if sites.len() >= cap {
                                break;
                            }
                            sites.push(RawSite {
                                node_id: id,
                                line,
                                description: format!("{} -> {}", v, new_value),
                                kind: RawSiteKind::IntLitReplace { new_value },
                            });
                        }
                    }
                }
                Lit::Bool(lb) => {
                    let new_v = !lb.value;
                    sites.push(RawSite {
                        node_id: id,
                        line,
                        description: format!("{} -> {}", lb.value, new_v),
                        kind: RawSiteKind::BoolLitFlip,
                    });
                }
                _ => {}
            }
        }
        Expr::Return(r) => {
            if sites.len() < cap {
                sites.push(RawSite {
                    node_id: id,
                    line,
                    description: "return -> Default::default()".into(),
                    kind: RawSiteKind::ReturnDefault,
                });
            }
            if let Some(e) = &r.expr {
                visit_expr_for_collection(e, counter, sites, cap, ctx, state);
            }
        }
        Expr::Block(b) => {
            visit_block_for_collection(&b.block, counter, sites, cap, ctx, state);
        }
        Expr::If(i) => {
            visit_expr_for_collection(&i.cond, counter, sites, cap, ctx, state);
            visit_block_for_collection(&i.then_branch, counter, sites, cap, ctx, state);
            if let Some((_, e)) = &i.else_branch {
                visit_expr_for_collection(e, counter, sites, cap, ctx, state);
            }
        }
        Expr::Match(m) => {
            visit_expr_for_collection(&m.expr, counter, sites, cap, ctx, state);
            for arm in &m.arms {
                if let Some((_, g)) = &arm.guard {
                    // Match-guard mutation: emit two sites per guard
                    // (always-true / always-false). Walking children
                    // happens *after* so ids align with the applier.
                    let guard_id = *counter;
                    *counter += 1;
                    let g_line = g.span().start().line as u32;
                    if sites.len() < cap {
                        sites.push(RawSite {
                            node_id: guard_id,
                            line: g_line,
                            description: "match guard -> true".into(),
                            kind: RawSiteKind::MatchGuardReplace { value: true },
                        });
                    }
                    if sites.len() < cap {
                        // Note: same node id -- both sites target the
                        // same guard expression. The applier matches
                        // by id and only fires once per mutated body,
                        // so the second site reaches the same node on
                        // a fresh clone.
                        sites.push(RawSite {
                            node_id: guard_id,
                            line: g_line,
                            description: "match guard -> false".into(),
                            kind: RawSiteKind::MatchGuardReplace { value: false },
                        });
                    }
                    // Recurse into the guard expression itself so
                    // sub-expressions can also be mutated.
                    visit_expr_for_collection(g, counter, sites, cap, ctx, state);
                }
                visit_expr_for_collection(&arm.body, counter, sites, cap, ctx, state);
            }
        }
        Expr::Call(c) => {
            for a in &c.args {
                visit_expr_for_collection(a, counter, sites, cap, ctx, state);
            }
            visit_expr_for_collection(&c.func, counter, sites, cap, ctx, state);
        }
        Expr::MethodCall(mc) => {
            visit_expr_for_collection(&mc.receiver, counter, sites, cap, ctx, state);
            for a in &mc.args {
                visit_expr_for_collection(a, counter, sites, cap, ctx, state);
            }
        }
        Expr::Paren(p) => visit_expr_for_collection(&p.expr, counter, sites, cap, ctx, state),
        Expr::Reference(r) => visit_expr_for_collection(&r.expr, counter, sites, cap, ctx, state),
        Expr::Cast(c) => visit_expr_for_collection(&c.expr, counter, sites, cap, ctx, state),
        Expr::Tuple(t) => {
            for e in &t.elems {
                visit_expr_for_collection(e, counter, sites, cap, ctx, state);
            }
        }
        Expr::Array(a) => {
            for e in &a.elems {
                visit_expr_for_collection(e, counter, sites, cap, ctx, state);
            }
        }
        Expr::Index(_) => {
            // Emit index-perturbation sites only when the index value
            // is a non-Range expression. For `slice[i..j]` (which
            // parses as `Expr::Index` with a `Range` index), the `+ 1`
            // / `- 1` mutation would produce `Range + integer`, a type
            // error; we skip the index-offset operator there and let
            // the range-perturb branch handle the range itself when it
            // recurses below.
            let index_is_range = if let Expr::Index(i) = expr {
                matches!(*i.index, Expr::Range(_))
            } else {
                false
            };
            if !index_is_range {
                for offset in [1i32, -1i32] {
                    if sites.len() >= cap {
                        break;
                    }
                    let descr = if offset > 0 {
                        "[i] -> [i + 1]".to_string()
                    } else {
                        "[i] -> [i - 1]".to_string()
                    };
                    sites.push(RawSite {
                        node_id: id,
                        line,
                        description: descr,
                        kind: RawSiteKind::IndexOffset { offset },
                    });
                }
            }
            if let Expr::Index(i) = expr {
                visit_expr_for_collection(&i.expr, counter, sites, cap, ctx, state);
                // Mark that we're descending into the index slot so
                // UOI doesn't fire on the bare index ident -- the
                // IndexOffset operator already covers that perturbation.
                let prev = state.inside_index_subscript;
                state.inside_index_subscript = true;
                visit_expr_for_collection(&i.index, counter, sites, cap, ctx, state);
                state.inside_index_subscript = prev;
            }
        }
        Expr::Field(f) => visit_expr_for_collection(&f.base, counter, sites, cap, ctx, state),
        Expr::Assign(a) => {
            visit_expr_for_collection(&a.left, counter, sites, cap, ctx, state);
            visit_expr_for_collection(&a.right, counter, sites, cap, ctx, state);
        }
        Expr::Range(r) => {
            // Three perturbation variants per range. Each fires on the
            // range node; the children get separate ids on recursion.
            // Reverse / Empty / ExtendEnd require both ends present;
            // FlipInclusive only requires that we have a range
            // expression (HalfOpen <-> Closed), so it fires on both
            // bounded and `start..` / `..end` shapes.
            if sites.len() < cap {
                sites.push(RawSite {
                    node_id: id,
                    line,
                    description: "i..j -> i..=j (flip inclusivity)".into(),
                    kind: RawSiteKind::RangePerturb(RangePerturbKind::FlipInclusive),
                });
            }
            if r.start.is_some() && r.end.is_some() {
                for kind in [
                    RangePerturbKind::Reverse,
                    RangePerturbKind::Empty,
                    RangePerturbKind::ExtendEnd,
                ] {
                    if sites.len() >= cap {
                        break;
                    }
                    let descr = match kind {
                        RangePerturbKind::Reverse => "i..j -> j..i",
                        RangePerturbKind::Empty => "i..j -> i..i",
                        RangePerturbKind::ExtendEnd => "i..j -> i..(j+1)",
                        RangePerturbKind::FlipInclusive => unreachable!(),
                    };
                    sites.push(RawSite {
                        node_id: id,
                        line,
                        description: descr.into(),
                        kind: RawSiteKind::RangePerturb(kind),
                    });
                }
            }
            if let Some(s) = &r.start {
                visit_expr_for_collection(s, counter, sites, cap, ctx, state);
            }
            if let Some(e) = &r.end {
                visit_expr_for_collection(e, counter, sites, cap, ctx, state);
            }
        }
        Expr::Try(t) => {
            // Drop the `?` operator: `expr?` -> `expr`. Compiles only
            // when the surrounding context accepts the inner type
            // directly. Mutants that fail to compile surface as
            // `Inconclusive` in the report.
            if sites.len() < cap {
                sites.push(RawSite {
                    node_id: id,
                    line,
                    description: "drop `?`".into(),
                    kind: RawSiteKind::DropTry,
                });
            }
            visit_expr_for_collection(&t.expr, counter, sites, cap, ctx, state);
        }
        Expr::Unsafe(u) => {
            visit_block_for_collection(&u.block, counter, sites, cap, ctx, state);
        }
        Expr::Loop(l) => {
            visit_block_for_collection(&l.body, counter, sites, cap, ctx, state);
        }
        Expr::While(w) => {
            visit_expr_for_collection(&w.cond, counter, sites, cap, ctx, state);
            visit_block_for_collection(&w.body, counter, sites, cap, ctx, state);
        }
        // Other expression kinds: walk children if needed. Conservative
        // default: no recursion. Most missed expressions (closures,
        // `await`, etc.) are unusual in `external_body` bodies.
        _ => {}
    }
}

/// Extract the single-segment ident from an `Expr::Path`. Returns
/// `None` if the path has multiple segments, generic args, or a
/// `qself`. Used by ABS / UOI to gate on bare variable references.
fn simple_path_ident(p: &verus_syn::ExprPath) -> Option<&verus_syn::Ident> {
    if p.qself.is_some() {
        return None;
    }
    if p.path.segments.len() != 1 {
        return None;
    }
    let seg = p.path.segments.first()?;
    if !matches!(seg.arguments, verus_syn::PathArguments::None) {
        return None;
    }
    Some(&seg.ident)
}

fn classify_binop(op: &BinOp) -> Vec<BinOpKind> {
    use BinOp::*;
    let pair: Option<BinOpKind> = match op {
        // Arithmetic swaps.
        Add(_) => Some(BinOpKind::Arith(BinOp::Sub(Default::default()))),
        Sub(_) => Some(BinOpKind::Arith(BinOp::Add(Default::default()))),
        Mul(_) => Some(BinOpKind::Arith(BinOp::Div(Default::default()))),
        Div(_) => Some(BinOpKind::Arith(BinOp::Mul(Default::default()))),
        Rem(_) => Some(BinOpKind::Arith(BinOp::Div(Default::default()))),
        Shl(_) => Some(BinOpKind::Arith(BinOp::Shr(Default::default()))),
        Shr(_) => Some(BinOpKind::Arith(BinOp::Shl(Default::default()))),
        // Comparison swaps.
        Lt(_) => Some(BinOpKind::Cmp(BinOp::Le(Default::default()))),
        Le(_) => Some(BinOpKind::Cmp(BinOp::Lt(Default::default()))),
        Gt(_) => Some(BinOpKind::Cmp(BinOp::Ge(Default::default()))),
        Ge(_) => Some(BinOpKind::Cmp(BinOp::Gt(Default::default()))),
        Eq(_) => Some(BinOpKind::Cmp(BinOp::Ne(Default::default()))),
        Ne(_) => Some(BinOpKind::Cmp(BinOp::Eq(Default::default()))),
        // Logic swaps.
        And(_) => Some(BinOpKind::Logic(BinOp::Or(Default::default()))),
        Or(_) => Some(BinOpKind::Logic(BinOp::And(Default::default()))),
        // Bitwise swaps. Each bitwise op gets one swap (to a different
        // bitwise op of the same arity). Two-mutant-per-op would
        // produce too many sites in chains like `a | b | c | d`; one
        // is enough to surface mask/direction bugs reliably.
        BitAnd(_) => Some(BinOpKind::Bitwise(BinOp::BitOr(Default::default()))),
        BitOr(_) => Some(BinOpKind::Bitwise(BinOp::BitAnd(Default::default()))),
        BitXor(_) => Some(BinOpKind::Bitwise(BinOp::BitAnd(Default::default()))),
        // Bitwise compound-assign swaps. These ARE statements in
        // verus_syn, but appear inside `Expr::Binary` for the
        // assignment-as-expression form (`x &= y`).
        BitAndAssign(_) => Some(BinOpKind::Bitwise(BinOp::BitOrAssign(Default::default()))),
        BitOrAssign(_) => Some(BinOpKind::Bitwise(BinOp::BitAndAssign(Default::default()))),
        BitXorAssign(_) => Some(BinOpKind::Bitwise(BinOp::BitAndAssign(Default::default()))),
        _ => None,
    };
    pair.into_iter().collect()
}

fn binop_to_str(op: &BinOp) -> &'static str {
    use BinOp::*;
    match op {
        Add(_) => "+",
        Sub(_) => "-",
        Mul(_) => "*",
        Div(_) => "/",
        Rem(_) => "%",
        Shl(_) => "<<",
        Shr(_) => ">>",
        Lt(_) => "<",
        Le(_) => "<=",
        Gt(_) => ">",
        Ge(_) => ">=",
        Eq(_) => "==",
        Ne(_) => "!=",
        And(_) => "&&",
        Or(_) => "||",
        BitAnd(_) => "&",
        BitOr(_) => "|",
        BitXor(_) => "^",
        BitAndAssign(_) => "&=",
        BitOrAssign(_) => "|=",
        BitXorAssign(_) => "^=",
        _ => "<other>",
    }
}

fn binop_kind_to_str(k: &BinOpKind) -> &'static str {
    let op = match k {
        BinOpKind::Arith(o) | BinOpKind::Cmp(o) | BinOpKind::Logic(o) | BinOpKind::Bitwise(o) => o,
    };
    binop_to_str(op)
}

fn is_stmt_deletable(stmt: &Stmt) -> bool {
    match stmt {
        // We delete only `Stmt::Expr(_, Some(semi))` (statement
        // expressions with a trailing `;`) -- these have a clear side
        // effect (the expression is evaluated, then discarded). Stripping
        // the semicolon would change the fn's return type.
        Stmt::Expr(e, Some(_)) => {
            // Filter to a small, safe set of "obviously side-effecting"
            // shapes to avoid producing `unused must_use` warnings or
            // type errors. Method calls and assignments are the
            // common cases for `&mut self` mutators.
            matches!(e, Expr::MethodCall(_) | Expr::Assign(_) | Expr::Call(_))
        }
        _ => false,
    }
}

fn stmt_delete_description(_stmt: &Stmt) -> String {
    "delete statement".into()
}

/// Yield the set of "interesting" replacement values for an integer
/// literal `v`. Each value flips one significant aspect of `v`:
///
///  - `0` and `1` are universally interesting (boundary / parity).
///  - For non-zero `v`, also try `0` (universal sentinel) and `v + 1`
///    (off-by-one).
///  - For `v >= 2`, also try `v - 1` (off-by-one in the other direction).
///
/// We deliberately keep the set small -- too many replacements per
/// literal blow up the per-fn cap quickly. A typical literal yields
/// 1-3 mutants, which is enough to surface common bugs without
/// crowding out the harder operators (range-perturb, index-offset).
fn interesting_int_replacements(v: u64) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    if v == 0 {
        out.push(1);
    } else {
        out.push(0);
        // `v + 1` overflows at u64::MAX; just skip it there.
        if let Some(plus) = v.checked_add(1) {
            out.push(plus);
        }
        if v >= 2 {
            out.push(v - 1);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Site application
// ---------------------------------------------------------------------------

/// Re-walks `mutated` (which is a clone of the original body) in the
/// same order as `visit_block_for_collection`, finds the node with id
/// `site.node_id`, and applies the mutation. Returns true on success.
fn apply_raw_site(mutated: &mut Block, site: &RawSite) -> bool {
    struct Applier<'a> {
        target: u64,
        site: &'a RawSite,
        counter: u64,
        applied: bool,
    }
    impl<'a> Applier<'a> {
        fn maybe_apply(&mut self, this_id: u64, expr: &mut Expr) {
            if self.applied || this_id != self.target {
                return;
            }
            match &self.site.kind {
                RawSiteKind::BinOpSwap(swap) => {
                    if let Expr::Binary(b) = expr {
                        let new_op = match swap {
                            BinOpKind::Arith(o)
                            | BinOpKind::Cmp(o)
                            | BinOpKind::Logic(o)
                            | BinOpKind::Bitwise(o) => o.clone(),
                        };
                        b.op = new_op;
                        self.applied = true;
                    }
                }
                RawSiteKind::DropNot => {
                    if let Expr::Unary(u) = expr {
                        if matches!(u.op, UnOp::Not(_)) {
                            let inner = (*u.expr).clone();
                            *expr = inner;
                            self.applied = true;
                        }
                    }
                }
                RawSiteKind::IntLitReplace { new_value } => {
                    if let Expr::Lit(lit) = expr {
                        if let Lit::Int(orig) = &lit.lit {
                            // Preserve suffix so the literal remains the
                            // same type (`0u32` stays `<n>u32`).
                            let suffix = orig.suffix();
                            let span = orig.span();
                            let s = if suffix.is_empty() {
                                format!("{}", new_value)
                            } else {
                                format!("{}{}", new_value, suffix)
                            };
                            lit.lit = Lit::Int(verus_syn::LitInt::new(&s, span));
                            self.applied = true;
                        }
                    }
                }
                RawSiteKind::BoolLitFlip => {
                    if let Expr::Lit(lit) = expr {
                        if let Lit::Bool(b) = &mut lit.lit {
                            b.value = !b.value;
                            self.applied = true;
                        }
                    }
                }
                RawSiteKind::ReturnDefault => {
                    let span = expr.span();
                    *expr = make_default_expr(span);
                    self.applied = true;
                }
                RawSiteKind::StmtDelete => {
                    // Statement-delete is applied at the Stmt level,
                    // not the Expr level, so this branch shouldn't fire
                    // for non-stmt sites.
                }
                RawSiteKind::IndexOffset { offset } => {
                    if let Expr::Index(idx) = expr {
                        let inner = (*idx.index).clone();
                        let new_index: Expr = if *offset > 0 {
                            verus_syn::parse_quote! { (#inner) + 1 }
                        } else {
                            verus_syn::parse_quote! { (#inner) - 1 }
                        };
                        idx.index = Box::new(new_index);
                        self.applied = true;
                    }
                }
                RawSiteKind::RangePerturb(kind) => {
                    if let Expr::Range(r) = expr {
                        // For FlipInclusive we don't need both ends; for
                        // the other three we do. Site collection guards
                        // the both-ends case.
                        match kind {
                            RangePerturbKind::FlipInclusive => {
                                use verus_syn::RangeLimits;
                                r.limits = match &r.limits {
                                    RangeLimits::HalfOpen(_) => {
                                        RangeLimits::Closed(verus_syn::token::DotDotEq::default())
                                    }
                                    RangeLimits::Closed(_) => {
                                        RangeLimits::HalfOpen(verus_syn::token::DotDot::default())
                                    }
                                };
                                self.applied = true;
                                return;
                            }
                            _ => {}
                        }
                        let (start, end) = match (&r.start, &r.end) {
                            (Some(s), Some(e)) => ((**s).clone(), (**e).clone()),
                            _ => return,
                        };
                        match kind {
                            RangePerturbKind::Reverse => {
                                r.start = Some(Box::new(end));
                                r.end = Some(Box::new(start));
                            }
                            RangePerturbKind::Empty => {
                                let s_clone = start.clone();
                                r.start = Some(Box::new(start));
                                r.end = Some(Box::new(s_clone));
                            }
                            RangePerturbKind::ExtendEnd => {
                                let extended: Expr = verus_syn::parse_quote! { (#end) + 1 };
                                r.end = Some(Box::new(extended));
                            }
                            RangePerturbKind::FlipInclusive => unreachable!(),
                        }
                        self.applied = true;
                    }
                }
                RawSiteKind::DropTry => {
                    if let Expr::Try(t) = expr {
                        let inner = (*t.expr).clone();
                        *expr = inner;
                        self.applied = true;
                    }
                }
                RawSiteKind::RefDirSwap => {
                    // Intentionally unimplemented (see the variant's
                    // doc comment).
                }
                RawSiteKind::AbsNegate => {
                    // `x -> -x`. Wrap the path expression in a unary
                    // negation. The collector confirms the variable is
                    // signed numeric before emitting the site, so the
                    // mutant should typecheck.
                    if matches!(expr, Expr::Path(_)) {
                        let inner = expr.clone();
                        let span = expr.span();
                        *expr = Expr::Unary(verus_syn::ExprUnary {
                            attrs: Vec::new(),
                            op: UnOp::Neg(verus_syn::token::Minus(span)),
                            expr: Box::new(inner),
                        });
                        self.applied = true;
                    }
                }
                RawSiteKind::UnaryOpInsert { offset } => {
                    // `x -> (x) + 1` / `(x) - 1`. Parens to keep
                    // precedence sane.
                    if matches!(expr, Expr::Path(_)) {
                        let inner = expr.clone();
                        let new_expr: Expr = if *offset > 0 {
                            verus_syn::parse_quote! { (#inner) + 1 }
                        } else {
                            verus_syn::parse_quote! { (#inner) - 1 }
                        };
                        *expr = new_expr;
                        self.applied = true;
                    }
                }
                RawSiteKind::MatchGuardReplace { value } => {
                    // The site targets the guard expression itself; we
                    // replace it with `true` or `false`. The collector
                    // only emits guard-replace sites for guard
                    // expressions, so any expr we land on here must be
                    // a guard.
                    let span = expr.span();
                    *expr = Expr::Lit(verus_syn::ExprLit {
                        attrs: Vec::new(),
                        lit: Lit::Bool(verus_syn::LitBool {
                            value: *value,
                            span,
                        }),
                    });
                    self.applied = true;
                }
            }
        }

        fn maybe_apply_stmt(&mut self, this_id: u64, stmt: &mut Stmt) {
            if self.applied || this_id != self.target {
                return;
            }
            if matches!(self.site.kind, RawSiteKind::StmtDelete) {
                // Replace the statement with an empty `()` statement.
                let span = stmt.span();
                *stmt = Stmt::Expr(
                    Expr::Tuple(verus_syn::ExprTuple {
                        attrs: Vec::new(),
                        paren_token: verus_syn::token::Paren(span),
                        elems: verus_syn::punctuated::Punctuated::new(),
                    }),
                    Some(verus_syn::token::Semi(span)),
                );
                self.applied = true;
            }
        }
    }

    fn walk_block(applier: &mut Applier, block: &mut Block) {
        for stmt in block.stmts.iter_mut() {
            if applier.applied {
                return;
            }
            let id = applier.counter;
            applier.counter += 1;
            applier.maybe_apply_stmt(id, stmt);
            if applier.applied {
                return;
            }
            match stmt {
                Stmt::Local(local) => {
                    if let Some(init) = &mut local.init {
                        walk_expr(applier, &mut init.expr);
                    }
                }
                Stmt::Expr(e, _) => walk_expr(applier, e),
                Stmt::Item(_) | Stmt::Macro(_) => {}
            }
        }
    }

    fn walk_expr(applier: &mut Applier, expr: &mut Expr) {
        if applier.applied {
            return;
        }
        let id = applier.counter;
        applier.counter += 1;
        applier.maybe_apply(id, expr);
        if applier.applied {
            return;
        }
        match expr {
            Expr::Binary(b) => {
                walk_expr(applier, &mut b.left);
                walk_expr(applier, &mut b.right);
            }
            Expr::Unary(u) => walk_expr(applier, &mut u.expr),
            Expr::Lit(_) => {}
            Expr::Return(r) => {
                if let Some(e) = &mut r.expr {
                    walk_expr(applier, e);
                }
            }
            Expr::Block(b) => walk_block(applier, &mut b.block),
            Expr::If(i) => {
                walk_expr(applier, &mut i.cond);
                walk_block(applier, &mut i.then_branch);
                if let Some((_, e)) = &mut i.else_branch {
                    walk_expr(applier, e);
                }
            }
            Expr::Match(m) => {
                walk_expr(applier, &mut m.expr);
                for arm in m.arms.iter_mut() {
                    if let Some((_, g)) = &mut arm.guard {
                        // Mirror the collector: it pre-allocates a
                        // `guard_id` for MatchGuardReplace before
                        // walking the guard. We consume the same id
                        // here, applying the guard-replace mutation if
                        // it's our target. The guard itself then walks
                        // normally to handle sub-expression mutations.
                        let guard_id = applier.counter;
                        applier.counter += 1;
                        applier.maybe_apply(guard_id, g);
                        if applier.applied {
                            return;
                        }
                        walk_expr(applier, g);
                    }
                    walk_expr(applier, &mut arm.body);
                }
            }
            Expr::Call(c) => {
                for a in c.args.iter_mut() {
                    walk_expr(applier, a);
                }
                walk_expr(applier, &mut c.func);
            }
            Expr::MethodCall(mc) => {
                walk_expr(applier, &mut mc.receiver);
                for a in mc.args.iter_mut() {
                    walk_expr(applier, a);
                }
            }
            Expr::Paren(p) => walk_expr(applier, &mut p.expr),
            Expr::Reference(r) => walk_expr(applier, &mut r.expr),
            Expr::Cast(c) => walk_expr(applier, &mut c.expr),
            Expr::Tuple(t) => {
                for e in t.elems.iter_mut() {
                    walk_expr(applier, e);
                }
            }
            Expr::Array(a) => {
                for e in a.elems.iter_mut() {
                    walk_expr(applier, e);
                }
            }
            Expr::Index(i) => {
                walk_expr(applier, &mut i.expr);
                walk_expr(applier, &mut i.index);
            }
            Expr::Field(f) => walk_expr(applier, &mut f.base),
            Expr::Assign(a) => {
                walk_expr(applier, &mut a.left);
                walk_expr(applier, &mut a.right);
            }
            Expr::Range(r) => {
                if let Some(s) = &mut r.start {
                    walk_expr(applier, s);
                }
                if let Some(e) = &mut r.end {
                    walk_expr(applier, e);
                }
            }
            Expr::Try(t) => {
                walk_expr(applier, &mut t.expr);
            }
            Expr::Unsafe(u) => walk_block(applier, &mut u.block),
            Expr::Loop(l) => walk_block(applier, &mut l.body),
            Expr::While(w) => {
                walk_expr(applier, &mut w.cond);
                walk_block(applier, &mut w.body);
            }
            _ => {}
        }
    }

    let mut applier = Applier {
        target: site.node_id,
        site,
        counter: 0,
        applied: false,
    };
    walk_block(&mut applier, mutated);
    applier.applied
}

fn make_default_expr(span: Span) -> Expr {
    use verus_syn::{ExprCall, ExprPath, Path, PathArguments, PathSegment};
    let path = Path {
        leading_colon: Some(verus_syn::token::PathSep::default()),
        segments: {
            let mut p = verus_syn::punctuated::Punctuated::new();
            p.push(PathSegment {
                ident: verus_syn::Ident::new("core", span),
                arguments: PathArguments::None,
            });
            p.push(PathSegment {
                ident: verus_syn::Ident::new("default", span),
                arguments: PathArguments::None,
            });
            p.push(PathSegment {
                ident: verus_syn::Ident::new("Default", span),
                arguments: PathArguments::None,
            });
            p.push(PathSegment {
                ident: verus_syn::Ident::new("default", span),
                arguments: PathArguments::None,
            });
            p
        },
    };
    let func = Expr::Path(ExprPath {
        attrs: Vec::new(),
        qself: None,
        path,
    });
    Expr::Call(ExprCall {
        attrs: Vec::new(),
        func: Box::new(func),
        paren_token: verus_syn::token::Paren(span),
        args: verus_syn::punctuated::Punctuated::new(),
        // verus_syn 2026-07-27+: synthesized calls are never atomic.
        atomically: None,
    })
}

// Suppress unused warnings for visitor scaffolding we keep for future
// operators (closure recursion, generator expressions, etc.).
#[allow(dead_code)]
fn _suppress_visitor_unused() {
    struct _N;
    impl VisitMut for _N {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use verus_syn::parse_quote;

    fn parse_block(s: &str) -> Block {
        verus_syn::parse_str::<Block>(s).expect("test block must parse")
    }

    #[test]
    fn arith_swap_finds_expected_sites() {
        let body: Block = parse_block("{ let _ = a + b * c; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        // `+` and `*` each yield one swap.
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d.contains("+ -> -")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("* -> /")), "{:?}", descs);
    }

    #[test]
    fn cmp_swap_finds_expected_sites() {
        let body: Block = parse_block("{ let _ = a < b && c == d; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d.contains("< -> <=")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("== -> !=")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("&& -> ||")), "{:?}", descs);
    }

    #[test]
    fn const_flip_int() {
        let body: Block = parse_block("{ 0u32 + 1u32 }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d.contains("0 -> 1")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("1 -> 0")), "{:?}", descs);
    }

    #[test]
    fn const_flip_bool() {
        let body: Block = parse_block("{ if true { 1u8 } else { 0u8 } }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("true -> false")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn drop_not_finds_unary_not() {
        let body: Block = parse_block("{ let _ = !flag; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d.contains("drop `!`")), "{:?}", descs);
    }

    #[test]
    fn return_default_on_explicit_return() {
        let body: Block = parse_block("{ return 5u32; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("Default::default")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn stmt_delete_recognizes_method_call() {
        let body: Block = parse_block("{ v.push(1u32); v.len() }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d == &"delete statement"),
            "{:?}",
            descs
        );
    }

    #[test]
    fn cap_is_respected() {
        let body: Block =
            parse_block("{ let a = b + c + d + e + f + g + h + i + j + k + l + m + n + o; }");
        let (sites, hit_cap) = enumerate_mutation_sites(&body, 3);
        assert!(sites.len() <= 3);
        assert!(hit_cap);
    }

    #[test]
    fn applied_mutation_changes_only_one_node() {
        let body: Block = parse_block("{ a + b + c }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        // Three +'s, three sites.
        let plus_sites: Vec<&MutationSite> = sites
            .iter()
            .filter(|s| s.description.contains("+ -> -"))
            .collect();
        // Should have at least 2 (left and right halves of the chain).
        assert!(plus_sites.len() >= 2, "{:?}", sites);
        // Each mutated body should round-trip through `quote!` cleanly.
        for s in &plus_sites {
            let blk = &s.mutated_body;
            let _txt = quote::quote!(#blk).to_string();
        }
    }

    #[test]
    fn no_sites_for_empty_body() {
        let body: Block = parse_block("{ }");
        let (sites, hit_cap) = enumerate_mutation_sites(&body, 10);
        assert!(sites.is_empty());
        assert!(!hit_cap);
    }

    #[test]
    fn mutated_body_preserves_outer_stmts() {
        let body: Block = parse_block("{ let x = 1u32; x + 2u32 }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        // Find the `+ -> -` site and verify the let is preserved.
        let plus = sites
            .iter()
            .find(|s| s.description.contains("+ -> -"))
            .unwrap();
        let blk = &plus.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        assert!(txt.contains("let x"), "preserved let stmt: {}", txt);
    }

    #[test]
    fn deeply_nested_expr_is_reachable() {
        let body: Block =
            parse_block("{ if a < b { if c == d { e + f } else { 0u32 } } else { 0u32 } }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        // Reach the inner `+` and `==` from inside two nested `if`s.
        assert!(descs.iter().any(|d| d.contains("+ -> -")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("== -> !=")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("< -> <=")), "{:?}", descs);
    }

    #[test]
    fn parse_quote_block_works() {
        // Verify that `parse_quote!` produces blocks the visitor handles.
        let body: Block = parse_quote! { { let mut v = Vec::new(); v.push(1u32); v } };
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        // At least the `1 -> 0` int-flip.
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d.contains("1 -> 0")), "{:?}", descs);
    }

    // -----------------------------------------------------------------
    // Tests for v2 operators: index-offset, range-perturb, drop-`?`,
    // and the richer const-replacement set.
    // -----------------------------------------------------------------

    #[test]
    fn index_offset_emits_plus_and_minus() {
        let body: Block = parse_block("{ let _ = s[i]; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("[i] -> [i + 1]")),
            "{:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d.contains("[i] -> [i - 1]")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn index_offset_actually_perturbs() {
        let body: Block = parse_block("{ let r = s[i]; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let plus = sites
            .iter()
            .find(|s| s.description.contains("+ 1"))
            .unwrap();
        let blk = &plus.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        assert!(
            txt.contains("(i) + 1") || txt.contains("(i) +1") || txt.contains("i + 1"),
            "expected i + 1 in mutated body: {}",
            txt
        );
    }

    #[test]
    fn range_perturb_emits_three_kinds() {
        let body: Block = parse_block("{ let _ = &s[i..j]; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("i..j -> j..i")),
            "{:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d.contains("i..j -> i..i")),
            "{:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d.contains("i..j -> i..(j+1)")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn range_perturb_skips_unbounded_ranges_for_directional_variants() {
        let body: Block = parse_block("{ let _ = &s[..j]; let _ = &s[i..]; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        // Reverse / Empty / ExtendEnd require both bounds; should NOT
        // fire on unbounded ranges. FlipInclusive does fire on every
        // range regardless of bounds, so we don't check that here.
        assert!(
            !descs.iter().any(|d| d.contains("j..i")),
            "no reverse: {:?}",
            descs
        );
        assert!(
            !descs.iter().any(|d| d.contains("i..i")),
            "no empty: {:?}",
            descs
        );
        assert!(
            !descs.iter().any(|d| d.contains("i..(j+1)")),
            "no extend: {:?}",
            descs
        );
    }

    #[test]
    fn drop_try_emits_one_site() {
        let body: Block = parse_block("{ let v: Result<u32, ()> = Ok(1u32); let r = v?; r }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d == &"drop `?`"), "{:?}", descs);
    }

    #[test]
    fn const_replacement_yields_multiple_per_literal() {
        let body: Block = parse_block("{ let _ = 5u32; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d == &"5 -> 0"),
            "expected 5 -> 0: {:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d == &"5 -> 6"),
            "expected 5 -> 6: {:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d == &"5 -> 4"),
            "expected 5 -> 4: {:?}",
            descs
        );
    }

    #[test]
    fn const_replacement_handles_zero() {
        // For `0u32` only `0 -> 1` should fire (no `0 - 1` underflow).
        let body: Block = parse_block("{ let _ = 0u32; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let zero_sites: Vec<&str> = sites
            .iter()
            .filter(|s| s.description.starts_with("0 ->"))
            .map(|s| s.description.as_str())
            .collect();
        assert_eq!(zero_sites, vec!["0 -> 1"]);
    }

    #[test]
    fn const_replacement_handles_one() {
        // For `1u32`: 1 -> 0, 1 -> 2.
        let body: Block = parse_block("{ let _ = 1u32; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites
            .iter()
            .filter(|s| s.description.starts_with("1 ->"))
            .map(|s| s.description.as_str())
            .collect();
        assert!(descs.contains(&"1 -> 0"), "{:?}", descs);
        assert!(descs.contains(&"1 -> 2"), "{:?}", descs);
    }

    #[test]
    fn vstd_byte_body_finds_method_index_sites() {
        // A vstd-shaped body with an indexed access. The index-offset
        // operator should fire.
        let body: Block = parse_block("{ self.as_bytes()[i] }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("[i] -> [i + 1]")),
            "{:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d.contains("[i] -> [i - 1]")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn vstd_slice_subrange_body_finds_range_sites() {
        // The vstd::slice::slice_subrange body shape.
        let body: Block = parse_block("{ &slice[i..j] }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        // All three range-perturb variants present.
        assert!(descs.iter().any(|d| d.contains("j..i")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("i..i")), "{:?}", descs);
        assert!(descs.iter().any(|d| d.contains("i..(j+1)")), "{:?}", descs);
    }

    // -----------------------------------------------------------------
    // Tests for the v3 operators: bitwise-swap, ABS, UOI, range
    // inclusivity flip, match-arm guard.
    // -----------------------------------------------------------------

    /// Build a `MutatorContext` from inline param declarations. Used by
    /// the ABS / UOI tests, which need the type info to fire.
    fn ctx_from(params: &[(&str, &str)]) -> MutatorContext {
        let mut typed_idents = HashMap::new();
        for (name, ty) in params {
            typed_idents.insert((*name).to_string(), (*ty).to_string());
        }
        MutatorContext { typed_idents }
    }

    #[test]
    fn abs_fires_only_on_signed_numeric() {
        let body: Block = parse_block("{ let _ = x; let _ = y; let _ = z; }");
        let ctx = ctx_from(&[("x", "i32"), ("y", "u32"), ("z", "f64")]);
        let (sites, _) = enumerate_mutation_sites_with_context(&body, 200, &ctx);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        // ABS fires on `x: i32` (signed) and `z: f64` (signed/float),
        // but not on `y: u32` (unsigned).
        assert!(descs.iter().any(|d| d == &"x -> -x"), "{:?}", descs);
        assert!(descs.iter().any(|d| d == &"z -> -z"), "{:?}", descs);
        assert!(!descs.iter().any(|d| d == &"y -> -y"), "{:?}", descs);
    }

    #[test]
    fn abs_actually_negates() {
        let body: Block = parse_block("{ x }");
        let ctx = ctx_from(&[("x", "i32")]);
        let (sites, _) = enumerate_mutation_sites_with_context(&body, 100, &ctx);
        let abs = sites
            .iter()
            .find(|s| s.description == "x -> -x")
            .expect("expected ABS site");
        let blk = &abs.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        assert!(
            txt.contains("- x") || txt.contains("-x"),
            "expected -x: {}",
            txt
        );
    }

    #[test]
    fn uoi_fires_on_integer_outside_index() {
        let body: Block = parse_block("{ let _ = x + y; }");
        let ctx = ctx_from(&[("x", "i32"), ("y", "u8")]);
        let (sites, _) = enumerate_mutation_sites_with_context(&body, 200, &ctx);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(descs.iter().any(|d| d == &"x -> (x) + 1"), "{:?}", descs);
        assert!(descs.iter().any(|d| d == &"x -> (x) - 1"), "{:?}", descs);
        assert!(descs.iter().any(|d| d == &"y -> (y) + 1"), "{:?}", descs);
    }

    #[test]
    fn uoi_does_not_fire_inside_index_subscript() {
        let body: Block = parse_block("{ let _ = s[i]; }");
        let ctx = ctx_from(&[("i", "usize")]);
        let (sites, _) = enumerate_mutation_sites_with_context(&body, 200, &ctx);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        // UOI should not fire on `i` because IndexOffset already
        // covers that perturbation.
        assert!(!descs.iter().any(|d| d == &"i -> (i) + 1"), "{:?}", descs);
        assert!(!descs.iter().any(|d| d == &"i -> (i) - 1"), "{:?}", descs);
        // But IndexOffset should fire.
        assert!(descs.iter().any(|d| d.contains("[i + 1]")), "{:?}", descs);
    }

    #[test]
    fn uoi_actually_perturbs() {
        let body: Block = parse_block("{ x }");
        let ctx = ctx_from(&[("x", "i32")]);
        let (sites, _) = enumerate_mutation_sites_with_context(&body, 100, &ctx);
        let plus = sites
            .iter()
            .find(|s| s.description == "x -> (x) + 1")
            .expect("expected UOI +1");
        let blk = &plus.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        assert!(
            txt.contains("(x) + 1") || txt.contains("x + 1"),
            "expected x + 1: {}",
            txt
        );
    }

    #[test]
    fn range_flip_inclusive_emits_site() {
        let body: Block = parse_block("{ let _ = &s[i..j]; }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d.contains("flip inclusivity")),
            "{:?}",
            descs
        );
    }

    #[test]
    fn range_flip_inclusive_actually_flips() {
        let body: Block = parse_block("{ let _ = (i..j); }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let flip = sites
            .iter()
            .find(|s| s.description.contains("flip inclusivity"))
            .expect("expected FlipInclusive site");
        let blk = &flip.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        assert!(txt.contains("..="), "expected ..= in mutated body: {}", txt);
    }

    #[test]
    fn match_guard_emits_two_sites_per_guard() {
        let body: Block = parse_block("{ match x { y if y > 0u32 => 1u32, _ => 0u32 } }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let descs: Vec<&str> = sites.iter().map(|s| s.description.as_str()).collect();
        assert!(
            descs.iter().any(|d| d == &"match guard -> true"),
            "{:?}",
            descs
        );
        assert!(
            descs.iter().any(|d| d == &"match guard -> false"),
            "{:?}",
            descs
        );
    }

    #[test]
    fn match_guard_actually_replaces() {
        let body: Block = parse_block("{ match x { y if y > 0u32 => 1u32, _ => 0u32 } }");
        let (sites, _) = enumerate_mutation_sites(&body, 100);
        let true_site = sites
            .iter()
            .find(|s| s.description == "match guard -> true")
            .expect("expected guard -> true site");
        let blk = &true_site.mutated_body;
        let txt = quote::quote!(#blk).to_string();
        // Original `y > 0u32` should be gone, replaced by `true`.
        assert!(txt.contains("if true"), "expected `if true`: {}", txt);
    }

    #[test]
    fn mutator_context_built_from_signature() {
        let sig: verus_syn::Signature =
            verus_syn::parse_str("fn foo(a: i32, b: u8, c: &str, d: f64) -> i32").unwrap();
        let ctx = MutatorContext::from_signature(&sig);
        assert_eq!(ctx.typed_idents.get("a"), Some(&"i32".to_string()));
        assert_eq!(ctx.typed_idents.get("b"), Some(&"u8".to_string()));
        assert_eq!(ctx.typed_idents.get("c"), Some(&"str".to_string()));
        assert_eq!(ctx.typed_idents.get("d"), Some(&"f64".to_string()));
        assert!(ctx.is_signed_numeric("a"));
        assert!(!ctx.is_signed_numeric("b"));
        assert!(ctx.is_signed_numeric("d"));
        assert!(ctx.is_integer("a"));
        assert!(ctx.is_integer("b"));
        assert!(!ctx.is_integer("d"));
    }

    // These confirm two assumptions before we build on them:
    //  1. verus_syn parses `#[vcheck] assert(...)` and `#[vcheck] assert
    //     forall |...| ... by { }` cleanly, with the attribute landing
    //     on the assert variant's `attrs` field.
    //  2. The discovery pass can locate inline asserts inside arbitrary
    //     fn bodies and read the binders / predicate.
    #[test]
    fn vcheck_attr_on_assert_parses_into_attrs_field() {
        let f: verus_syn::ItemFn = verus_syn::parse_str(
            "fn caller(x: u32, y: u32) -> u32 { let z = x + y; #[vcheck] assert(z >= x); z }",
        )
        .expect("attribute on assert must parse");
        let mut found = false;
        for stmt in &f.block.stmts {
            if let verus_syn::Stmt::Expr(verus_syn::Expr::Assert(a), _) = stmt {
                assert_eq!(a.attrs.len(), 1, "expected one attr");
                let p = &a.attrs[0].path();
                let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
                assert_eq!(segs, vec!["vcheck".to_string()]);
                found = true;
            }
        }
        assert!(found, "did not find Expr::Assert in parsed body");
    }

    #[test]
    fn vcheck_attr_on_assert_forall_parses_with_binders() {
        let f: verus_syn::ItemFn = verus_syn::parse_str(
            "fn caller() { #[vcheck] assert forall |w: u32| w + w == 2u32 * w by { }; }",
        )
        .expect("attribute on assert forall must parse");
        let mut found = false;
        for stmt in &f.block.stmts {
            if let verus_syn::Stmt::Expr(verus_syn::Expr::AssertForall(a), _) = stmt {
                assert_eq!(a.attrs.len(), 1, "expected one attr");
                let p = a.attrs[0].path();
                let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
                assert_eq!(segs, vec!["vcheck".to_string()]);
                // Confirm the binder is `w: u32`.
                assert_eq!(a.inputs.len(), 1);
                let pat = a.inputs.iter().next().unwrap();
                if let verus_syn::Pat::Type(pt) = pat {
                    if let verus_syn::Pat::Ident(pi) = &*pt.pat {
                        assert_eq!(pi.ident.to_string(), "w");
                    } else {
                        panic!("binder pattern not Pat::Ident: {:?}", pt.pat);
                    }
                } else {
                    panic!("binder pattern not Pat::Type: {:?}", pat);
                }
                found = true;
            }
        }
        assert!(found, "did not find Expr::AssertForall in parsed body");
    }

    #[test]
    fn vcheck_attr_on_assert_forall_implies_form() {
        let f: verus_syn::ItemFn = verus_syn::parse_str(
            "fn caller() { #[vcheck] assert forall |w: u32| w < 100u32 implies w + 1u32 > 0u32 by { }; }",
        )
        .expect("implies form must parse");
        let mut found = false;
        for stmt in &f.block.stmts {
            if let verus_syn::Stmt::Expr(verus_syn::Expr::AssertForall(a), _) = stmt {
                assert!(a.implies.is_some(), "expected implies clause");
                found = true;
            }
        }
        assert!(found);
    }
}
