//! Dedicated discovery + body-rewriting support for `#[vcheck]` on inline asserts.
//!
//! ## What this module is for
//!
//! Users write `#[vcheck]` on `assert(...)` or `assert forall |...| ... by { }`
//! statements inside the body of an `exec` fn. This module provides the
//! pieces the main `verus_spec_check!{...}` expansion needs to:
//!
//!  1. Find every `#[vcheck]`-marked assert in a function body.
//!  2. Strip the `#[vcheck]` attribute from the assert (so the verifier
//!     doesn't see an unknown attribute when the original fn is later
//!     re-emitted).
//!  3. For path-form `#[vcheck] assert(P)`: produce a *checked clone* of
//!     the body where that single assert is rewritten into an explicit
//!     `if !{P} { panic!(...) }`. Other asserts in the body are left as
//!     `assert(...)` and erase to no-ops at `cargo test` time, since
//!     Verus wraps them in `#[verifier::proof_block]` which the runtime
//!     erases.
//!  4. For forall-form: extract the typed binders + predicate +
//!     optional `implies` antecedent so the harness can sample them
//!     directly.
//!
//! ## What it deliberately doesn't do
//! 
//! This module doesn't do the spec->exec lowering, this doesn't 
//! do any tracking of outer scope, and it doesn't generate any 
//! harnesses directly.

use verus_syn::spanned::Spanned;
use verus_syn::{Assert, AssertForall, Attribute, Block, Error, Expr, Ident, Pat, Stmt, Type};

/// One inline assert annotated with `#[vcheck]`.
#[derive(Clone, Debug)]
pub struct InlineAssertTarget {
    /// String form of the enclosing fn's ident — used for harness
    /// naming. Free fns: just the fn's ident. Methods: `<TypeName>_<method>`
    /// to keep names unique across an impl block.
    pub enclosing_fn_label: String,
    /// Source line of the assert. Embedded in harness fn name so test
    /// output points at the right place.
    pub line: u32,
    /// Per-fn 0-based ordinal — distinguishes multiple inline asserts
    /// in the same fn that happen to share a line.
    pub assert_idx: u32,
    pub kind: InlineAssertKind,
}

/// Path-form vs forall-form.
#[derive(Clone, Debug)]
pub enum InlineAssertKind {
    /// `#[vcheck] assert(P)`. The harness drives the enclosing fn with
    /// random params; the cloned body panics at this assert site if
    /// `P` is false.
    ///
    /// `predicate` is captured for diagnostics / future use but
    /// production rewriting uses `(line, marker_idx)` to locate the
    /// assert in the cloned body, not the predicate text. Kept for
    /// debug visibility.
    Path {
        #[allow(dead_code)]
        predicate: Expr,
    },
    /// `#[vcheck] assert forall |x: T1, y: T2| P(x, y) by { }` and the
    /// `... implies Q(x, y)` form.
    Forall {
        binders: Vec<(Ident, Type)>,
        /// For the basic form: the single predicate.
        /// For implies form: the consequent.
        predicate: Expr,
        /// `Some(antecedent)` for `forall |...| P implies Q`,
        /// `None` for the unconditional form.
        implies: Option<Expr>,
    },
}

/// Returns true if `attr` is the bare `#[vcheck]` marker (no arguments).
/// Inline-assert markers don't take options today; if a user writes
/// `#[vcheck(...)]` on an assert we ignore the args silently and treat it
/// as the bare form. Caller-supplied diagnostics surface argument
/// errors at the item level via the existing `vcheck_attr` machinery.
fn attr_is_vcheck(attr: &Attribute) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    matches!(segs.as_slice(), [s] if s == "vcheck")
}

/// Walk a function body, find every `#[vcheck]`-marked assert, and:
///
///  - Append an `InlineAssertTarget` to `out_targets` for each.
///  - Strip the `#[vcheck]` attribute from the assert so re-emission is
///    clean.
///  - Validate the assert's shape: returns `Err` for unsupported
///    binders or other static-time issues. The first error stops the
///    walk so we don't bury the user in cascaded diagnostics.
///
/// The walk visits stmts in order, descending into nested blocks
/// (loops, ifs, match arms, unsafe, etc.) using a deterministic
/// depth-first order. The `assert_idx` is a per-line ordinal among
/// `Expr::Assert` (path-form) sites, which is what the harness's
/// `rewrite_path_assert_at_line` consumes. Forall-form asserts get
/// `assert_idx = 0` since they have a standalone harness keyed by
/// (fn-label, line) and don't need an ordinal.
pub fn discover_in_block(
    block: &mut Block,
    enclosing_fn_label: &str,
    out_targets: &mut Vec<InlineAssertTarget>,
) -> Result<(), Error> {
    let mut state = DiscoveryState {
        path_idx_per_line: std::collections::HashMap::new(),
    };
    visit_block(block, enclosing_fn_label, &mut state, out_targets)
}

struct DiscoveryState {
    /// Per-source-line counter for path-form asserts only. Used to
    /// hand the rewriter a deterministic "Nth path-form `Expr::Assert`
    /// on line L" ordinal. Forall-form asserts don't increment this.
    path_idx_per_line: std::collections::HashMap<u32, u32>,
}

fn visit_block(
    block: &mut Block,
    label: &str,
    state: &mut DiscoveryState,
    out: &mut Vec<InlineAssertTarget>,
) -> Result<(), Error> {
    for stmt in block.stmts.iter_mut() {
        visit_stmt(stmt, label, state, out)?;
    }
    Ok(())
}

fn visit_stmt(
    stmt: &mut Stmt,
    label: &str,
    state: &mut DiscoveryState,
    out: &mut Vec<InlineAssertTarget>,
) -> Result<(), Error> {
    match stmt {
        Stmt::Local(local) => {
            if let Some(init) = &mut local.init {
                visit_expr(&mut init.expr, label, state, out)?;
            }
        }
        Stmt::Expr(e, _) => {
            visit_expr(e, label, state, out)?;
        }
        Stmt::Item(_) | Stmt::Macro(_) => {}
    }
    Ok(())
}

fn visit_expr(
    expr: &mut Expr,
    label: &str,
    state: &mut DiscoveryState,
    out: &mut Vec<InlineAssertTarget>,
) -> Result<(), Error> {
    // Visit the expr's role first: `Expr::Assert` and
    // `Expr::AssertForall` may themselves be `#[vcheck]`-marked, so
    // intercept before recursing into children.
    match expr {
        Expr::Assert(a) => {
            if take_vcheck_attr(&mut a.attrs) {
                let line = a.assert_token.span.start().line as u32;
                let idx = state.path_idx_per_line.entry(line).or_insert(0);
                let assert_idx = *idx;
                *idx += 1;
                let target = build_path_target(a, label, assert_idx, line)?;
                out.push(target);
                visit_expr(&mut a.expr, label, state, out)?;
                if let Some(body) = &mut a.body {
                    visit_block(body, label, state, out)?;
                }
                return Ok(());
            }
        }
        Expr::AssertForall(a) => {
            if take_vcheck_attr(&mut a.attrs) {
                let target = build_forall_target(a, label)?;
                out.push(target);
                visit_expr(&mut a.expr, label, state, out)?;
                if let Some((_, q)) = &mut a.implies {
                    visit_expr(q, label, state, out)?;
                }
                visit_block(&mut a.body, label, state, out)?;
                return Ok(());
            }
        }
        _ => {}
    }
    // Default recursion: descend into children that can themselves
    // contain stmts.
    match expr {
        Expr::Block(b) => visit_block(&mut b.block, label, state, out)?,
        Expr::If(i) => {
            visit_expr(&mut i.cond, label, state, out)?;
            visit_block(&mut i.then_branch, label, state, out)?;
            if let Some((_, e)) = &mut i.else_branch {
                visit_expr(e, label, state, out)?;
            }
        }
        Expr::Match(m) => {
            visit_expr(&mut m.expr, label, state, out)?;
            for arm in m.arms.iter_mut() {
                if let Some((_, g)) = &mut arm.guard {
                    visit_expr(g, label, state, out)?;
                }
                visit_expr(&mut arm.body, label, state, out)?;
            }
        }
        Expr::Loop(l) => visit_block(&mut l.body, label, state, out)?,
        Expr::While(w) => {
            visit_expr(&mut w.cond, label, state, out)?;
            visit_block(&mut w.body, label, state, out)?;
        }
        Expr::ForLoop(f) => {
            visit_expr(&mut f.expr, label, state, out)?;
            visit_block(&mut f.body, label, state, out)?;
        }
        Expr::Unsafe(u) => visit_block(&mut u.block, label, state, out)?,
        Expr::Binary(b) => {
            visit_expr(&mut b.left, label, state, out)?;
            visit_expr(&mut b.right, label, state, out)?;
        }
        Expr::Unary(u) => visit_expr(&mut u.expr, label, state, out)?,
        Expr::Paren(p) => visit_expr(&mut p.expr, label, state, out)?,
        Expr::Reference(r) => visit_expr(&mut r.expr, label, state, out)?,
        Expr::Cast(c) => visit_expr(&mut c.expr, label, state, out)?,
        Expr::Tuple(t) => {
            for e in t.elems.iter_mut() {
                visit_expr(e, label, state, out)?;
            }
        }
        Expr::Array(a) => {
            for e in a.elems.iter_mut() {
                visit_expr(e, label, state, out)?;
            }
        }
        Expr::Call(c) => {
            visit_expr(&mut c.func, label, state, out)?;
            for a in c.args.iter_mut() {
                visit_expr(a, label, state, out)?;
            }
        }
        Expr::MethodCall(mc) => {
            visit_expr(&mut mc.receiver, label, state, out)?;
            for a in mc.args.iter_mut() {
                visit_expr(a, label, state, out)?;
            }
        }
        Expr::Index(i) => {
            visit_expr(&mut i.expr, label, state, out)?;
            visit_expr(&mut i.index, label, state, out)?;
        }
        Expr::Field(f) => visit_expr(&mut f.base, label, state, out)?,
        Expr::Assign(a) => {
            visit_expr(&mut a.left, label, state, out)?;
            visit_expr(&mut a.right, label, state, out)?;
        }
        Expr::Range(r) => {
            if let Some(s) = &mut r.start {
                visit_expr(s, label, state, out)?;
            }
            if let Some(e) = &mut r.end {
                visit_expr(e, label, state, out)?;
            }
        }
        Expr::Try(t) => visit_expr(&mut t.expr, label, state, out)?,
        Expr::Return(r) => {
            if let Some(e) = &mut r.expr {
                visit_expr(e, label, state, out)?;
            }
        }
        // Other shapes don't contain inline asserts in any vstd-shaped
        // body; conservative no-op default keeps the visitor small.
        _ => {}
    }
    Ok(())
}

/// Strip a `#[vcheck]` attribute from `attrs`, returning `true` if one
/// was present. Only removes the first match — duplicates would be a
/// user error and we let them surface naturally elsewhere.
fn take_vcheck_attr(attrs: &mut Vec<Attribute>) -> bool {
    if let Some(pos) = attrs.iter().position(attr_is_vcheck) {
        attrs.remove(pos);
        true
    } else {
        false
    }
}

fn build_path_target(
    a: &Assert,
    label: &str,
    assert_idx: u32,
    line: u32,
) -> Result<InlineAssertTarget, Error> {
    // Reject the by-prover and assert-by-block forms — neither makes
    // sense for property-based testing. They have a clear diagnostic
    // because the user almost certainly wants the plain form here.
    if a.prover.is_some() {
        return Err(Error::new_spanned(
            a.assert_token,
            "verus_spec_check: `#[vcheck] assert(P) by(...)` is not supported. Property-based \
             testing runs the predicate at runtime; the prover annotation only affects \
             SMT-time verification. Drop the `by(...)` clause to test the predicate.",
        ));
    }
    if a.body.is_some() {
        return Err(Error::new_spanned(
            a.assert_token,
            "verus_spec_check: `#[vcheck] assert(P) by { proof }` is not supported. The proof \
             body has no runtime meaning. Drop the `by { ... }` block to test the \
             predicate.",
        ));
    }
    let predicate = (*a.expr).clone();
    Ok(InlineAssertTarget {
        enclosing_fn_label: label.to_string(),
        line,
        assert_idx,
        kind: InlineAssertKind::Path { predicate },
    })
}

fn build_forall_target(a: &AssertForall, label: &str) -> Result<InlineAssertTarget, Error> {
    let line = a.assert_token.span.start().line as u32;
    let mut binders: Vec<(Ident, Type)> = Vec::new();
    for pat in a.inputs.iter() {
        let typed = match pat {
            Pat::Type(pt) => pt,
            other => {
                return Err(Error::new_spanned(
                    other,
                    "verus_spec_check: `#[vcheck] assert forall` binders must be typed (e.g. \
                     `|x: u32|`). Untyped binders can't be sampled because we don't \
                     know the strategy.",
                ));
            }
        };
        let ident = match &*typed.pat {
            Pat::Ident(pi) => pi.ident.clone(),
            other => {
                return Err(Error::new_spanned(
                    other,
                    "verus_spec_check: `#[vcheck] assert forall` binders must be simple `name: \
                     Type` patterns. Destructuring patterns aren't sampled.",
                ));
            }
        };
        binders.push((ident, (*typed.ty).clone()));
    }
    if binders.is_empty() {
        return Err(Error::new_spanned(
            a.assert_token,
            "verus_spec_check: `#[vcheck] assert forall` requires at least one typed binder.",
        ));
    }
    let predicate = (*a.expr).clone();
    let implies = a.implies.as_ref().map(|(_, q)| (**q).clone());
    Ok(InlineAssertTarget {
        enclosing_fn_label: label.to_string(),
        line,
        // Forall asserts use a (label, line)-keyed test name and don't
        // need the per-line ordinal. Always 0.
        assert_idx: 0,
        kind: InlineAssertKind::Forall {
            binders,
            predicate,
            implies,
        },
    })
}

/// Walk a `Block` and rewrite the path-form `Expr::Assert` at the
/// given source line and `marker_idx` (0-based ordinal among
/// `Expr::Assert`s on the same line) into the panicking-check form.
/// All OTHER `Expr::Assert` and `Expr::AssertForall` expressions in
/// the body are erased to a `()` no-op — they have no runtime meaning
/// in the cargo-test module where the checker fn lives, and leaving
/// them as `assert(...)` / `assert forall ...` would produce raw
/// Verus syntax that rustc rejects.
///
/// Returns `true` iff the targeted rewrite was applied.
///
/// Why line-based + ordinal instead of pure ordinal: by the time the
/// emit pass runs, the `Classified.passthrough_items` have already had
/// the `#[vcheck]` markers stripped from inline asserts. The
/// `ContractTarget` clones we emit checker fns from might still carry
/// the markers (depending on which clone path was used), but we don't
/// want to depend on that. Instead we identify the assert by its
/// source line — which is preserved through cloning and stripping —
/// and use `marker_idx` to disambiguate when multiple `#[vcheck]`-marked
/// asserts share a line.
///
/// Returns `true` if a rewrite was applied.
pub fn rewrite_path_assert_at_line(
    block: &mut Block,
    target_line: u32,
    marker_idx: u32,
    panic_message: &str,
) -> bool {
    let mut state = LineRewriteState {
        target_line,
        marker_idx,
        on_line_seen: 0,
        applied: false,
        message: panic_message.to_string(),
    };
    rewrite_block_for_line(block, &mut state);
    state.applied
}

struct LineRewriteState {
    target_line: u32,
    marker_idx: u32,
    on_line_seen: u32,
    applied: bool,
    message: String,
}

fn rewrite_block_for_line(block: &mut Block, st: &mut LineRewriteState) {
    // Walk every stmt. We don't bail after applying the targeted
    // rewrite — we keep walking to erase any non-target asserts in
    // the rest of the body.
    for stmt in block.stmts.iter_mut() {
        rewrite_stmt_for_line(stmt, st);
    }
}

fn rewrite_stmt_for_line(stmt: &mut Stmt, st: &mut LineRewriteState) {
    match stmt {
        Stmt::Local(local) => {
            if let Some(init) = &mut local.init {
                rewrite_expr_for_line(&mut init.expr, st);
            }
        }
        Stmt::Expr(e, _) => rewrite_expr_for_line(e, st),
        _ => {}
    }
}

fn rewrite_expr_for_line(expr: &mut Expr, st: &mut LineRewriteState) {
    // Note: we deliberately keep walking after `st.applied` becomes
    // true. The targeted assert is rewritten exactly once; everything
    // else is erased to a `()` no-op so the checker fn body is
    // valid raw Rust outside `verus!{}`.
    if let Expr::Assert(a) = expr {
        let assert_line = a.assert_token.span.start().line as u32;
        if !st.applied && assert_line == st.target_line {
            if st.on_line_seen == st.marker_idx {
                let predicate = (*a.expr).clone();
                let span = a.assert_token.span;
                let msg = st.message.clone();
                let new: Expr = verus_syn::parse_quote_spanned! { span =>
                    {
                        let __vcheck_check = #predicate;
                        if !__vcheck_check {
                            ::std::panic!(#msg);
                        }
                    }
                };
                *expr = new;
                st.applied = true;
                return;
            }
            st.on_line_seen += 1;
        }
        // Non-target asserts (other lines, or other ordinals on the
        // same line): erase to a `()` no-op so the checker fn body
        // doesn't carry raw `assert(...)` syntax outside `verus!{}`.
        let span = expr.span();
        *expr = verus_syn::parse_quote_spanned! { span => () };
        return;
    }
    if let Expr::AssertForall(_) = expr {
        // Forall-form asserts have a separate standalone harness; in
        // the checker fn body they're proof-only and erase to nothing.
        let span = expr.span();
        *expr = verus_syn::parse_quote_spanned! { span => () };
        return;
    }
    // Other Verus-only expression kinds the checker fn's host module
    // doesn't understand (it lives outside `verus!{...}`). All proof-
    // mode constructs erase to `()` since they have no runtime
    // meaning.
    if matches!(expr, Expr::Assume(_) | Expr::RevealHide(_)) {
        let span = expr.span();
        *expr = verus_syn::parse_quote_spanned! { span => () };
        return;
    }
    // `proof { ... }` blocks parse as `Expr::Unary(UnOp::Proof, ...)`.
    // Erase them too.
    if let Expr::Unary(u) = expr {
        if matches!(u.op, verus_syn::UnOp::Proof(_)) {
            let span = expr.span();
            *expr = verus_syn::parse_quote_spanned! { span => () };
            return;
        }
    }
    match expr {
        Expr::Block(b) => rewrite_block_for_line(&mut b.block, st),
        Expr::If(i) => {
            rewrite_expr_for_line(&mut i.cond, st);
            rewrite_block_for_line(&mut i.then_branch, st);
            if let Some((_, e)) = &mut i.else_branch {
                rewrite_expr_for_line(e, st);
            }
        }
        Expr::Match(m) => {
            rewrite_expr_for_line(&mut m.expr, st);
            for arm in m.arms.iter_mut() {
                if let Some((_, g)) = &mut arm.guard {
                    rewrite_expr_for_line(g, st);
                }
                rewrite_expr_for_line(&mut arm.body, st);
            }
        }
        Expr::Loop(l) => rewrite_block_for_line(&mut l.body, st),
        Expr::While(w) => {
            rewrite_expr_for_line(&mut w.cond, st);
            rewrite_block_for_line(&mut w.body, st);
        }
        Expr::ForLoop(f) => {
            rewrite_expr_for_line(&mut f.expr, st);
            rewrite_block_for_line(&mut f.body, st);
        }
        Expr::Unsafe(u) => rewrite_block_for_line(&mut u.block, st),
        Expr::Binary(b) => {
            rewrite_expr_for_line(&mut b.left, st);
            rewrite_expr_for_line(&mut b.right, st);
        }
        Expr::Unary(u) => rewrite_expr_for_line(&mut u.expr, st),
        Expr::Paren(p) => rewrite_expr_for_line(&mut p.expr, st),
        Expr::Reference(r) => rewrite_expr_for_line(&mut r.expr, st),
        Expr::Cast(c) => rewrite_expr_for_line(&mut c.expr, st),
        Expr::Tuple(t) => {
            for e in t.elems.iter_mut() {
                rewrite_expr_for_line(e, st);
            }
        }
        Expr::Array(a) => {
            for e in a.elems.iter_mut() {
                rewrite_expr_for_line(e, st);
            }
        }
        Expr::Call(c) => {
            rewrite_expr_for_line(&mut c.func, st);
            for a in c.args.iter_mut() {
                rewrite_expr_for_line(a, st);
            }
        }
        Expr::MethodCall(mc) => {
            rewrite_expr_for_line(&mut mc.receiver, st);
            for a in mc.args.iter_mut() {
                rewrite_expr_for_line(a, st);
            }
        }
        Expr::Index(i) => {
            rewrite_expr_for_line(&mut i.expr, st);
            rewrite_expr_for_line(&mut i.index, st);
        }
        Expr::Field(f) => rewrite_expr_for_line(&mut f.base, st),
        Expr::Assign(a) => {
            rewrite_expr_for_line(&mut a.left, st);
            rewrite_expr_for_line(&mut a.right, st);
        }
        Expr::Range(r) => {
            if let Some(s) = &mut r.start {
                rewrite_expr_for_line(s, st);
            }
            if let Some(e) = &mut r.end {
                rewrite_expr_for_line(e, st);
            }
        }
        Expr::Try(t) => rewrite_expr_for_line(&mut t.expr, st),
        Expr::Return(r) => {
            if let Some(e) = &mut r.expr {
                rewrite_expr_for_line(e, st);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Read-only inline-assert presence scan.
//
// Used by the whole-block preprocessor (`vcheck_attr::vcheck_provide_preprocess`)
// to detect fn bodies that carry stmt-level `#[vcheck] assert(...)` /
// `#[vcheck] assert forall ...` markers without an item-level `#[vcheck]` on
// the enclosing fn. Such fns must still be folded into the engine block
// or the inline-assert harness emitter never sees them and the test is
// silently dropped.
//
// This is a structural mirror of `visit_block` / `visit_expr` above, but:
//   - it takes `&Block` / `&Expr` (no mutation),
//   - it stops at the first match (return `true`),
//   - it ignores assert *contents* — only the presence of the `#[vcheck]`
//     attribute on `Expr::Assert` / `Expr::AssertForall` matters here.
//
// Keep this in lockstep with `visit_expr` when new expression kinds that
// can host inline asserts are added.
// ---------------------------------------------------------------------------

/// Return `true` if `block` contains at least one `#[vcheck]`-marked
/// `assert(...)` or `assert forall |...| ... by { }` statement,
/// transitively through nested blocks (loops, ifs, match arms,
/// unsafe blocks, etc.).
pub fn block_has_vcheck_inline_assert(block: &Block) -> bool {
    block.stmts.iter().any(stmt_has_vcheck_inline_assert)
}

fn stmt_has_vcheck_inline_assert(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Local(local) => local
            .init
            .as_ref()
            .map_or(false, |i| expr_has_vcheck_inline_assert(&i.expr)),
        Stmt::Expr(e, _) => expr_has_vcheck_inline_assert(e),
        Stmt::Item(_) | Stmt::Macro(_) => false,
    }
}

fn expr_has_vcheck_inline_assert(expr: &Expr) -> bool {
    match expr {
        Expr::Assert(a) => {
            if a.attrs.iter().any(attr_is_vcheck) {
                return true;
            }
            if expr_has_vcheck_inline_assert(&a.expr) {
                return true;
            }
            a.body
                .as_ref()
                .map_or(false, |b| block_has_vcheck_inline_assert(b))
        }
        Expr::AssertForall(a) => {
            if a.attrs.iter().any(attr_is_vcheck) {
                return true;
            }
            if expr_has_vcheck_inline_assert(&a.expr) {
                return true;
            }
            if let Some((_, q)) = &a.implies {
                if expr_has_vcheck_inline_assert(q) {
                    return true;
                }
            }
            block_has_vcheck_inline_assert(&a.body)
        }
        Expr::Block(b) => block_has_vcheck_inline_assert(&b.block),
        Expr::If(i) => {
            expr_has_vcheck_inline_assert(&i.cond)
                || block_has_vcheck_inline_assert(&i.then_branch)
                || i.else_branch
                    .as_ref()
                    .map_or(false, |(_, e)| expr_has_vcheck_inline_assert(e))
        }
        Expr::Match(m) => {
            if expr_has_vcheck_inline_assert(&m.expr) {
                return true;
            }
            m.arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .map_or(false, |(_, g)| expr_has_vcheck_inline_assert(g))
                    || expr_has_vcheck_inline_assert(&arm.body)
            })
        }
        Expr::Loop(l) => block_has_vcheck_inline_assert(&l.body),
        Expr::While(w) => {
            expr_has_vcheck_inline_assert(&w.cond) || block_has_vcheck_inline_assert(&w.body)
        }
        Expr::ForLoop(f) => {
            expr_has_vcheck_inline_assert(&f.expr) || block_has_vcheck_inline_assert(&f.body)
        }
        Expr::Unsafe(u) => block_has_vcheck_inline_assert(&u.block),
        Expr::Binary(b) => {
            expr_has_vcheck_inline_assert(&b.left) || expr_has_vcheck_inline_assert(&b.right)
        }
        Expr::Unary(u) => expr_has_vcheck_inline_assert(&u.expr),
        Expr::Paren(p) => expr_has_vcheck_inline_assert(&p.expr),
        Expr::Reference(r) => expr_has_vcheck_inline_assert(&r.expr),
        Expr::Cast(c) => expr_has_vcheck_inline_assert(&c.expr),
        Expr::Tuple(t) => t.elems.iter().any(expr_has_vcheck_inline_assert),
        Expr::Array(a) => a.elems.iter().any(expr_has_vcheck_inline_assert),
        Expr::Call(c) => {
            expr_has_vcheck_inline_assert(&c.func) || c.args.iter().any(expr_has_vcheck_inline_assert)
        }
        Expr::MethodCall(mc) => {
            expr_has_vcheck_inline_assert(&mc.receiver)
                || mc.args.iter().any(expr_has_vcheck_inline_assert)
        }
        Expr::Index(i) => {
            expr_has_vcheck_inline_assert(&i.expr) || expr_has_vcheck_inline_assert(&i.index)
        }
        Expr::Field(f) => expr_has_vcheck_inline_assert(&f.base),
        Expr::Assign(a) => {
            expr_has_vcheck_inline_assert(&a.left) || expr_has_vcheck_inline_assert(&a.right)
        }
        Expr::Range(r) => {
            r.start
                .as_ref()
                .map_or(false, |s| expr_has_vcheck_inline_assert(s))
                || r.end
                    .as_ref()
                    .map_or(false, |e| expr_has_vcheck_inline_assert(e))
        }
        Expr::Try(t) => expr_has_vcheck_inline_assert(&t.expr),
        Expr::Return(r) => r
            .expr
            .as_ref()
            .map_or(false, |e| expr_has_vcheck_inline_assert(e)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use verus_syn::ItemFn;

    fn parse_fn(src: &str) -> ItemFn {
        verus_syn::parse_str(src).expect("test fn must parse")
    }

    #[test]
    fn discovers_path_form_assert() {
        let mut f =
            parse_fn("fn caller(x: u32) -> u32 { let z = x + 1u32; #[vcheck] assert(z > x); z }");
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 1);
        assert!(matches!(targets[0].kind, InlineAssertKind::Path { .. }));
        assert_eq!(targets[0].assert_idx, 0);
    }

    #[test]
    fn discovers_forall_form_assert() {
        let mut f =
            parse_fn("fn caller() { #[vcheck] assert forall |w: u32| w + w == 2u32 * w by { }; }");
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 1);
        match &targets[0].kind {
            InlineAssertKind::Forall { binders, .. } => {
                assert_eq!(binders.len(), 1);
                assert_eq!(binders[0].0.to_string(), "w");
            }
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn discovers_forall_implies_form() {
        let mut f = parse_fn(
            "fn caller() { #[vcheck] assert forall |w: u32| w < 100u32 implies w + 1u32 > 0u32 by { }; }",
        );
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 1);
        match &targets[0].kind {
            InlineAssertKind::Forall { implies, .. } => {
                assert!(implies.is_some(), "expected implies clause");
            }
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn strips_vcheck_attribute_from_assert() {
        let mut f = parse_fn("fn caller(x: u32) { let z = x + 1u32; #[vcheck] assert(z > x); }");
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        // The cloned body should no longer carry the #[vcheck] attr.
        for stmt in &f.block.stmts {
            if let Stmt::Expr(Expr::Assert(a), _) = stmt {
                assert!(
                    a.attrs.iter().all(|attr| !attr_is_vcheck(attr)),
                    "vcheck attr should have been stripped"
                );
            }
        }
    }

    #[test]
    fn rejects_untyped_forall_binder() {
        let mut f = parse_fn("fn caller() { #[vcheck] assert forall |w| w + w == 2u32 * w by { }; }");
        let mut targets = Vec::new();
        let err = discover_in_block(&mut f.block, "caller", &mut targets);
        assert!(err.is_err());
        assert!(err.unwrap_err().to_string().contains("typed"));
    }

    #[test]
    fn rejects_assert_by_prover() {
        let mut f = parse_fn("fn caller(x: u32) { #[vcheck] assert(x > 0u32) by(bit_vector); }");
        let mut targets = Vec::new();
        let err = discover_in_block(&mut f.block, "caller", &mut targets);
        assert!(err.is_err());
        assert!(err.unwrap_err().to_string().contains("by(...)"));
    }

    #[test]
    fn discovers_multiple_asserts_in_order() {
        let mut f =
            parse_fn("fn caller(x: u32) { #[vcheck] assert(x > 0u32); #[vcheck] assert(x < 100u32); }");
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 2);
        assert_eq!(targets[0].assert_idx, 0);
        assert_eq!(targets[1].assert_idx, 1);
    }

    #[test]
    fn discovers_assert_inside_if() {
        let mut f = parse_fn("fn caller(x: u32) { if x > 0u32 { #[vcheck] assert(x >= 1u32); } }");
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 1);
    }

    #[test]
    fn parses_path_then_forall_back_to_back() {
        // Reproduces the multi-assert scenario: `#[vcheck] assert(...);` then
        // `assert forall ... by { };` on the next line. This tests that
        // verus_syn can parse the combination without the verus_spec_check
        // macro running. If this passes but the real macro emit fails,
        // the issue is downstream of verus_syn.
        let src = r#"fn caller(x: u32) -> u32 {
                let r = x + x;
                #[vcheck] assert(r >= x);
                assert forall |w: u32| w + w == 2u32 * w by { };
                r
            }"#;
        let f: ItemFn = verus_syn::parse_str(src)
            .expect("verus_syn must accept #[vcheck] path-form followed by assert forall");
        // Sanity: round-trip the body and confirm both asserts are still there.
        let txt = quote::quote!(#f).to_string();
        assert!(txt.contains("assert"), "{}", txt);
        assert!(txt.contains("forall"), "{}", txt);
    }

    #[test]
    fn discovery_strip_then_reparse_round_trip() {
        // Mirror what the production macro does: parse the body,
        // run discovery (which strips `#[vcheck]`), re-emit via quote!,
        // then re-parse. The re-parsed AST must still parse cleanly
        // — if it doesn't, the strip is leaving a malformed token
        // stream behind. This is the scenario the demo crate hits.
        let mut f: ItemFn = verus_syn::parse_str(
            r#"fn caller(x: u32) -> u32 {
                let r = x + x;
                #[vcheck] assert(r >= x);
                assert forall |w: u32| w + w == 2u32 * w by { };
                r
            }"#,
        )
        .unwrap();
        let mut targets = Vec::new();
        discover_in_block(&mut f.block, "caller", &mut targets).unwrap();
        assert_eq!(targets.len(), 1, "should discover the path-form #[vcheck]");

        // Re-emit and re-parse — this is what production does in the
        // `passthrough_block` of `expand`.
        let txt = quote::quote!(#f).to_string();
        let _re_parsed: ItemFn = verus_syn::parse_str(&txt).unwrap_or_else(|e| {
            panic!(
                "post-strip re-parse failed — discovery is leaving a malformed \
                 token stream behind:\n  error: {}\n  source: {}",
                e, txt
            );
        });
    }

    #[test]
    fn rewrite_path_assert_replaces_with_panic() {
        // Note: the rewriter expects the #[vcheck] attr to already be
        // stripped (rewrite is a separate pass after discovery).
        let mut f = parse_fn("fn caller(x: u32) { let z = x + 1u32; assert(z > x); }");
        // Find the line of the assert
        let assert_line = f
            .block
            .stmts
            .iter()
            .find_map(|s| {
                if let Stmt::Expr(Expr::Assert(a), _) = s {
                    Some(a.assert_token.span.start().line as u32)
                } else {
                    None
                }
            })
            .expect("expected assert in fn body");
        let applied =
            rewrite_path_assert_at_line(&mut f.block, assert_line, 0, "verus_spec_check: failed");
        assert!(applied);
        let txt = quote::quote!(#f).to_string();
        assert!(
            txt.contains("__vcheck_check"),
            "expected check binding: {}",
            txt
        );
        assert!(txt.contains("panic"), "expected panic call: {}", txt);
        assert!(
            !txt.contains("assert (z > x)") && !txt.contains("assert(z > x)"),
            "original assert should be gone: {}",
            txt
        );
    }

    #[test]
    fn rewrite_only_targets_indexed_assert() {
        // Two asserts on different lines. Rewriting line 1, ordinal 0,
        // should hit the first assert; line 2, ordinal 0 should hit
        // the second.
        let src = "fn caller(x: u32) {\n    assert(x > 0u32);\n    assert(x < 100u32);\n}";
        let mut f = parse_fn(src);
        let lines: Vec<u32> = f
            .block
            .stmts
            .iter()
            .filter_map(|s| {
                if let Stmt::Expr(Expr::Assert(a), _) = s {
                    Some(a.assert_token.span.start().line as u32)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(lines.len(), 2, "expected two asserts");
        let applied =
            rewrite_path_assert_at_line(&mut f.block, lines[1], 0, "second assert failed");
        assert!(applied);
        let txt = quote::quote!(#f).to_string();
        // The targeted (second) assert becomes a panicking check; the
        // first assert is erased to `()` since it's not the target
        // and Verus syntax (`assert(...)`) is invalid in raw Rust.
        let occurs = txt.matches("__vcheck_check").count();
        assert_eq!(
            occurs, 2,
            "expected exactly one rewrite (2 ident uses): {}",
            txt
        );
        // The non-target assert is erased to `()`.
        assert!(
            !txt.contains("assert (x > 0u32)") && !txt.contains("assert(x > 0u32)"),
            "non-target assert should be erased: {}",
            txt
        );
        assert!(
            !txt.contains("assert (x < 100u32)") && !txt.contains("assert(x < 100u32)"),
            "target assert should be rewritten: {}",
            txt
        );
        // The targeted panicking check should be present with the
        // configured message.
        assert!(
            txt.contains("second assert failed"),
            "expected panic message: {}",
            txt
        );
    }
}
