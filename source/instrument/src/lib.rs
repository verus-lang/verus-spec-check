//! Branch-site enumeration + source-level instrumentation for
//! `#[vcheck_cov_fuzz]`.
//!
//! Given a `verus_syn::Block` (the body of a contract-bearing exec fn),
//! [`instrument_branches`] returns one [`BranchSite`] per branch *arm* we
//! can plausibly observe, plus a full clone of the body with a marker call
//! (`<marker>(<site index>);`) injected at the entry of each arm. The
//! cov_fuzz emitter pairs the instrumented clone with a per-fn hit-bit
//! array; the coverage-guided runner then drives generated inputs through
//! the clone and the report reads back which arms were reached.
//!
//! ## What counts as a branch arm
//!
//! Every site kind implemented today is listed here, with what it
//! observes and what it deliberately doesn't. New kinds should be added
//! with the same level of documentation.
//!
//! ### if / if-let
//! Two arms per `if`: the then-branch and the else-branch. An `if`
//! without an `else` gets a synthesized `else { <mark>; }` so the
//! condition-false path is observable. `else if` chains need no special
//! handling — the nested `if` is instrumented by recursion, so each
//! `else if` arm is exactly the nested if's then-arm.
//!
//! ### match
//! One arm per match arm, marked at arm-body entry. A guarded arm
//! (`pat if g =>`) is marked when *taken*; the guard-false fall-through
//! is not a separate site (the subsequently-taken arm's mark covers it).
//!
//! ### `&&` / `||` short-circuit
//! One arm per binary lazy operator: the right operand's evaluation
//! (`a && { <mark>; b }`). Reached iff the left operand did not
//! short-circuit. This is also the mechanism that gives the
//! coverage-guided search per-conjunct progress signal through
//! compound conditions.
//!
//! ### while / for
//! One arm per loop: body entry (i.e. "the loop iterated at least
//! once"). The zero-iteration path is NOT a separate site — observing
//! it would require restructuring the loop, and the exit path is
//! usually implied by the surrounding straight-line code.
//!
//! ## What we deliberately don't instrument
//!
//! - **`loop { ... }`**: the body is unconditionally entered, so a mark
//!   would be an always-hit site that only inflates the denominator.
//! - **`?` operator**: marking the error path requires expanding the
//!   `?` into a match, which changes inference around `From::from`;
//!   high build-failure risk for low signal. 
//! - **`let ... else`**: same restructuring concern as `?`.
//! - **Guard-false fall-throughs** in `match`: see above.
//!
//! Sites are capped per-fn (see the emitter's cap) to bound compile
//! time; the walker stops allocating new sites once the cap is hit and
//! reports that it did.

use quote::quote;
use verus_syn::spanned::Spanned;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{BinOp, Block, Expr, Ident, Stmt};

/// One observable branch arm. `idx` is the 0-based slot in the per-fn
/// hit-bit array (`__VCHECK_COVF_HITS_<fn>[idx]`); `line`/`description`
/// feed the coverage report's "unreached" listing.
#[derive(Clone, Debug)]
pub struct BranchSite {
    /// 0-based hit-array slot, matching the marker call's argument.
    pub idx: u32,
    /// Source line of the branch construct in the original body.
    pub line: u32,
    /// Short human-readable arm description (e.g. `"if (then branch)"`,
    /// ``"match arm `Kind::Extended`"``).
    pub description: String,
}

/// Walk `body`, enumerate branch arms, and return `(sites, instrumented
/// clone, hit_cap)`. The clone is identical to `body` except that each
/// enumerated arm's entry gains a `<marker>(<idx>);` statement (and
/// `if`s without an `else` gain a synthesized marking `else`). When the
/// cap is reached the walker stops allocating *new* sites (the body is
/// then only partially instrumented) and `hit_cap` is `true`; the
/// report's denominator stays consistent because it is `sites.len()`.
pub fn instrument_branches(
    body: &Block,
    marker: &Ident,
    cap: usize,
) -> (Vec<BranchSite>, Block, /* hit_cap: */ bool) {
    let mut instrumented = body.clone();
    let mut v = Instrumenter {
        marker,
        sites: Vec::new(),
        cap,
        hit_cap: false,
    };
    v.visit_block_mut(&mut instrumented);
    (v.sites, instrumented, v.hit_cap)
}

struct Instrumenter<'a> {
    marker: &'a Ident,
    sites: Vec<BranchSite>,
    cap: usize,
    hit_cap: bool,
}

impl Instrumenter<'_> {
    /// Allocate the next site slot, or `None` once the cap is hit.
    fn alloc(&mut self, line: u32, description: String) -> Option<usize> {
        if self.sites.len() >= self.cap {
            self.hit_cap = true;
            return None;
        }
        let idx = self.sites.len();
        self.sites.push(BranchSite {
            idx: idx as u32,
            line,
            description,
        });
        Some(idx)
    }

    /// `\<marker>(<idx>);` as a statement, for splicing at arm entry.
    fn mark_stmt(&self, idx: usize) -> Stmt {
        let marker = self.marker;
        verus_syn::parse_quote! { #marker(#idx); }
    }

    /// `{ <marker>(<idx>); <expr> }` — wrap an arm-body expression so
    /// the mark runs first. Used for match arms and `&&`/`||` right
    /// operands, whose bodies are expressions rather than blocks.
    fn mark_wrapped(&self, idx: usize, expr: &Expr) -> Expr {
        let marker = self.marker;
        verus_syn::parse_quote! {{ #marker(#idx); #expr }}
    }
}

/// Best-effort source line of a spanned node.
fn line_of<T: Spanned>(node: &T) -> u32 {
    node.span().start().line as u32
}

/// Render a match pattern for the report, truncated so a large struct
/// pattern doesn't blow up the line.
fn render_pat(pat: &verus_syn::Pat) -> String {
    let mut s = quote!(#pat).to_string();
    if s.len() > 40 {
        s.truncate(37);
        s.push_str("...");
    }
    s
}

impl VisitMut for Instrumenter<'_> {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        match e {
            Expr::If(ei) => {
                let line = line_of(&ei.cond);
                let is_let = matches!(ei.cond.as_ref(), Expr::Let(_));
                let (then_desc, else_desc) = if is_let {
                    ("if let (pattern matched)", "if let (pattern not matched)")
                } else {
                    ("if (then branch)", "if (else branch)")
                };
                if let Some(idx) = self.alloc(line, then_desc.to_string()) {
                    ei.then_branch.stmts.insert(0, self.mark_stmt(idx));
                }
                match &mut ei.else_branch {
                    Some((_, else_expr)) => match else_expr.as_mut() {
                        Expr::Block(b) => {
                            if let Some(idx) = self.alloc(line, else_desc.to_string()) {
                                b.block.stmts.insert(0, self.mark_stmt(idx));
                            }
                        }
                        // `else if`: the nested `if` gets its own arms
                        // via recursion below; no extra site here.
                        Expr::If(_) => {}
                        // Unusual else shapes (macro output, etc.):
                        // leave unobserved rather than risk a rewrite.
                        _ => {}
                    },
                    None => {
                        let implicit = if is_let {
                            "if let (pattern not matched, implicit else)"
                        } else {
                            "if (implicit else: condition false)"
                        };
                        if let Some(idx) = self.alloc(line, implicit.to_string()) {
                            let marker = self.marker;
                            let else_block: Expr = verus_syn::parse_quote! {{ #marker(#idx); }};
                            ei.else_branch = Some((Default::default(), Box::new(else_block)));
                        }
                    }
                }
            }
            Expr::Match(em) => {
                for arm in em.arms.iter_mut() {
                    let line = line_of(&arm.pat);
                    let mut desc = format!("match arm `{}`", render_pat(&arm.pat));
                    if arm.guard.is_some() {
                        desc.push_str(" (guard passed)");
                    }
                    if let Some(idx) = self.alloc(line, desc) {
                        let wrapped = self.mark_wrapped(idx, &arm.body);
                        *arm.body = wrapped;
                    }
                }
            }
            Expr::Binary(be)
                if matches!(be.op, BinOp::And(_) | BinOp::Or(_))
                    // Let-chains: `a && let Some(x) = b` — a let-expr is
                    // only legal directly in the condition chain, so
                    // wrapping it in a block would not compile. Leave
                    // that arm unobserved (and un-counted).
                    && !matches!(be.right.as_ref(), Expr::Let(_)) =>
            {
                let line = line_of(&be.op);
                let desc = match be.op {
                    BinOp::And(_) => "`&&` right operand evaluated (left was true)",
                    BinOp::Or(_) => "`||` right operand evaluated (left was false)",
                    _ => unreachable!(),
                };
                if let Some(idx) = self.alloc(line, desc.to_string()) {
                    let wrapped = self.mark_wrapped(idx, &be.right);
                    *be.right = wrapped;
                }
            }
            Expr::While(ew) => {
                // Strip Verus loop-spec clauses (ghost: no runtime
                // effect) so the instrumented twin is valid plain Rust.
                ew.invariant = None;
                ew.invariant_except_break = None;
                ew.invariant_ensures = None;
                ew.ensures = None;
                ew.decreases = None;
                let line = line_of(&ew.cond);
                if let Some(idx) =
                    self.alloc(line, "while body entered (>= 1 iteration)".to_string())
                {
                    ew.body.stmts.insert(0, self.mark_stmt(idx));
                }
            }
            Expr::ForLoop(ef) => {
                ef.invariant = None;
                ef.invariant_except_break = None;
                ef.ensures = None;
                ef.decreases = None;
                let line = line_of(&ef.pat);
                if let Some(idx) = self.alloc(line, "for body entered (>= 1 iteration)".to_string())
                {
                    ef.body.stmts.insert(0, self.mark_stmt(idx));
                }
            }
            Expr::Loop(el) => {
                // Not a site (the body is unconditionally entered), but
                // the ghost clauses still need stripping for the twin.
                el.invariant = None;
                el.invariant_except_break = None;
                el.invariant_ensures = None;
                el.ensures = None;
                el.decreases = None;
            }
            _ => {}
        }
        // Recurse AFTER the structural rewrite so nested branches inside
        // the (possibly wrapped) children are enumerated too. The
        // injected mark statements are plain calls and match no case
        // above, so they are never re-instrumented.
        verus_syn::visit_mut::visit_expr_mut(self, e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;

    fn instr(src: &str) -> (Vec<BranchSite>, String) {
        let block: Block = verus_syn::parse_str(&format!("{{ {} }}", src)).expect("parse");
        let marker = format_ident!("__vcheck_covmark_t");
        let (sites, out, hit_cap) = instrument_branches(&block, &marker, 128);
        assert!(!hit_cap);
        (sites, quote!(#out).to_string())
    }

    #[test]
    fn if_with_else_two_arms() {
        let (sites, out) = instr("if x > 0 { 1 } else { 2 }");
        assert_eq!(sites.len(), 2);
        assert!(out.contains("__vcheck_covmark_t (0usize)"));
        assert!(out.contains("__vcheck_covmark_t (1usize)"));
    }

    #[test]
    fn if_without_else_synthesizes_else() {
        let (sites, out) = instr("if x > 0 { y += 1; }");
        assert_eq!(sites.len(), 2);
        assert!(sites[1].description.contains("implicit else"));
        assert!(out.contains("else"));
    }

    #[test]
    fn else_if_chain_counts_each_arm_once() {
        // if/else-if/else: then + (nested then + nested else) = 3 arms,
        // NOT 4 (no separate site for the `else if` wrapper).
        let (sites, _) = instr("if a { 1 } else if b { 2 } else { 3 }");
        assert_eq!(sites.len(), 3);
    }

    #[test]
    fn match_arms() {
        let (sites, _) = instr("match x { 0 => a, 1 if y => b, _ => c }");
        assert_eq!(sites.len(), 3);
        assert!(sites[1].description.contains("guard passed"));
    }

    #[test]
    fn short_circuit_ops() {
        let (sites, out) = instr("let v = a && b || c;");
        // (a && b) || c: one site per lazy op's rhs.
        assert_eq!(sites.len(), 2);
        assert!(out.contains("__vcheck_covmark_t"));
    }

    #[test]
    fn loops_mark_body_entry() {
        let (sites, _) = instr("while i < n { i += 1; } for x in 0..k { s += x; }");
        assert_eq!(sites.len(), 2);
    }

    #[test]
    fn straight_line_body_has_no_sites() {
        let (sites, _) = instr("let y = x + 1; y * 2");
        assert!(sites.is_empty());
    }

    #[test]
    fn cap_stops_allocation() {
        let block: Block =
            verus_syn::parse_str("{ if a { 1 } else { 2 }; if b { 3 } else { 4 }; }")
                .expect("parse");
        let marker = format_ident!("m");
        let (sites, _, hit_cap) = instrument_branches(&block, &marker, 3);
        assert_eq!(sites.len(), 3);
        assert!(hit_cap);
    }

    #[test]
    fn nested_branches_inside_wrapped_arms_are_found() {
        let (sites, _) = instr("match x { 0 => if y { 1 } else { 2 }, _ => 3 }");
        // 2 match arms + 2 if arms.
        assert_eq!(sites.len(), 4);
    }

    /// Let-chains: the `&&`-rhs of `a && let Some(x) = b` must NOT be
    /// block-wrapped (a let-expr is only legal in the condition chain
    /// itself; the wrap would not compile). Only the if's two arms are
    /// counted. Skipped when the pinned verus_syn can't parse
    /// let-chains at all — then the hazard can't arise.
    #[test]
    fn let_chain_rhs_is_not_wrapped() {
        let parsed: Result<Block, _> =
            verus_syn::parse_str("{ if a && let Some(x) = b { 1 } else { 2 } }");
        let Ok(block) = parsed else { return };
        let marker = format_ident!("m");
        let (sites, out, _) = instrument_branches(&block, &marker, 16);
        let text = quote!(#out).to_string();
        assert_eq!(sites.len(), 2, "only the if arms: {text}");
        // The let-expr must remain DIRECTLY after `&&` (not wrapped in
        // a marking block, which would be illegal outside the chain).
        assert!(
            text.contains("&& let Some"),
            "let-expr must not be block-wrapped: {text}"
        );
    }
}

#[cfg(test)]
mod verus_loop_tests {
    use super::*;
    use quote::{format_ident, quote};

    /// Verus loop-spec clauses (invariant/decreases) must be stripped
    /// from the instrumented clone — the twin is emitted as plain Rust.
    #[test]
    fn while_invariant_and_decreases_are_stripped() {
        let block: Block = verus_syn::parse_str(
            "{ let mut i: u8 = 0; while i < n invariant i <= n, decreases n - i, { i = i + 1; } i }",
        )
        .expect("parse verus while");
        let marker = format_ident!("m");
        let (sites, out, _) = instrument_branches(&block, &marker, 16);
        assert_eq!(sites.len(), 1);
        let text = quote!(#out).to_string();
        assert!(!text.contains("invariant"), "invariant survived: {text}");
        assert!(!text.contains("decreases"), "decreases survived: {text}");
        assert!(text.contains("m (0usize)"));
    }
}
