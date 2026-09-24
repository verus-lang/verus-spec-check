//! Additional useful checks for emitted blocks.

use super::*;

/// Extract the body call expression of a synthesized wrapper
/// (`__vcheck_assume_*`). For a Verus `assume_specification` like
/// `assume_specification[<u8>::wrapping_add](x, y) returns ...`, the
/// wrapper synthesized in `synthesize_vcheck_wrapper_from_assume_spec`
/// has a single-statement body `<u8>::wrapping_add(x, y)` (with maybe
/// a `.clone()` / `.cloned()` tail for adapted returns). We extract
/// that call's tokens so the audit can spot the case where the
/// rewritten ensures' RHS reduces to the same call.
pub fn extract_wrapper_body_call(target: &ContractTarget) -> Option<TokenStream2> {
    let block = match target {
        ContractTarget::FreeFn { item_fn, .. } => &item_fn.block,
        ContractTarget::Method { method, .. } => &method.block,
    };
    // The wrapper body is either a single expression statement
    // (`<T>::method(args)`) or a single block whose tail is that call.
    // Strip surface boilerplate to find the underlying call.
    let stmts = &block.stmts;
    if stmts.len() != 1 {
        return None;
    }
    let expr = match &stmts[0] {
        verus_syn::Stmt::Expr(e, _) => e,
        _ => return None,
    };
    // For `assume_specification` items the wrapper body is exactly the
    // call we want; for assertion-bearing user fns it would be the
    // user's body (which is unrelated to the ensures clause and won't
    // produce a tautology accidentally).
    let mut cur = expr;
    while let Expr::Paren(p) = cur {
        cur = p.expr.as_ref();
    }
    // Tolerate a trailing `.clone()` / `.cloned()` / `.map(...)` —
    // those are added by the wrapper synthesizer to materialize owned
    // returns. The underlying call still drives the tautology.
    while let Expr::MethodCall(mc) = cur {
        cur = mc.receiver.as_ref();
        while let Expr::Paren(p) = cur {
            cur = p.expr.as_ref();
        }
    }
    if matches!(cur, Expr::Call(_)) {
        Some(quote! { #cur })
    } else {
        None
    }
}

/// Check a single rewritten ensures clause for some known silent-no-op
/// patterns. See the call site in `emit_harness_with_flavor` for the
/// rationale
pub fn audit_rewritten_ensures(
    src_expr: &Expr,
    rewritten: &TokenStream2,
    wrapper_body_call: Option<&TokenStream2>,
) -> Result<(), Error> {
    // A1: empty / literal-bool. Use the token string for a robust
    // check that doesn't depend on parsing every emitted shape.
    let s = rewritten.to_string();
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(Error::new_spanned(
            src_expr,
            "verus_spec_check: this ensures clause lowered to an empty assertion. \
             The harness would compile and run, but no runtime check would fire. \
             This is the fingerprint of a silent-no-op bug in the engine; \
             please report it (with the source of the surrounding contract).",
        ));
    }
    if trimmed == "true" || trimmed == "false" {
        return Err(Error::new_spanned(
            src_expr,
            format!(
                "verus_spec_check: this ensures clause lowered to the bare boolean \
                 literal `{trimmed}`. The harness would always {} regardless of \
                 the sampled inputs, so the runtime check is vacuous. If the \
                 contract was meant to be unconditional, write it differently \
                 (e.g. by referencing the return value); otherwise this is \
                 a silent-no-op bug in the engine.",
                if trimmed == "true" { "pass" } else { "fail" }
            ),
        ));
    }

    // A3: tautological equality. Parse the rewritten tokens back to an
    // Expr and inspect the top-level shape. If parsing fails (because
    // the rewriter emitted something exotic), fall through — the
    // string-level checks above already handle the most common
    // silent-no-op shapes.
    if let Ok(parsed) = verus_syn::parse2::<Expr>(rewritten.clone()) {
        if let Some((lhs, rhs, op)) = top_level_eq_or_ne(&parsed) {
            let l_tokens = normalize_for_tautology_check(lhs);
            let r_tokens = normalize_for_tautology_check(rhs);
            let l = l_tokens.to_string();
            let r = r_tokens.to_string();
            // A3a: direct tautology, identical sides.
            if l == r {
                return Err(Error::new_spanned(
                    src_expr,
                    format!(
                        "verus_spec_check: this ensures clause lowered to a tautological \
                         `{op}` whose left and right sides are syntactically \
                         identical (`{l}`). The runtime check would {} for every \
                         sampled input, so the test isn't actually checking the \
                         spec against the implementation. This usually means a \
                         spec call (e.g. `u8_specs::wrapping_add(x, y)`) was \
                         lowered to the same intrinsic that the wrapper body \
                         calls. Inline the spec body directly instead.",
                        if op == "==" {
                            "always pass"
                        } else {
                            "always fail"
                        }
                    ),
                ));
            }
            // A3b: `__vcheck_ret == <wrapper_body_call>` shape. The wrapper
            // body's return value IS what `__vcheck_ret` is bound to, so
            // the comparison is vacuously true.
            if let Some(body_call) = wrapper_body_call {
                let body_s = body_call.to_string();
                let is_vcheck_ret = l == "__vcheck_ret" || r == "__vcheck_ret";
                let other = if l == "__vcheck_ret" { &r } else { &l };
                if is_vcheck_ret && other == &body_s {
                    return Err(Error::new_spanned(
                        src_expr,
                        format!(
                            "verus_spec_check: this ensures clause lowered to \
                             `__vcheck_ret {op} {other}`, where the right-hand \
                             side is syntactically identical to the body of \
                             the synthesized wrapper that produces \
                             `__vcheck_ret`. The runtime check would {} for \
                             every sampled input. This is the wrapper-tautology \
                             shape that hid the `wrapping_<add|sub|mul>` \
                             family of VCHECKs for a long time. Inline the \
                             spec body in the engine rather \
                             than redirecting to the same intrinsic the \
                             wrapper calls.",
                            if op == "==" {
                                "always pass"
                            } else {
                                "always fail"
                            }
                        ),
                    ));
                }
            }
        }
    }

    Ok(())
}

/// If `e` is a top-level `==` or `!=`, return `(lhs, rhs, "=="|"!=")`.
/// Looks through one layer of `Expr::Paren` on the outer.
pub fn top_level_eq_or_ne(e: &Expr) -> Option<(&Expr, &Expr, &'static str)> {
    let mut cur = e;
    while let Expr::Paren(p) = cur {
        cur = p.expr.as_ref();
    }
    if let Expr::Binary(b) = cur {
        let op = match &b.op {
            verus_syn::BinOp::Eq(_) => "==",
            verus_syn::BinOp::Ne(_) => "!=",
            _ => return None,
        };
        return Some((b.left.as_ref(), b.right.as_ref(), op));
    }
    None
}

/// Strip the cosmetic differences that shouldn't matter for the
/// tautology check: outer `Expr::Paren`s. We compare via `to_string()`
/// on the stripped form, which canonicalizes whitespace too.
pub fn normalize_for_tautology_check(e: &Expr) -> TokenStream2 {
    let mut cur = e;
    while let Expr::Paren(p) = cur {
        cur = p.expr.as_ref();
    }
    quote! { #cur }
}
