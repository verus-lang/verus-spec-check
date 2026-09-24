use super::*;

// ---------------------------------------------------------------------------
// `#[vcheck_cov_mutate]` emission
// ---------------------------------------------------------------------------

/// Build the inline-assert test-module contents for a `Classified`
/// with non-empty `inline_assert_targets`. Returns an empty token
/// stream when no targets are present.
///
/// For each path-form target (`#[vcheck] assert(P)`):
///   - Emits a parallel "checker" fn `__vcheck_assert_<idx>_<encfn>` with
///     the targeted `assert(P)` rewritten to a panicking check.
///   - Emits a `#[test] fn __vcheck_assert_<encfn>_at_lineN(...)`
///     produced via `emit_harness_with_flavor` in
///     `HarnessFlavor::InlineAssertChecker` mode. The harness samples
///     the enclosing fn's parameters (with `prop_assume!` for
///     requires-clauses) and calls the checker fn. A panic from the
///     checker is the failure signal, caught and shrunk by proptest.
///
/// For each forall-form target (`#[vcheck] assert forall |...| ... by { }`):
///   - Emits a self-contained `#[test] fn __vcheck_assert_forall_<encfn>_at_lineN()`
///     that builds a proptest strategy from the binders' types and
///     evaluates the predicate (or `implies`-form antecedent -> consequent).
///
/// Path-form harnesses skip targets whose enclosing fn is not
/// `#[vcheck]`-able (e.g. has `Tracked` parameters); we surface a
/// diagnostic via `compile_error!`. Forall-form harnesses don't
/// depend on the enclosing fn's shape.
pub fn emit_inline_assert_block(classified: &Classified) -> Result<TokenStream2, Error> {
    if classified.inline_assert_targets.is_empty() {
        return Ok(quote! {});
    }

    let mut checker_fns: Vec<TokenStream2> = Vec::new();
    let mut harnesses: Vec<TokenStream2> = Vec::new();

    for ctx in &classified.inline_assert_targets {
        match &ctx.target.kind {
            crate::vcheck_assert::InlineAssertKind::Path { .. } => {
                // Path-form: needs the enclosing ContractTarget to
                // build the harness. If we couldn't find one, the
                // assert is in a fn that isn't `#[vcheck]`-able.
                let enclosing = match &ctx.enclosing {
                    Some(e) => e,
                    None => {
                        return Err(Error::new(
                            proc_macro2::Span::call_site(),
                            format!(
                                "verus_spec_check: `#[vcheck]` on inline assert at {}:{} \
                                 requires the enclosing fn `{}` to be `#[vcheck]`-able. \
                                 Add `#[vcheck]` to the fn (and ensure its params are \
                                 sample-able) so the harness can drive it.",
                                ctx.target.enclosing_fn_label,
                                ctx.target.line,
                                ctx.target.enclosing_fn_label,
                            ),
                        ));
                    }
                };

                // Build the checker fn: clone the enclosing fn's body,
                // rewrite the targeted assert to a panicking check.
                // The fn is emitted at module scope (free fn shape).
                let (checker_fn_ident, test_fn_ident, checker_ts) =
                    emit_inline_assert_checker_fn(enclosing, &ctx.target)?;
                checker_fns.push(checker_ts);

                // Build the harness via emit_harness_with_flavor with
                // the new InlineAssertChecker flavor.
                let mut counter = 0u64;
                let harness = emit_harness_with_flavor(
                    enclosing,
                    &classified.spec_fn_names,
                    &classified.user_type_names,
                    &classified.when_used_as_spec_redirect,
                    &mut counter,
                    HarnessFlavor::InlineAssertChecker {
                        checker_fn: checker_fn_ident,
                        test_name: test_fn_ident,
                        enclosing_is_method: matches!(enclosing, ContractTarget::Method { .. }),
                    },
                )?;
                harnesses.push(harness.harness_tokens);
            }
            crate::vcheck_assert::InlineAssertKind::Forall { .. } => {
                // Forall-form: standalone harness, no enclosing fn
                // dependency. Emit directly.
                let harness = emit_inline_assert_forall_harness(
                    &ctx.target,
                    &classified.spec_fn_names,
                    &classified.user_type_names,
                )?;
                harnesses.push(harness);
            }
        }
    }

    Ok(quote! {
        #(#checker_fns)*
        #(#harnesses)*
    })
}

/// Build the parallel "checker" fn for a path-form inline assert.
/// Returns `(checker_fn_ident, test_fn_ident, fn_tokens)`.
///
/// The checker fn is the enclosing fn's body with the targeted
/// `assert(P)` rewritten to a panicking check. Other asserts in the
/// body remain `assert(...)` and erase to no-ops at `cargo test` time.
pub fn emit_inline_assert_checker_fn(
    enclosing: &ContractTarget,
    target: &crate::vcheck_assert::InlineAssertTarget,
) -> Result<(Ident, Ident, TokenStream2), Error> {
    let line = target.line;
    let idx = target.assert_idx;
    let encfn_label = sanitize_label(&target.enclosing_fn_label);

    let checker_fn_ident: Ident = format_ident!("__vcheck_assert_{}_{}", idx, encfn_label);
    let test_fn_ident: Ident = format_ident!("__vcheck_assert_{}_at_line{}", encfn_label, line);

    let panic_msg = format!(
        "verus_spec_check: inline assert at {}:{} (#[vcheck] marker {}) failed",
        target.enclosing_fn_label, line, idx
    );

    let mut body = match enclosing {
        ContractTarget::FreeFn { item_fn, .. } => (*item_fn.block).clone(),
        ContractTarget::Method { method, .. } => method.block.clone(),
    };

    // Find the assert by source line and rewrite it. We use line-based
    // matching because the body has already had `#[vcheck]` stripped
    // before we got here (the discovery pass mutates passthrough_items),
    // so the cloned ContractTarget body may or may not still carry the
    // attribute depending on which clone-vs-original path was used.
    let applied = crate::vcheck_assert::rewrite_path_assert_at_line(&mut body, line, idx, &panic_msg);
    if !applied {
        return Err(Error::new(
            proc_macro2::Span::call_site(),
            format!(
                "verus_spec_check: internal: failed to rewrite inline assert at {}:{} \
                 (idx={}). Likely a discovery/rewrite ordering mismatch.",
                target.enclosing_fn_label, line, idx
            ),
        ));
    }

    let fn_ts = match enclosing {
        ContractTarget::FreeFn { item_fn, .. } => {
            emit_mutant_fn_freefn(item_fn, &checker_fn_ident, &body)
        }
        ContractTarget::Method {
            self_ty, method, ..
        } => emit_mutant_fn_method(self_ty, method, &checker_fn_ident, &body),
    };

    Ok((checker_fn_ident, test_fn_ident, fn_ts))
}

/// Sanitize a `Type::name` / `fn_name` label into a valid Rust ident
/// suffix. Replaces `::` with `_` so we get
/// `__vcheck_assert_Counter_step` rather than the invalid
/// `__vcheck_assert_Counter::step`.
pub fn sanitize_label(s: &str) -> String {
    s.replace("::", "_")
}

/// A self-contained `#[test]` for a forall-form `#[vcheck] assert
/// forall |x: T| P(x) [implies Q(x)] by { }`
///
/// The harness:
///   - Builds a proptest strategy tuple from the binders' declared
///     types via the existing `ParamShape` classification.
///   - Samples the binders, evaluates `P` (or `P` as antecedent and
///     `Q` as consequent for the implies form).
///   - Reports a counterexample on first failure.
pub fn emit_inline_assert_forall_harness(
    target: &crate::vcheck_assert::InlineAssertTarget,
    _spec_fn_names: &HashSet<String>,
    user_type_names: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let (binders, predicate, implies) = match &target.kind {
        crate::vcheck_assert::InlineAssertKind::Forall {
            binders,
            predicate,
            implies,
        } => (binders, predicate, implies),
        _ => unreachable!(),
    };

    let line = target.line;
    let encfn_label = sanitize_label(&target.enclosing_fn_label);
    let test_fn_ident: Ident = format_ident!("__vcheck_assert_forall_{}_at_line{}", encfn_label, line);

    // Build the strategy tuple from the binder types, using the same
    // shape-classification path as regular `#[vcheck]` parameters. We
    // reject any binder type whose `ParamShape` we can't sample.
    let mut strategy_exprs: Vec<TokenStream2> = Vec::new();
    let mut binder_idents: Vec<Ident> = Vec::new();
    let mut binder_types: Vec<TokenStream2> = Vec::new();
    for (ident, ty) in binders {
        let _shape = classify_param_type(ty, user_type_names).map_err(|e| {
            Error::new_spanned(
                ty,
                format!(
                    "verus_spec_check: `#[vcheck] assert forall` binder `{}: {}` has an \
                     unsupported type. {}",
                    ident,
                    quote::quote!(#ty),
                    e
                ),
            )
        })?;
        // Use the same simple `vcheck_strategy::<T>()` path used for
        // unconstrained ordinary params.
        strategy_exprs.push(quote! {
            ::verus_spec_check::vcheck_strategy::<#ty>()
        });
        binder_idents.push(ident.clone());
        binder_types.push(quote! { #ty });
    }

    let test_failure_msg = format!(
        "verus_spec_check: assert forall failed at {}:{}",
        target.enclosing_fn_label, line
    );

    let body = match implies {
        // implies form: predicate is the antecedent, implies is the consequent.
        Some(consequent) => quote! {
            // Antecedent false -> discard (don't count as failure).
            if !{ #predicate } {
                return Err(::verus_spec_check::proptest::test_runner::TestCaseError::reject(
                    "antecedent rejected"
                ));
            }
            if !{ #consequent } {
                return Err(::verus_spec_check::proptest::test_runner::TestCaseError::fail(
                    #test_failure_msg
                ));
            }
            Ok(())
        },
        // simple form: just check the predicate.
        None => quote! {
            if !{ #predicate } {
                return Err(::verus_spec_check::proptest::test_runner::TestCaseError::fail(
                    #test_failure_msg
                ));
            }
            Ok(())
        },
    };

    Ok(quote! {
        #[test]
        #[allow(non_snake_case, unused_variables, unused_mut, dead_code)]
        fn #test_fn_ident() {
            use ::verus_spec_check::proptest::strategy::Strategy;
            use ::verus_spec_check::proptest::test_runner::{Config, TestCaseError, TestRunner};
            let cfg = Config {
                max_global_rejects: 1_000_000,
                ..Config::default()
            };
            let mut runner = TestRunner::new(cfg);
            let strategy = ( #( (#strategy_exprs) ,)* );
            let result = runner.run(&strategy, |( #( #binder_idents , )* )| {
                #body
            });
            if let Err(e) = result {
                ::std::panic!("verus_spec_check: assert forall produced a counterexample: {:?}", e);
            }
        }
    })
}
