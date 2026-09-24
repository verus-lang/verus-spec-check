use super::*;

/// Build the cov_mutate test-module contents for a `Classified` with
/// non-empty `cov_mutate_targets`. Returns an empty token stream when
/// no targets are present. Emits, for each non-skipped target:
///
///  - One parallel `__vcheck_mutant_<k>_<orig>` fn per mutation site, with
///    the same signature as the original but a mutated body and no
///    contract attributes.
///  - One `__vcheck_mutant_run_<k>_<orig>` runner fn produced by
///    [`emit_harness_with_flavor`] in [`HarnessFlavor::MutantRunner`]
///    mode. The runner sets up an in-process proptest loop and returns
///    [`MutantOutcome`].
///  - One `VcheckCovMutant` const slice referencing the runners.
///  - The aggregating `VcheckCovMutateTarget` const slice.
///  - A `#[test] fn __vcheck_mutation_report()` that calls
///    `run_mutation_report` with the targets.
pub fn emit_cov_mutate_block(classified: &Classified) -> Result<TokenStream2, Error> {
    if classified.cov_mutate_targets.is_empty() {
        return Ok(quote! {});
    }

    /// Per-fn cap on mutation sites. Keeps compile time bounded.
    const PER_FN_MAX_MUTANTS: usize = 30;

    let mut mutant_fn_decls: Vec<TokenStream2> = Vec::new();
    let mut mutant_runner_decls: Vec<TokenStream2> = Vec::new();
    let mut target_decls: Vec<TokenStream2> = Vec::new();

    for target in &classified.cov_mutate_targets {
        // Skipped targets still appear in the report; we just emit no
        // mutants for them.
        if target.skip {
            target_decls.push(emit_target_decl(target, &[]));
            continue;
        }

        // Enumerate mutation sites on the body. We thread a
        // `MutatorContext` built from the original fn's signature so
        // the type-gated operators (ABS, UOI) can fire only on params
        // with the right declared type.
        let (body, sig) = match &target.body_source {
            CovMutateBodySource::FreeFn(item_fn) => (item_fn.block.as_ref().clone(), &item_fn.sig),
            CovMutateBodySource::Method { method, .. } => (method.block.clone(), &method.sig),
        };
        let mutator_ctx = crate::vcheck_mutator::MutatorContext::from_signature(sig);
        let (sites, _hit_cap) = crate::vcheck_mutator::enumerate_mutation_sites_with_context(
            &body,
            PER_FN_MAX_MUTANTS,
            &mutator_ctx,
        );

        let mut per_fn_mutant_consts: Vec<TokenStream2> = Vec::new();

        for site in &sites {
            // Names of the parallel fn and its runner.
            let fn_ident_str = &target.fn_ident;
            let mutant_fn_ident: Ident =
                format_ident!("__vcheck_mutant_{}_{}", site.idx, fn_ident_str);
            let runner_ident: Ident =
                format_ident!("__vcheck_mutant_run_{}_{}", site.idx, fn_ident_str);

            // Emit the parallel fn (same sig as original, mutated body,
            // contract attrs stripped).
            let mutant_fn_ts = match &target.body_source {
                CovMutateBodySource::FreeFn(item_fn) => {
                    emit_mutant_fn_freefn(item_fn, &mutant_fn_ident, &site.mutated_body)
                }
                CovMutateBodySource::Method { self_ty, method } => {
                    emit_mutant_fn_method(self_ty, method, &mutant_fn_ident, &site.mutated_body)
                }
            };
            mutant_fn_decls.push(mutant_fn_ts);

            // Emit the runner fn via `emit_harness_with_flavor`. The
            // contract target is the *original* fn (so the requires /
            // ensures are correct), but the call routes through the
            // mutant fn.
            let mutant_is_method =
                matches!(&target.body_source, CovMutateBodySource::Method { .. });
            let contract_target = match &target.body_source {
                CovMutateBodySource::FreeFn(item_fn) => {
                    ContractTarget::FreeFn {
                        item_fn: item_fn.clone(),
                        // cov_mutate runs its own runner test; the
                        // Miri-skip toggle is honored only on the
                        // primary harness emission path. Default
                        // here matches "no skip".
                        miri_skip: false,
                        // cov_mutate runs its own in-process runner
                        backend: crate::vcheck_attr::VcheckBackend::Proptest,
                        // Proptest backend ==> no bolero mode.
                        bolero_mode: None,
                        // cov_mutate uses this target only as the
                        // signature/body source for the runner; the
                        // skip-regular-harness flag is meaningless
                        // here, so default it.
                        skip_regular_harness: false,
                    }
                }
                CovMutateBodySource::Method { self_ty, method } => ContractTarget::Method {
                    self_ty: self_ty.clone(),
                    method: method.clone(),
                    miri_skip: false,
                    backend: crate::vcheck_attr::VcheckBackend::Proptest,
                    bolero_mode: None,
                    skip_regular_harness: false,
                },
            };
            let mut counter = 0u64;
            let runner = emit_harness_with_flavor(
                &contract_target,
                &classified.spec_fn_names,
                &classified.user_type_names,
                &classified.when_used_as_spec_redirect,
                &mut counter,
                HarnessFlavor::MutantRunner {
                    runner_name: runner_ident.clone(),
                    mutant_call_fn: mutant_fn_ident.clone(),
                    mutant_is_method,
                },
            )?;
            // Emit the synthetic spec fns alongside the runner. They go
            // into the harness module like the regular harness's synth
            // fns. (We collect them into a side bucket; the caller
            // appends them to the engine_items list.)
            for synth in runner.synthetic_spec_fns {
                mutant_runner_decls.push(synth);
            }
            mutant_runner_decls.push(runner.harness_tokens);

            // Build the VcheckCovMutant entry referring to this runner.
            let line_num = site.line as u64;
            let desc_str = site.description.clone();
            let idx_num = site.idx;
            let mutant_const = quote! {
                ::verus_spec_check::cov_mutate::VcheckCovMutant {
                    idx: #idx_num as u32,
                    line: #line_num as u32,
                    description: #desc_str,
                    run: #runner_ident,
                }
            };
            per_fn_mutant_consts.push(mutant_const);
        }

        target_decls.push(emit_target_decl(target, &per_fn_mutant_consts));
    }

    let n = target_decls.len();
    Ok(quote! {
        // Mutant fns (one per mutation site).
        #(#mutant_fn_decls)*

        // Per-mutant runner fns (one per mutation site).
        #(#mutant_runner_decls)*

        // Per-fn target metadata. Each target carries a slice of
        // mutants pointing at the runner fns.
        const __VCHECK_COV_MUTATE_TARGETS:
            [::verus_spec_check::cov_mutate::VcheckCovMutateTarget; #n] = [
            #(#target_decls),*
        ];

        // The report test runs as part of `cargo test`. It iterates
        // each non-skipped target's mutants in process, tallies kill
        // rates, writes a full report to
        // `target/verus-spec-check-cov-mutate.txt` (under
        // CARGO_MANIFEST_DIR), prints the report to stderr (visible
        // with `cargo test -- --nocapture`), and panics if any
        // configured threshold is violated.
        //
        // Always skipped under Miri: the per-mutant loop alone takes
        // multiple minutes interpreted, which makes `cargo miri test`
        // unusable. Run the mutation report under regular cargo test.
        #[test]
        #[cfg_attr(miri, ignore)]
        #[allow(non_snake_case)]
        fn __vcheck_mutation_report() {
            ::verus_spec_check::cov_mutate::run_mutation_report(
                env!("CARGO_MANIFEST_DIR"),
                &__VCHECK_COV_MUTATE_TARGETS,
            );
        }
    })
}

/// Build a `VcheckCovMutateTarget { ... mutants: &[ ... ] }` literal.
pub fn emit_target_decl(target: &CovMutateTarget, mutant_consts: &[TokenStream2]) -> TokenStream2 {
    let fn_name = &target.fn_name;
    let threshold_expr: TokenStream2 = match target.threshold {
        Some(n) => {
            let n = n as u8;
            quote! { ::std::option::Option::Some(#n) }
        }
        None => quote! { ::std::option::Option::None },
    };
    let skip = target.skip;
    // The macro doesn't have access to `file!()` in a const context the
    // way a runtime fn does, so we punt: the report will use the
    // per-mutant `line` and label the `file` as a placeholder. Users
    // who need a precise file path can `cargo test -- --nocapture` and
    // the report will show file:line for each survivor.
    quote! {
        ::verus_spec_check::cov_mutate::VcheckCovMutateTarget {
            fn_name: #fn_name,
            file: file!(),
            mutants: &[ #(#mutant_consts),* ],
            threshold: #threshold_expr,
            skip: #skip,
        }
    }
}

/// Emit a parallel `fn __vcheck_mutant_<k>_<orig>(args) -> ret { <mutated body> }`
/// for a free-fn target. The signature mirrors the original fn's exec
/// signature (param names, types, return type) but with all Verus
/// annotations removed: no `requires`/`ensures`, no `(out: T)`-style
/// named return, no `exec`/`spec` mode keywords.
pub fn emit_mutant_fn_freefn(
    item_fn: &verus_syn::ItemFn,
    mutant_fn_ident: &Ident,
    mutated_body: &verus_syn::Block,
) -> TokenStream2 {
    let sig = strip_verus_sig_for_mutant(&item_fn.sig);
    let attrs: Vec<&verus_syn::Attribute> = item_fn
        .attrs
        .iter()
        .filter(|a| !attr_belongs_to_verus(a))
        .collect();
    quote! {
        #(#attrs)*
        #[allow(unused_variables, unused_mut, dead_code, non_snake_case)]
        pub(super) fn #mutant_fn_ident #sig
            #mutated_body
    }
}

/// Same as `emit_mutant_fn_freefn` but for impl methods. For
/// `impl<T> Container<T> { fn step(&mut self) { ... } }` we emit
/// `fn __vcheck_mutant_<k>_step(self_value: &mut Container<T>) { ... }` —
/// a free fn with the receiver remapped to a positional parameter, so
/// the body's `self.<x>` references must be rewritten to
/// `self_value.<x>`. We reuse `replace_self_with_ident` for that pass
/// (the same one used by the regular harness).
pub fn emit_mutant_fn_method(
    self_ty: &Ident,
    method: &verus_syn::ImplItemFn,
    mutant_fn_ident: &Ident,
    mutated_body: &verus_syn::Block,
) -> TokenStream2 {
    // Walk a clone of the body to replace `self` -> `self_value`.
    let mut body = mutated_body.clone();
    let synth_self = Ident::new("self_value", proc_macro2::Span::call_site());
    {
        struct R<'a> {
            replacement: &'a Ident,
        }
        impl<'a> VisitMut for R<'a> {
            fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
                for seg in p.path.segments.iter_mut() {
                    if seg.ident == "self" {
                        seg.ident = self.replacement.clone();
                    }
                }
                verus_syn::visit_mut::visit_expr_path_mut(self, p);
            }
        }
        let mut r = R {
            replacement: &synth_self,
        };
        for stmt in body.stmts.iter_mut() {
            match stmt {
                verus_syn::Stmt::Local(local) => {
                    if let Some(init) = &mut local.init {
                        r.visit_expr_mut(&mut init.expr);
                    }
                }
                verus_syn::Stmt::Expr(e, _) => r.visit_expr_mut(e),
                _ => {}
            }
        }
    }

    // Reconstruct the signature with the receiver translated to a
    // positional `self_value: &<Self>` (or `&mut <Self>`) parameter.
    let sig = strip_verus_sig_for_mutant_method(&method.sig, self_ty, &synth_self);
    let attrs: Vec<&verus_syn::Attribute> = method
        .attrs
        .iter()
        .filter(|a| !attr_belongs_to_verus(a))
        .collect();
    quote! {
        #(#attrs)*
        #[allow(unused_variables, unused_mut, dead_code, non_snake_case)]
        pub(super) fn #mutant_fn_ident #sig
            #body
    }
}

/// True if `attr` is a Verus-only attribute we should drop on the
/// mutant fn (because the mutant has no contract / mode / etc.).
pub fn attr_belongs_to_verus(attr: &verus_syn::Attribute) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    matches!(
        &segs[..],
        ["vcheck"]
            | ["contrib", "vcheck"]
            | ["vstd", "contrib", "vcheck"]
            | ["vcheck_cov_mutate"]
            | ["contrib", "vcheck_cov_mutate"]
            | ["vstd", "contrib", "vcheck_cov_mutate"]
            | ["vcheck_cov_fuzz"]
            | ["contrib", "vcheck_cov_fuzz"]
            | ["vstd", "contrib", "vcheck_cov_fuzz"]
            | ["vcheck_provide"]
            | ["contrib", "vcheck_provide"]
            | ["vstd", "contrib", "vcheck_provide"]
            | ["verifier", _]
            | ["verus", ..]
            | ["verus_spec"]
    )
}

/// Build a fn signature suitable for the mutant fn: same generics +
/// inputs + return type as the original, but with the Verus-specific
/// extensions (named return `(out: T)`, `requires`, `ensures`,
/// `decreases`, mode keywords) stripped out.
pub fn strip_verus_sig_for_mutant(orig: &verus_syn::Signature) -> TokenStream2 {
    let generics = &orig.generics;
    let inputs: Vec<TokenStream2> = orig
        .inputs
        .iter()
        .map(|arg| match &arg.kind {
            FnArgKind::Receiver(_r) => {
                // Free fns don't have receivers — this branch
                // shouldn't fire from `emit_mutant_fn_freefn`.
                quote! {}
            }
            FnArgKind::Typed(pt) => {
                let pat = &pt.pat;
                let ty = &pt.ty;
                quote! { #pat: #ty }
            }
        })
        .collect();
    let ret_ty: TokenStream2 = match &orig.output {
        ReturnType::Default => quote! {},
        ReturnType::Type(_, _, _, ty) => quote! { -> #ty },
    };
    let where_clause: TokenStream2 = match &generics.where_clause {
        Some(wc) => quote! { #wc },
        None => quote! {},
    };
    quote! { #generics ( #(#inputs),* ) #ret_ty #where_clause }
}

/// Same as `strip_verus_sig_for_mutant` but for impl methods, with the
/// receiver translated to `self_value: &<Self>` / `&mut <Self>` /
/// `<Self>`.
pub fn strip_verus_sig_for_mutant_method(
    orig: &verus_syn::Signature,
    self_ty: &Ident,
    self_replacement: &Ident,
) -> TokenStream2 {
    let generics = &orig.generics;
    let mut inputs: Vec<TokenStream2> = Vec::new();
    for arg in &orig.inputs {
        match &arg.kind {
            FnArgKind::Receiver(r) => {
                let self_param: TokenStream2 = if r.reference.is_some() {
                    if r.mutability.is_some() {
                        quote! { #self_replacement: &mut #self_ty }
                    } else {
                        quote! { #self_replacement: &#self_ty }
                    }
                } else {
                    quote! { #self_replacement: #self_ty }
                };
                inputs.push(self_param);
            }
            FnArgKind::Typed(pt) => {
                let pat = &pt.pat;
                let ty = &pt.ty;
                inputs.push(quote! { #pat: #ty });
            }
        }
    }
    let ret_ty: TokenStream2 = match &orig.output {
        ReturnType::Default => quote! {},
        ReturnType::Type(_, _, _, ty) => quote! { -> #ty },
    };
    let where_clause: TokenStream2 = match &generics.where_clause {
        Some(wc) => quote! { #wc },
        None => quote! {},
    };
    quote! { #generics ( #(#inputs),* ) #ret_ty #where_clause }
}
