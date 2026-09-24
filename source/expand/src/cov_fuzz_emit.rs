use super::*;

/// Stable macro-time selector for rescue side builds. It deliberately uses
/// only syntax available to the proc macro (the external path, wrapper name,
/// generic spellings, and expansion-local ordinal); `module_path!()` is not
/// available until the generated crate is compiled. A collision merely puts
/// two targets in one rescue shard—it cannot misattribute profile identity.
fn covext_compile_selector(target: &CovFuzzTarget, target_index: usize) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut feed = |text: &str| {
        for byte in text.bytes() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(0x100_0000_01b3);
        }
        hash ^= 0xff;
        hash = hash.wrapping_mul(0x100_0000_01b3);
    };
    feed(target.external.as_deref().unwrap_or("local"));
    feed(&target.fn_name);
    feed(&target_index.to_string());
    for param in &target.generic_type_params {
        feed(param);
    }
    format!("{hash:016x}")
}

/// Build the cov_fuzz test-module contents for a `Classified` with
/// non-empty `cov_fuzz_targets`. Returns an empty token stream when no
/// targets are present. Emits, for each non-skipped target:
///
///  - A per-fn hit-bit static `__VCHECK_COVF_HITS_<fn>: [AtomicBool; N]`
///    (one slot per branch arm the instrumenter found) plus its marker
///    fn `__vcheck_covmark_<fn>(i)` that the instrumented body calls at
///    each arm entry.
///  - An *instrumented twin* `__vcheck_covfuzz_fn_<fn>` — same signature
///    as the original (contract attrs stripped, methods lowered to a
///    free fn with a `self_value` positional param, reusing the
///    cov_mutate twin emitters), body instrumented by
///    `verus_spec_check_instrument::instrument_branches`.
///  - A runner `__vcheck_covfuzz_run_<fn>` produced by
///    [`emit_harness_with_flavor`] in [`HarnessFlavor::CovFuzzRunner`]
///    mode: an in-process coverage-guided search that decodes byte
///    buffers through the bolero generator stack, filters through
///    `requires` (with per-clause guidance bits), and calls the twin.
///  - One `VcheckCovFuzzBranch` slice + `VcheckCovFuzzTarget` entry.
///
/// plus a single aggregating `#[test] fn __vcheck_cov_fuzz_report()` that
/// calls `run_cov_fuzz_report` with the targets. Everything runs in
/// process under plain `cargo test` — no external tooling — mirroring
/// the `#[vcheck_cov_mutate]` architecture.
///
/// Note: the runner decodes inputs through `::verus_spec_check::
/// bolero_generator`, so a crate using `#[vcheck_cov_fuzz]` needs the
/// umbrella's `bolero` feature (on by default; a `default-features =
/// false` opt-out build will fail to resolve the path).
pub fn emit_cov_fuzz_block(classified: &Classified) -> Result<TokenStream2, Error> {
    if classified.cov_fuzz_targets.is_empty() {
        return Ok(quote! {});
    }

    /// Per-fn cap on instrumented branch arms. Keeps compile time and
    /// hit-array size bounded; the instrumenter stops allocating sites
    /// past the cap. The emitted `branch_cap_hit` bit marks the result
    /// incomplete, and a capped target cannot satisfy a threshold.
    ///
    /// Generated symbols include this expansion's target ordinal, so a free
    /// function and method with the same bare name remain independent.
    const PER_FN_MAX_BRANCHES: usize = 128;

    let mut decls: Vec<TokenStream2> = Vec::new();
    let mut target_decls: Vec<TokenStream2> = Vec::new();

    for (target_index, target) in classified.cov_fuzz_targets.iter().enumerate() {
        let fn_ident_str = &target.fn_ident;
        let symbol = format!("{}_{}", target_index, fn_ident_str);
        let target_id = quote! {
            concat!(module_path!(), "::cov_fuzz:", stringify!(#target_index))
        };
        let compile_selector = covext_compile_selector(target, target_index);
        let hits_ident: Ident = format_ident!("__VCHECK_COVF_HITS_{}", symbol);
        let covered_ident: Ident = format_ident!("__VCHECK_COVF_COVERED_{}", symbol);
        let indeterminate_ident: Ident = format_ident!("__VCHECK_COVF_INDETERMINATE_{}", symbol);
        let scratch_ident: Ident = format_ident!("__VCHECK_COVF_SCRATCH_{}", symbol);
        let runner_ident: Ident = format_ident!("__vcheck_covfuzz_run_{}", symbol);
        let mut unlowerable_ensures: Vec<(usize, &'static str)> = Vec::new();

        // Skipped targets still appear in the report; we emit an empty
        // hit array and a stub runner (never called — the report checks
        // `skip` first) so the target struct is complete. External
        // (assume_specification) targets get the same stub run
        // machinery — their implementation lives outside this crate, so
        // there is nothing for the source-level instrumenter to
        // instrument — but non-skipped external targets additionally
        // get an engagement RECORDER + replay test pair (see the
        // CovExtRecorder flavor): the report runs the recorder in the
        // outer process and the instrumented side build replays the
        // recorded spec-engaged genomes.
        if target.skip || target.external.is_some() {
            let recorder_ident: Ident = format_ident!("__vcheck_covext_record_{}", symbol);
            decls.push(quote! {
                static #hits_ident: [::core::sync::atomic::AtomicBool; 0] = [];
                static #covered_ident: [::core::sync::atomic::AtomicBool; 0] = [];
                static #indeterminate_ident: [::core::sync::atomic::AtomicBool; 0] = [];
                #[allow(non_snake_case, dead_code)]
                pub(super) fn #runner_ident() -> ::verus_spec_check::cov_fuzz::CovFuzzRunStats {
                    ::core::default::Default::default()
                }
            });
            if target.external.is_some() && !target.skip {
                // Real recorder + replay pair via the harness emitter
                // (external targets are always free-fn assume wrappers).
                let CovMutateBodySource::FreeFn(item_fn) = &target.body_source else {
                    unreachable!("external cov_fuzz targets are always free fns");
                };
                let replay_ident: Ident = format_ident!("__vcheck_covext_replay_{}", symbol);
                let contract_target = ContractTarget::FreeFn {
                    item_fn: item_fn.clone(),
                    miri_skip: false,
                    backend: crate::vcheck_attr::VcheckBackend::Proptest,
                    bolero_mode: None,
                    skip_regular_harness: false,
                };
                let mut counter = 0u64;
                let recorder = emit_harness_with_flavor(
                    &contract_target,
                    &classified.spec_fn_names,
                    &classified.user_type_names,
                    &classified.when_used_as_spec_redirect,
                    &mut counter,
                    HarnessFlavor::CovExtRecorder {
                        recorder_name: recorder_ident.clone(),
                        replay_test_name: replay_ident.clone(),
                        target_id: target_id.clone(),
                        compile_selector: compile_selector.clone(),
                    },
                )?;
                unlowerable_ensures = recorder.unlowerable_ensures.clone();
                for synth in recorder.synthetic_spec_fns {
                    decls.push(synth);
                }
                decls.push(recorder.harness_tokens);
            } else {
                // Skipped (or skipped-external) targets: stub recorder,
                // never called (the orchestrator filters on `skip`).
                decls.push(quote! {
                    #[allow(non_snake_case, dead_code)]
                    pub(super) fn #recorder_ident() -> ::verus_spec_check::cov_fuzz::CovExtRecording {
                        ::core::default::Default::default()
                    }
                });
            }
            let replay_test_expr = if target.external.is_some() && !target.skip {
                let replay_ident: Ident = format_ident!("__vcheck_covext_replay_{}", symbol);
                quote! { concat!(module_path!(), "::", stringify!(#replay_ident)) }
            } else {
                quote! { "" }
            };
            target_decls.push(emit_cov_fuzz_target_decl(
                target,
                &target_id,
                &compile_selector,
                false,
                &replay_test_expr,
                &[],
                &hits_ident,
                &covered_ident,
                &indeterminate_ident,
                &unlowerable_ensures,
                &runner_ident,
                &recorder_ident,
            ));
            continue;
        }

        // Enumerate branch arms and build the instrumented body.
        let body = match &target.body_source {
            CovMutateBodySource::FreeFn(item_fn) => item_fn.block.as_ref().clone(),
            CovMutateBodySource::Method { method, .. } => method.block.clone(),
        };
        let marker_ident: Ident = format_ident!("__vcheck_covmark_{}", symbol);
        let (sites, instrumented_body, hit_cap) =
            crate::vcheck_instrument::instrument_branches(&body, &marker_ident, PER_FN_MAX_BRANCHES);
        let n_sites = sites.len();

        // Hit/covered/scratch statics + marker fn. Const-item repetition
        // keeps the array inits valid for non-Copy AtomicBool on stable.
        // The marker writes the cumulative `reached` bit AND the
        // per-execution scratch bit; the runner merges scratch into
        // `covered` only when the execution turns out to be
        // spec-engaged (see the CovFuzzRunner flavor docs).
        decls.push(quote! {
            static #hits_ident: [::core::sync::atomic::AtomicBool; #n_sites] =
                [__VCHECK_COVF_FALSE_INIT; #n_sites];
            static #covered_ident: [::core::sync::atomic::AtomicBool; #n_sites] =
                [__VCHECK_COVF_FALSE_INIT; #n_sites];
            static #indeterminate_ident: [::core::sync::atomic::AtomicBool; #n_sites] =
                [__VCHECK_COVF_FALSE_INIT; #n_sites];
            static #scratch_ident: [::core::sync::atomic::AtomicBool; #n_sites] =
                [__VCHECK_COVF_FALSE_INIT; #n_sites];
            #[allow(non_snake_case, dead_code)]
            pub(super) fn #marker_ident(__vcheck_i: usize) {
                if let ::core::option::Option::Some(__vcheck_b) = #hits_ident.get(__vcheck_i) {
                    __vcheck_b.store(true, ::core::sync::atomic::Ordering::Relaxed);
                }
                if let ::core::option::Option::Some(__vcheck_b) = #scratch_ident.get(__vcheck_i) {
                    __vcheck_b.store(true, ::core::sync::atomic::Ordering::Relaxed);
                }
            }
        });

        // Instrumented twin: same emitters the mutant fns use (sig with
        // Verus annotations stripped; methods lowered to a free fn with
        // `self_value`), just with the instrumented body instead of a
        // mutated one.
        let twin_ident: Ident = format_ident!("__vcheck_covfuzz_fn_{}", symbol);
        let twin_ts = match &target.body_source {
            CovMutateBodySource::FreeFn(item_fn) => {
                emit_mutant_fn_freefn(item_fn, &twin_ident, &instrumented_body)
            }
            CovMutateBodySource::Method { self_ty, method } => {
                emit_mutant_fn_method(self_ty, method, &twin_ident, &instrumented_body)
            }
        };
        decls.push(twin_ts);

        // Runner via the harness emitter (contract target is the
        // ORIGINAL fn so the requires clauses and generator shapes are
        // correct; the call routes through the twin). Backend fields
        // are defaulted the same way cov_mutate's runner defaults them
        // — the CovFuzzRunner flavor picks its own input machinery.
        let contract_target = match &target.body_source {
            CovMutateBodySource::FreeFn(item_fn) => ContractTarget::FreeFn {
                item_fn: item_fn.clone(),
                miri_skip: false,
                backend: crate::vcheck_attr::VcheckBackend::Proptest,
                bolero_mode: None,
                skip_regular_harness: false,
            },
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
            HarnessFlavor::CovFuzzRunner {
                runner_name: runner_ident.clone(),
                twin_call_fn: twin_ident.clone(),
                hits_static: hits_ident.clone(),
                covered_static: covered_ident.clone(),
                indeterminate_static: indeterminate_ident.clone(),
                scratch_static: scratch_ident.clone(),
            },
        )?;
        // Synthetic spec fns from quantified clauses land in the harness
        // module alongside the runner (same convention as cov_mutate).
        unlowerable_ensures = runner.unlowerable_ensures.clone();
        for synth in runner.synthetic_spec_fns {
            decls.push(synth);
        }
        decls.push(runner.harness_tokens);

        // Branch metadata for the report.
        let branch_consts: Vec<TokenStream2> = sites
            .iter()
            .map(|s| {
                let idx = s.idx;
                let line = s.line;
                let desc = &s.description;
                quote! {
                    ::verus_spec_check::cov_fuzz::VcheckCovFuzzBranch {
                        idx: #idx,
                        line: #line,
                        description: #desc,
                    }
                }
            })
            .collect();
        // Non-external targets never consult the recorder; a stub
        // keeps the decl uniform.
        let recorder_ident: Ident = format_ident!("__vcheck_covext_record_{}", symbol);
        decls.push(quote! {
            #[allow(non_snake_case, dead_code)]
            pub(super) fn #recorder_ident() -> ::verus_spec_check::cov_fuzz::CovExtRecording {
                ::core::default::Default::default()
            }
        });
        let replay_test_expr = quote! { "" };
        target_decls.push(emit_cov_fuzz_target_decl(
            target,
            &target_id,
            &compile_selector,
            hit_cap,
            &replay_test_expr,
            &branch_consts,
            &hits_ident,
            &covered_ident,
            &indeterminate_ident,
            &unlowerable_ensures,
            &runner_ident,
            &recorder_ident,
        ));
    }

    let n = target_decls.len();
    Ok(quote! {
        // Shared zero-initializer for the hit-bit statics (const-item
        // repetition — `AtomicBool` isn't Copy).
        #[allow(clippy::declare_interior_mutable_const, dead_code)]
        const __VCHECK_COVF_FALSE_INIT: ::core::sync::atomic::AtomicBool =
            ::core::sync::atomic::AtomicBool::new(false);

        // Hit statics, marker fns, instrumented twins, runners.
        #(#decls)*

        // Per-fn target metadata. A `static` (not `const`) because the
        // entries reference the hit-bit statics.
        static __VCHECK_COV_FUZZ_TARGETS:
            [::verus_spec_check::cov_fuzz::VcheckCovFuzzTarget; #n] = [
            #(#target_decls),*
        ];

        // Link-time registration for the whole-binary campaign audit
        // (`VERUS_SPEC_CHECK_COV_CAMPAIGN=1`): every expansion contributes its
        // target table to the runtime's distributed slice so ONE report
        // pass can walk all of them. `#[linkme(crate = ...)]` points the
        // attribute macro at the re-exported linkme.
        #[::verus_spec_check::cov_fuzz::linkme::distributed_slice(
            ::verus_spec_check::cov_fuzz::VCHECK_COV_FUZZ_REGISTRY
        )]
        #[linkme(crate = ::verus_spec_check::cov_fuzz::linkme)]
        #[allow(non_upper_case_globals)]
        static __VCHECK_COV_FUZZ_REGISTRY_ENTRY:
            ::verus_spec_check::cov_fuzz::VcheckCovFuzzRegistryEntry =
            ::verus_spec_check::cov_fuzz::VcheckCovFuzzRegistryEntry {
                crate_dir: env!("CARGO_MANIFEST_DIR"),
                targets: &__VCHECK_COV_FUZZ_TARGETS,
            };

        // The report test runs as part of `cargo test`: it drives each
        // non-skipped target's coverage-guided search in process, reads
        // back the hit bits, prints the branch-coverage report, and
        // panics if any configured threshold is violated.
        //
        // Skipped under Miri: thousands of interpreted executions per
        // target make `cargo miri test` unusable; run the coverage
        // report under regular cargo test.
        #[test]
        #[cfg_attr(miri, ignore)]
        #[allow(non_snake_case)]
        fn __vcheck_cov_fuzz_report() {
            ::verus_spec_check::cov_fuzz::run_cov_fuzz_report(
                env!("CARGO_MANIFEST_DIR"),
                &__VCHECK_COV_FUZZ_TARGETS,
            );
        }
    })
}

/// Build a `VcheckCovFuzzTarget { ... }` literal.
fn emit_cov_fuzz_target_decl(
    target: &CovFuzzTarget,
    target_id: &TokenStream2,
    compile_selector: &str,
    branch_cap_hit: bool,
    replay_test_expr: &TokenStream2,
    branch_consts: &[TokenStream2],
    hits_ident: &Ident,
    covered_ident: &Ident,
    indeterminate_ident: &Ident,
    unlowerable_ensures: &[(usize, &'static str)],
    runner_ident: &Ident,
    recorder_ident: &Ident,
) -> TokenStream2 {
    let fn_name = &target.fn_name;
    let threshold_expr: TokenStream2 = match target.threshold {
        Some(n) => {
            let n = n as u8;
            quote! { ::std::option::Option::Some(#n) }
        }
        None => quote! { ::std::option::Option::None },
    };
    let skip = target.skip;
    let generic_type_params = &target.generic_type_params;
    // External (assume_specification) targets carry the wrapped path,
    // its original type parameters, and the engagement recorder the report
    // runs in the outer process.
    let external_expr: TokenStream2 = match &target.external {
        Some(path) => {
            quote! {
                ::std::option::Option::Some(::verus_spec_check::cov_fuzz::VcheckCovFuzzExternal {
                    target_path: #path,
                    generic_type_params: &[#(#generic_type_params),*],
                    compile_selector: #compile_selector,
                    replay_test: #replay_test_expr,
                    recorder: #recorder_ident,
                })
            }
        }
        None => quote! { ::std::option::Option::None },
    };
    let unlowerable_entries = unlowerable_ensures.iter().map(|(clause, reason)| {
        quote! {
            ::verus_spec_check::cov_fuzz::VcheckCovFuzzUnlowerableClause {
                clause: #clause,
                reason: #reason,
            }
        }
    });
    quote! {
        ::verus_spec_check::cov_fuzz::VcheckCovFuzzTarget {
            target_id: #target_id,
            fn_name: #fn_name,
            file: file!(),
            branch_cap_hit: #branch_cap_hit,
            branches: &[ #(#branch_consts),* ],
            hits: &#hits_ident,
            covered: &#covered_ident,
            indeterminate: &#indeterminate_ident,
            unlowerable_ensures: &[#(#unlowerable_entries),*],
            run: #runner_ident,
            threshold: #threshold_expr,
            skip: #skip,
            external: #external_expr,
        }
    }
}
