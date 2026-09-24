use super::*;

// ---------------------------------------------------------------------------
// Top-level entry point
// ---------------------------------------------------------------------------

pub static UNIQUE_ID: AtomicU64 = AtomicU64::new(0);

pub fn fresh_mod_name() -> Ident {
    let id = UNIQUE_ID.fetch_add(1, Ordering::Relaxed);
    Ident::new(&format!("__verus_spec_check_{}", id), Span::call_site())
}

pub fn expand(input: TokenStream, verified: bool) -> TokenStream {
    let parsed: VcheckItems = match verus_syn::parse2::<VcheckItems>(input) {
        Ok(v) => v,
        Err(e) => return e.to_compile_error(),
    };
    let classified = classify(parsed.0);

    // Hard classification errors (e.g. a `#[vcheck]`-marked fn with no
    // contract clauses) fail the build before any emission — the
    // alternative was a silent no-harness expansion, which is exactly
    // the vacuous-green shape this crate exists to prevent.
    if !classified.contract_errors.is_empty() {
        let mut out = TokenStream2::new();
        for err in &classified.contract_errors {
            out.extend(err.to_compile_error());
        }
        return out;
    }

    // Build harnesses first; they may produce synthetic spec fns that need
    // to be appended to the engine input.
    let mut clause_counter: u64 = 0;
    let mut harnesses_tokens: Vec<TokenStream2> = Vec::new();
    let mut synthetic_spec_fns: Vec<TokenStream2> = Vec::new();
    for target in &classified.contract_targets {
        // Targets that are present only to serve as enclosing-context
        // for an inline-assert harness: skip the regular harness
        // emission. The inline-assert harness still fires via
        // `emit_inline_assert_block`.
        if target.skip_regular_harness() {
            continue;
        }
        let out = match emit_harness(
            target,
            &classified.spec_fn_names,
            &classified.user_type_names,
            &classified.when_used_as_spec_redirect,
            &mut clause_counter,
        ) {
            Ok(h) => h,
            Err(err) => return err.to_compile_error().into(),
        };
        harnesses_tokens.push(out.harness_tokens);
        synthetic_spec_fns.extend(out.synthetic_spec_fns);
    }

    // Build the engine input: classified.engine_items + synthetic spec fns.
    let engine_items_ts = {
        let items = &classified.engine_items;
        quote! {
            #(#items)*
            #(#synthetic_spec_fns)*
        }
    };

    let engine_block: TokenStream2 =
        crate::exec_spec::exec_spec(engine_items_ts.into(), /*unverified=*/ !verified).into();

    // Pass-through items.
    let v = crate::syntax::Vstd(Span::call_site());
    let passthrough_block = {
        let items = &classified.passthrough_items;
        quote! {
            #v::prelude::verus! {
                #(#items)*
            }
        }
    };

    // Does any harness target in this block use the bolero backend? If so we
    // additionally emit `TypeGenerator` + `VcheckGen` impls for user types (their
    // feature-gated paths only resolve when a bolero target forced the
    // `bolero` feature on). Inline-assert targets inherit their enclosing fn's
    // backend, so scanning `contract_targets` covers them too.
    // `#[vcheck_cov_fuzz]` runners also decode inputs through the bolero
    // generator stack, so any cov_fuzz target forces the bolero impls on
    // user types too.
    let wants_bolero = classified
        .contract_targets
        .iter()
        .any(|t| matches!(t.backend(), crate::vcheck_attr::VcheckBackend::Bolero))
        || !classified.cov_fuzz_targets.is_empty();

    // Strategy + Clone/Debug + to_exec converter for each user type, plus the
    // bolero generator impls when `wants_bolero`.
    let strategy_impls: Result<Vec<TokenStream2>, Error> = classified
        .user_types
        .iter()
        .map(|ut| {
            let base = match ut {
                UserType::Struct(s) => emit_struct_support(s, &classified.user_type_names)?,
                UserType::Enum(e) => emit_enum_support(e, &classified.user_type_names)?,
            };
            let bolero = if wants_bolero {
                match ut {
                    UserType::Struct(s) => {
                        emit_struct_bolero_impls(s, &classified.user_type_names)?
                    }
                    UserType::Enum(e) => emit_enum_bolero_impls(e, &classified.user_type_names)?,
                }
            } else {
                quote! {}
            };
            Ok(quote! { #base #bolero })
        })
        .collect();
    let strategy_block = match strategy_impls {
        Ok(impls) => {
            if impls.is_empty() {
                quote! {}
            } else {
                quote! {
                    #(#impls)*
                }
            }
        }
        Err(err) => return err.to_compile_error().into(),
    };

    // Emit `exec_<name>` fns into the harness module so 
    // contract calls `exec_<name>(..)` resolve. Errors here surface
    // as compile errors at the macro site.
    let external_companions = {
        let mut out = TokenStream2::new();
        for body in &classified.external_provide_bodies {
            match crate::external_vcheck_provide::emit_companions(body.clone()) {
                Ok(ts) => out.extend(ts),
                Err(err) => return err.to_compile_error().into(),
            }
        }
        out
    };

    // Single test module holding strategy/Clone/Debug/converter support AND
    // the proptest harnesses, so the harnesses can call the generated
    // `__vcheck_to_exec_*` converters and `vcheck_strategy::<UserType>()` directly.
    let mod_name = fresh_mod_name();

    // Emit per-fn mutant fns + per-mutant runners + metadata for
    // `#[vcheck_cov_mutate]`-marked targets. Each marked fn is mutated by
    // the body-mutator visitor, producing N parallel fns plus N runner
    // fns. The runners are aggregated via `__vcheck_mutation_report`,
    // which is a `#[test]` that drives them in-process (no external
    // tooling).
    let cov_mutate_block: TokenStream2 = match emit_cov_mutate_block(&classified) {
        Ok(ts) => ts,
        Err(e) => return e.to_compile_error().into(),
    };

    // Emit per-fn instrumented twins + coverage-guided runners + metadata
    // for `#[vcheck_cov_fuzz]`-marked targets, aggregated via the
    // `__vcheck_cov_fuzz_report` `#[test]` (in-process, no external
    // tooling — the cov_mutate sibling for branch coverage).
    let cov_fuzz_block: TokenStream2 = match emit_cov_fuzz_block(&classified) {
        Ok(ts) => ts,
        Err(e) => return e.to_compile_error().into(),
    };

    // Kani proof orchestration: when this block contains `mode = "kani"`
    // targets, emit ONE aggregating `__vcheck_kani_report` test that drives
    // `cargo kani --tests` as a side run (see runtime::kani_orch), so
    // plain `cargo test` covers the kani tier under the same interface
    // as every other mode. The body is cfg-gated on "no engine cfg":
    //   - the kani side build (`--cfg kani`) must not contain the test
    //     that spawns it (re-entrancy impossible by construction);
    //   - cargo-bolero's target discovery executes tests, and must not
    //     trip a minutes-long proof run.
    // Under miri the report is ignored (miri's isolation forbids
    // subprocesses), matching the cov_fuzz report convention.
    let kani_report_block: TokenStream2 = {
        let names: Vec<String> = classified
            .contract_targets
            .iter()
            .filter(|t| !t.skip_regular_harness())
            .filter(|t| matches!(t.bolero_mode(), Some(crate::vcheck_attr::VcheckBoleroMode::Kani)))
            .map(vcheck_harness_name)
            .collect();
        if names.is_empty() {
            quote! {}
        } else {
            quote! {
                #[test]
                #[allow(unexpected_cfgs)]
                #[cfg_attr(miri, ignore)]
                fn __vcheck_kani_report() {
                    #[cfg(not(any(
                        fuzzing_libfuzzer,
                        fuzzing_afl,
                        fuzzing_honggfuzz,
                        fuzzing_random,
                        kani
                    )))]
                    {
                        ::verus_spec_check::kani_orch::run_kani_report(
                            env!("CARGO_MANIFEST_DIR"),
                            &[#(#names),*],
                        );
                    }
                }
            }
        }
    };

    // Build the inline-assert harness block: emits checker fns +
    // `#[test]`s for `#[vcheck]`-marked asserts inside fn bodies. Returns
    // empty when there are no inline-assert targets.
    let inline_assert_block: TokenStream2 = match emit_inline_assert_block(&classified) {
        Ok(ts) => ts,
        Err(e) => return e.to_compile_error().into(),
    };

    let test_mod = if harnesses_tokens.is_empty()
        && classified.user_types.is_empty()
        && classified.cov_mutate_targets.is_empty()
        && classified.cov_fuzz_targets.is_empty()
        && classified.inline_assert_targets.is_empty()
    {
        quote! {}
    } else {
        quote! {
            #[cfg(test)]
            #[allow(non_snake_case)]
            #[allow(unused_imports)]
            #[allow(dead_code)]
            mod #mod_name {
                use super::*;
                use ::verus_spec_check::proptest::prelude::*;
                // Bring vstd-side exec_spec traits into scope so method
                // calls like `.exec_len()`, `.exec_index(...)`,
                // `.exec_count(...)` resolve to their trait impls. The
                // emitted impl declarations use absolute paths
                // (`::verus_spec_check_vstd_ext::*`), but method calls in
                // rewritten contract expressions need a `use` to find
                // the trait.
                use ::verus_spec_check_vstd_ext::*;
                // The BTreeMap/BTreeSet exec companions live in the
                // runtime crate (vstd's `DeepView for BTree*` is
                // ghost-gated, so vstd_ext can't host them; see the
                // `VcheckBTreeMapExec` docs). Their `&BTreeMap`/`&BTreeSet`
                // receivers are disjoint from the vstd_ext impls, so both
                // glob imports coexist without ambiguity.
                use ::verus_spec_check::{VcheckBTreeMapExec, VcheckBTreeSetExec};
                #strategy_block
                #external_companions
                #(#harnesses_tokens)*
                #cov_mutate_block
                #cov_fuzz_block
                #kani_report_block
                #inline_assert_block
            }
        }
    };

    // Inspection hook: when VERUS_SPEC_CHECK_PRINT_EXPANSION is set, print the
    // pretty-printed generated test module to stderr so the harnesses
    // can be inspected without a full `cargo expand` (which also
    // expands proptest's internals and the `#[test]` plumbing).
    maybe_print_expansion(&mod_name, &test_mod);

    let combined = quote! {
        #engine_block
        #passthrough_block
        #test_mod
    };

    combined.into()
}

/// When `VERUS_SPEC_CHECK_PRINT_EXPANSION` is set (to anything but `0`), print
/// the pretty-printed generated test module to stderr, bracketed by
/// `<pkg>.<mod_name>` markers.
///
/// Runs at macro-expansion time, so a fresh compile of the annotated
/// crate is required to see output; force one with e.g.:
///
/// ```bash
/// cargo clean -p mycrate && VERUS_SPEC_CHECK_PRINT_EXPANSION=1 cargo check
/// ```
fn maybe_print_expansion(mod_name: &Ident, test_mod: &TokenStream2) {
    if test_mod.is_empty() {
        return;
    }
    match std::env::var_os("VERUS_SPEC_CHECK_PRINT_EXPANSION") {
        None => return,
        Some(v) if v == "0" => return,
        Some(_) => {}
    }
    // CARGO_PKG_NAME here is the crate currently being *compiled* (the
    // user's crate), not this proc-macro crate.
    let pkg = std::env::var("CARGO_PKG_NAME").unwrap_or_else(|_| "unknown".to_string());
    eprintln!(
        "// ==== verus-spec-check expansion: {pkg}.{mod_name} ====\n{}\
         // ==== end {pkg}.{mod_name} ====",
        crate::render::pretty_tokens(test_mod)
    );
}
