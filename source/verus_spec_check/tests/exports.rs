use verus_spec_check::*;

// A compile-time check that bolero properly exports at `verus_spec_check::bolero`.
#[cfg(all(test, feature = "bolero"))]
mod bolero_reexport_check {
    #[test]
    fn bolero_paths_resolve() {
        // A tiny bolero generator to see if it compiles right
        #[allow(unused_imports)]
        use crate::bolero_generator::prelude::*;
        let _g = crate::bolero_generator::produce::<u32>();

        // The `check!` entry point lives here, and naming the module path is enough
        // to prove the re-export resolves.
        #[allow(unused_imports)]
        use crate::bolero::check;
    }

    // Functional end-to-end check that the bundled-by-default bolero stack
    // works through the *exact* umbrella paths the engine emits into harness
    // modules — `::verus_spec_check::vcheck_gen::<T>()` driven by `::verus_spec_check::
    // bolero_generator`. Because the `bolero` feature is on by default, this
    // runs on a plain `cargo test` with no feature flags: the whole point of
    // "bolero packaged by default".
    #[test]
    fn bolero_generator_produces_value_via_umbrella_paths() {
        use crate::bolero_generator::driver::ByteSliceDriver;
        use crate::bolero_generator::prelude::*;

        let gen = crate::vcheck_gen::<u32>();
        // Any non-empty byte source drives a deterministic draw.
        let bytes = 0x9E37_79B9_7F4A_7C15u64.to_le_bytes();
        let mut driver = ByteSliceDriver::new(&bytes, &Default::default());
        let value = gen.generate(&mut driver);
        assert!(value.is_some(), "vcheck_gen::<u32>() produced no value");
    }
}

// Compile + behavior check that the `spec_real` surface resolves through the
// exact umbrella paths the contract rewriter emits (`::verus_spec_check::__vcheck_real::*`
// and `::verus_spec_check::SpecReal`), mirroring the `__vcheck_int` path. Not feature
// gated — `real` support is always available.
#[cfg(test)]
mod spec_real_reexport_check {
    #[test]
    fn vcheck_real_paths_resolve() {
        // int -> real, exact arithmetic (the property f64 gets wrong).
        crate::__vcheck_real::reset_defined();
        let half = crate::__vcheck_real::div(crate::__vcheck_real::from_int(1u8), 2u8);
        let one = crate::__vcheck_real::mul(&half, 2u8);
        assert!(crate::__vcheck_real::eq(one, crate::__vcheck_real::from_int(1u8)));
        assert!(crate::__vcheck_real::is_defined());

        // real ÷ 0 and non-finite float -> real mark the clause undefined
        // (the harness skips such a case).
        crate::__vcheck_real::reset_defined();
        let _ = crate::__vcheck_real::div(crate::__vcheck_real::from_int(1u8), 0u8);
        assert!(!crate::__vcheck_real::is_defined());
        crate::__vcheck_real::reset_defined();
        let _ = crate::__vcheck_real::from_f64(f64::NAN);
        assert!(!crate::__vcheck_real::is_defined());

        // The public type alias resolves at the umbrella root.
        let _r: crate::SpecReal = crate::__vcheck_real::from_f64(0.5);
    }
}

// Manifest-level guard that the bolero backend is *packaged by default*: the
// `bolero` cargo feature must be in the `default` feature list of both the
// umbrella crate and the runtime crate it forwards to. This is the invariant
// the "bundle bolero by default" change establishes. It is intentionally NOT
// gated on `feature = "bolero"` so it still runs (and passes) under
// `--no-default-features` — it inspects the manifest text, not the active cfg,
// so an intentional opt-out build can't mask a regression in the default.
#[cfg(test)]
mod default_feature_manifest_check {
    /// Extract the values of the `default = [ ... ]` key from a Cargo manifest.
    /// A small hand-rolled scan (no `toml` dep): find the top-level `default`
    /// feature key and split its single-line array. Returns an empty vec if
    /// there is no `default` key.
    fn default_feature_list(manifest: &str) -> Vec<String> {
        for line in manifest.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with('#') {
                continue;
            }
            // Match the `default` feature key exactly (not `default-features`,
            // which appears on dependency lines).
            let Some(after_key) = trimmed.strip_prefix("default") else {
                continue;
            };
            let after_key = after_key.trim_start();
            let Some(after_eq) = after_key.strip_prefix('=') else {
                continue;
            };
            let rhs = after_eq.trim();
            if let Some(inner) = rhs.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
                return inner
                    .split(',')
                    .map(|s| s.trim().trim_matches('"').to_string())
                    .filter(|s| !s.is_empty())
                    .collect();
            }
        }
        Vec::new()
    }

    #[test]
    fn umbrella_defaults_include_bolero() {
        let manifest = include_str!("../Cargo.toml");
        let defaults = default_feature_list(manifest);
        assert!(
            defaults.iter().any(|f| f == "bolero"),
            "verus_spec_check umbrella `default` features must include \"bolero\" \
             (bolero is packaged by default); found {defaults:?}"
        );
    }

    #[test]
    fn runtime_defaults_include_bolero() {
        let manifest = include_str!("../../runtime/Cargo.toml");
        let defaults = default_feature_list(manifest);
        assert!(
            defaults.iter().any(|f| f == "bolero"),
            "verus_spec_check_runtime `default` features must include \"bolero\" \
             (bolero is packaged by default); found {defaults:?}"
        );
    }

    // Guard the parser itself so the checks above can't silently pass on a
    // manifest shape they fail to understand.
    #[test]
    fn parser_extracts_and_ignores_correctly() {
        assert_eq!(
            default_feature_list("[features]\ndefault = [\"bolero\"]\n"),
            vec!["bolero".to_string()]
        );
        assert_eq!(
            default_feature_list("default = [\"a\", \"b\"]\n"),
            vec!["a".to_string(), "b".to_string()]
        );
        // `default-features = false` on a dependency line must not be picked up.
        assert!(default_feature_list("dep = { default-features = false }\n").is_empty());
        // Commented-out default must be ignored.
        assert!(default_feature_list("# default = [\"bolero\"]\n").is_empty());
        // No default key at all.
        assert!(default_feature_list("[features]\nbolero = []\n").is_empty());
    }
}
