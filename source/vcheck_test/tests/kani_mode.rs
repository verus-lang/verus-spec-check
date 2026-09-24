mod common;
use common::*;

// A clean contract with a precondition: pins the `requires` ->
// `kani::assume` lowering (the proof must cover the FULL constrained
// domain, not skip-reject like the test engines) and the i128
// spec-int model on add/mul — the exact shape that used to time out.
test_kani_one_file! {
    #[test] kani_proves_clean_contract vcheck_code! {
        #[vcheck(mode = "kani")]
        fn safe_double(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x + x
        }

        #[vcheck(mode = "kani")]
        fn clamped_sum(a: u16, b: u16) -> (r: u32)
            ensures
                r == a as u32 + b as u32,
                r <= 0x1FFFE,
        {
            a as u32 + b as u32
        }
    } => KaniOutcome::Proves
}

// A broken contract must be REFUTED — otherwise the proving case can't
// distinguish "verified" from "analyzed nothing". The bug only
// manifests off the precondition's edge (x == 0 passes), so a refuting
// counterexample also demonstrates the assume didn't over-constrain.
test_kani_one_file! {
    #[test] kani_refutes_broken_contract vcheck_code! {
        #[vcheck(mode = "kani")]
        fn double_wrong(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x // BUG: not doubled
        }
    } => KaniOutcome::Refutes
}

// ---------------------------------------------------------------------------
// One-command path: plain `cargo test` drives the proof via the emitted
// `__vcheck_kani_report` orchestration test (VERUS_SPEC_CHECK_KANI=1 in the
// runner; ordinary cases keep the tier disabled).
// ---------------------------------------------------------------------------

// Clean contract: `cargo test` runs the random smoke harness AND the
// report test, which spawns `cargo kani --tests` and verifies the
// harness. One command, proof included.
test_kani_report_one_file! {
    #[test] cargo_test_proves_via_report vcheck_code! {
        #[vcheck(mode = "kani")]
        fn safe_shift(x: u8) -> (r: u16)
            requires x <= 8,
            ensures r == (1u16 << x) as u16,
        {
            1u16 << x
        }
    } => HarnessOutcome::PassWithKaniReport { harnesses: 1 }
}

// Broken contract: the report must REFUTE it (the random smoke will
// usually also catch this concretely, but the needle pins the kani
// verdict specifically — proving the failure came from the proof
// tier, not just the smoke).
test_kani_report_one_file! {
    #[test] cargo_test_refutes_via_report vcheck_code! {
        #[vcheck(mode = "kani")]
        fn off_by_one(x: u32) -> (r: u32)
            requires x < 1000,
            ensures r == x + 1,
        {
            // BUG: correct except at a single hard-to-sample point.
            // The random smoke at default iterations is unlikely to
            // hit exactly 999, so a refutation REQUIRES the proof
            // tier — this case would pass a smoke-only run.
            if x == 999 { 0 } else { x + 1 }
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "REFUTED" }
}

// The explicit opt-out knob (the default for every other case in this
// suite, via the runner env): the report prints a disabled note and
// passes — mode="kani" crates stay testable on kani-less machines by
// explicit choice, never by silent skip.
test_bolero_one_file! {
    #[test] kani_tier_disabled_by_knob_passes vcheck_code! {
        #[vcheck(mode = "kani")]
        fn ident(x: u8) -> (r: u8)
            ensures r == x,
        {
            x
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}
