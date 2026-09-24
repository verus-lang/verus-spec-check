mod common;
use common::*;

// A violation gated behind a narrow precondition AND two nested body
// branches with tight thresholds. One-shot random probability is
// (6/256)^3 ≈ 1.3e-5 — a plain random smoke at the default budget would
// most likely miss it — but the guided loop climbs it level by level:
// the requires-guidance bit rewards `a >= 250`, then each nested
// branch's hit bit rewards the next threshold. This is the case that
// distinguishes "actual fuzzer" from "random sampling".
test_bolero_one_file! {
    #[test] guided_search_finds_gated_violation vcheck_code! {
        #[vcheck(mode = "fuzz")]
        fn gated(a: u8, b: u8, c: u8) -> (r: u8)
            requires a >= 250,
            ensures r == 0,
        {
            if b >= 250 {
                if c >= 250 {
                    77  // BUG: reachable only at the top of the gradient
                } else {
                    0
                }
            } else {
                0
            }
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "found a contract violation" }
}

// The failure report carries the ORIGINAL ensures clause text (not the
// lowered `__vcheck_int` form) and the decoded counterexample.
test_bolero_one_file! {
    #[test] failure_reports_original_clause vcheck_code! {
        #[vcheck(mode = "fuzz")]
        fn double_wrong(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x // BUG: not doubled
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "ensures clause failed: `r == x * 2`" }
}

// A precondition no sampled input can satisfy must fail loudly as
// vacuous, not pass green having never evaluated the contract — the
// bolero half's vacuity check, ported to the guided loop's stats.
test_bolero_one_file! {
    #[test] unsatisfiable_requires_is_vacuous vcheck_code! {
        #[vcheck(mode = "fuzz")]
        fn never_tested(x: u8) -> (r: u8)
            requires x as u16 > 300,
            ensures r == x,
        {
            x
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "vacuous fuzz harness" }
}

// Impl-method target: exercises the method twin path (receiver lowered
// to a `self_value` positional param) and the `<SelfTy>_<fn>`-suffixed
// twin/hits/marker naming, on a passing contract with branches and a
// precondition.
test_bolero_one_file! {
    #[test] method_target_passes vcheck_code! {
        pub struct Counter { pub v: u8 }

        impl Counter {
            #[vcheck(mode = "fuzz")]
            pub fn saturating_step(&self, by: u8) -> (r: u8)
                requires by <= 100,
                ensures
                    self.v as u16 + by as u16 <= 255 ==> r == self.v + by,
                    self.v as u16 + by as u16 > 255 ==> r == 255,
            {
                if self.v as u16 + by as u16 <= 255 {
                    self.v + by
                } else {
                    255
                }
            }
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}
