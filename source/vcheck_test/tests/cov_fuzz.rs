mod common;
use common::*;

// Both arms of a simple if/else are reachable from the full input
// domain, so a 100% threshold passes. `&&` short-circuit and implicit
// else sites are exercised by the second fn.
fn reachable_pair_snippet() -> String {
    vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn abs_diff(a: u8, b: u8) -> (r: u8)
            ensures
                a >= b ==> r == a - b,
                a < b ==> r == b - a,
        {
            if a >= b {
                a - b
            } else {
                b - a
            }
        }

        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn both_big(a: u8, b: u8) -> (r: bool)
            ensures r == (a > 10 && b > 10),
        {
            if a > 10 && b > 10 {
                true
            } else {
                false
            }
        }
    }
}

test_vcheck_one_file! {
    #[test] reachable_arms_pass_full_threshold reachable_pair_snippet()
        => HarnessOutcome::PassWithCovFuzzReport { harnesses: 2 }
}

test_verify_one_file! {
    #[test] verify_reachable_pair reachable_pair_snippet()
        => VerifyOutcome::Verifies
}

// A `requires`-excluded arm: the precondition makes the then-arm dead.
// Without a threshold the report is informational — it lists the
// unreached arm but the test passes.
test_vcheck_one_file! {
    #[test] requires_excluded_arm_is_informational vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        fn bounded_incr(x: u8) -> (r: u8)
            requires x <= 100,
            ensures r == x + 1,
        {
            if x > 100 {
                0
            } else {
                x + 1
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// Same shape with `threshold = 100`: the reporter must FAIL the run,
// because the spec domain can never reach the then-arm.
test_vcheck_one_file! {
    #[test] threshold_fails_on_spec_excluded_arm vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn bounded_incr_gated(x: u8) -> (r: u8)
            requires x <= 100,
            ensures r == x + 1,
        {
            if x > 100 {
                0
            } else {
                x + 1
            }
        }
    } => HarnessOutcome::FailsHarness
}

// match arms + a while loop: exact-valued match arms are reachable by
// the byte-level search (the generator draws the byte directly), and
// the loop's body-entry site needs any n >= 1.
test_vcheck_one_file! {
    #[test] match_and_loop_sites vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn classify(x: u8) -> (r: u8)
            ensures
                x == 0 ==> r == 0,
                x == 1 ==> r == 1,
                x >= 2 ==> r == 2,
        {
            match x {
                0 => 0,
                1 => 1,
                _ => 2,
            }
        }

        // Verus loop-spec clauses (invariant/decreases) are ghost;
        // the instrumenter strips them from the twin, so this also
        // pins "invariants don't break the instrumented build".
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn count_to(n: u8) -> (r: u8)
            ensures r == n,
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                i = i + 1;
            }
            i
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 2 }
}

// SPEC ABLATION: the threshold gates the SPEC-COVERED percentage — an
// arm only earns credit from executions at least one ensures clause
// ENGAGES on (its `==>` antecedent chain holds; a non-implication
// clause engages every execution). Here the `x >= 2` clause is ablated:
// inputs with x >= 2 still REACH the `_` arm, but no clause speaks
// about them, so the arm is unspecified — 2/3 covered, and a 100%
// threshold must fail.
test_vcheck_one_file! {
    #[test] spec_ablation_fails_threshold vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn classify_ablated(x: u8) -> (r: u8)
            ensures
                x == 0 ==> r == 0,
                x == 1 ==> r == 1,
        {
            match x {
                0 => 0,
                1 => 1,
                _ => 2,
            }
        }
    } => HarnessOutcome::FailsHarness
}

// Same ablated spec without a threshold: informational — the report
// lists the `_` arm as unspecified but the run passes.
test_vcheck_one_file! {
    #[test] spec_ablation_is_informational_without_threshold vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        fn classify_ablated_info(x: u8) -> (r: u8)
            ensures
                x == 0 ==> r == 0,
                x == 1 ==> r == 1,
        {
            match x {
                0 => 0,
                1 => 1,
                _ => 2,
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// SPEC-FN ANTECEDENT: engagement extraction must survive an antecedent
// that calls a user spec fn (the idiomatic way to write a rich
// precondition-of-a-clause; the engagement lowering routes it through
// the same exec_spec pipeline as the full clause). Informational —
// the engagement compiling and running is the point. (An INLINE
// quantified antecedent `(forall|i| ..) ==> Q` is not exercised here:
// that clause shape doesn't survive the quantifier lift in plain
// `#[vcheck]` today. Coverage engagement marks it unlowerable and reports
// reached arms as indeterminate; any configured threshold fails closed.)
test_vcheck_one_file! {
    #[test] spec_fn_antecedent_engagement vcheck_code! {
        spec fn is_empty_seq(s: Seq<u8>) -> bool {
            s.len() == 0
        }

        #[vcheck]
        #[vcheck_cov_fuzz]
        fn first_or_default(v: Vec<u8>) -> (r: u8)
            ensures
                is_empty_seq(v.deep_view()) ==> r == 0,
                v.len() > 0 ==> r == v[0],
        {
            if v.len() == 0 {
                0
            } else {
                v[0]
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// The full spec restores 100%: all three antecedents partition u8, so
// every reached arm is spec-covered (this is the `classify` shape from
// match_and_loop_sites, kept here as the ablation counterpart).
test_vcheck_one_file! {
    #[test] full_spec_covers_all_arms vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn classify_full(x: u8) -> (r: u8)
            ensures
                x == 0 ==> r == 0,
                x == 1 ==> r == 1,
                x >= 2 ==> r == 2,
        {
            match x {
                0 => 0,
                1 => 1,
                _ => 2,
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// `skip` mutes one target (recorded in the report, search not run)
// while the sibling still runs; a straight-line body is classified as
// branchless and remains informational without a threshold.
test_vcheck_one_file! {
    #[test] skip_and_straight_line vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(skip)]
        fn muted(x: u8) -> (r: u8)
            ensures r >= x,
        {
            if x > 5 { x } else { x + 1 }
        }

        #[vcheck]
        #[vcheck_cov_fuzz]
        fn straight_line(x: u8) -> (r: u16)
            ensures r == x as u16 + 7,
        {
            x as u16 + 7
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 2 }
}

// `#[vcheck_cov_fuzz]` on an assume_specification: the wrapper carries the
// target-path sentinel, so the target is classified EXTERNAL — no
// source-level twin exists (the implementation is std's), the report
// renders an annotated row instead of a bogus "no branch sites", and
// the run stays informational. The wrapper's regular harness still
// checks the assumed contract against the real std behavior.
test_vcheck_one_file! {
    #[test] assume_spec_target_is_external vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        pub assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
            ensures
                r.is_some() ==> r.unwrap() == x + y,
                r.is_none() ==> x + y > u32::MAX,
        ;
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// A threshold on an unmeasured external target must FAIL the report —
// a requested coverage gate must not vacuously pass just because the
// implementation lives outside the crate.
test_vcheck_one_file! {
    #[test] assume_spec_threshold_fails_unmeasured vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 90)]
        pub assume_specification [ u32::checked_mul ](x: u32, y: u32) -> (r: Option<u32>)
            ensures
                r.is_some() ==> r.unwrap() == x * y,
        ;
    } => HarnessOutcome::FailsHarness
}

// End-to-end external-coverage measurement (dependency-crate tier):
// the assume_specification targets a LOCAL dependency crate
// (covext_dep, materialized by the scaffold). Orchestration first records
// engaged inputs, then rebuilds the dependency with nightly branch
// instrumentation (without build-std) and replays one exact target profile
// plus one profile per ensures clause. `threshold = 100` passes only when
// true LLVM branch-arm evidence exists and both arms are covered. Skips when
// llvm-tools is absent.
test_covext_one_file! {
    #[test] external_dep_measured_via_side_profile vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        pub assume_specification [ covext_dep::classify ](x: u8) -> (r: u8)
            ensures
                x < 128 ==> r == 1,
                x >= 128 ==> r == 2,
        ;
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// External SPEC ABLATION: the engagement recorder keeps exact per-clause
// input masks. With the `x >= 128` clause ablated, replay only executes
// covext_dep::classify on x < 128, so one true LLVM branch arm stays unhit
// and the 100% branch threshold must fail.
test_covext_one_file! {
    #[test] external_dep_spec_ablation_fails_threshold vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        pub assume_specification [ covext_dep::classify ](x: u8) -> (r: u8)
            ensures
                x < 128 ==> r == 1,
        ;
    } => HarnessOutcome::FailsHarness
}

// RESULT-DEPENDENT antecedents, full spec: `r == 1 ==> …` can only be
// decided AFTER the call, which the engagement recorder does exactly
// (its uninstrumented calls do not pollute side profiles). Both clauses
// engage their halves of the domain; aggregate replay covers both true
// branch arms, and each isolated clause profile covers its own arm.
test_covext_one_file! {
    #[test] external_result_dependent_full_spec_passes vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        pub assume_specification [ covext_dep::classify ](x: u8) -> (r: u8)
            ensures
                r == 1 ==> x < 128,
                r == 2 ==> x >= 128,
        ;
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// RESULT-DEPENDENT antecedent, ablated: with `r == 2 ==> …` commented
// out, only executions returning 1 (x < 128) engage the remaining
// clause; exact replay never drives x >= 128 through the instrumented
// dependency, one true branch arm stays unhit, and the threshold fails.
test_covext_one_file! {
    #[test] external_result_dependent_ablation_fails vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        pub assume_specification [ covext_dep::classify ](x: u8) -> (r: u8)
            ensures
                r == 1 ==> x < 128,
        ;
    } => HarnessOutcome::FailsHarness
}

// std/core tier: needs nightly + rust-src (`-Z build-std`) and a
// ~10-minute first build, so it is `#[ignore]`d — run explicitly with
// `cargo test -p verus_spec_check_test --test cov_fuzz -- --ignored`. The
// wrapper samples the full u32 domain, so both checked_add arms
// (overflow and not) are reached with certainty at 256 cases.
test_covext_one_file! {
    #[test]
    #[ignore = "std-tier external coverage: needs nightly + rust-src and a long first build"]
    external_std_target_measured_via_build_std vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        pub assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
            ensures
                r.is_some() ==> r.unwrap() == x + y,
                r.is_none() ==> x + y > u32::MAX,
        ;
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// Impl-method target (audit gap: classify captures methods, but every
// case above is a free fn). Exercises the method twin lowering
// (`self` -> `self_value` positional param) and the bolero generator
// path for a sampled user type inside the coverage runner.
test_vcheck_one_file! {
    #[test] impl_method_target vcheck_code! {
        pub struct Counter {
            pub v: u8,
        }

        impl Counter {
            #[vcheck]
            #[vcheck_cov_fuzz(threshold = 100)]
            pub fn describe(&self) -> (r: u8)
                ensures
                    self.v == 0 ==> r == 0,
                    self.v > 0 ==> r == 1,
            {
                if self.v == 0 {
                    0
                } else {
                    1
                }
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 1 }
}

// Generated coverage symbols and result keys use registration IDs rather
// than bare function names. A free function and method with the same name in
// one expansion must therefore compile and report independently.
test_vcheck_one_file! {
    #[test] same_named_targets_do_not_collide vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 100)]
        fn step(x: u8) -> (r: u8)
            ensures x == 0 ==> r == 0, x > 0 ==> r == 1,
        {
            if x == 0 { 0 } else { 1 }
        }

        pub struct Counter { pub value: u8 }

        impl Counter {
            #[vcheck]
            #[vcheck_cov_fuzz(threshold = 100)]
            pub fn step(&self) -> (r: u8)
                ensures self.value == 0 ==> r == 0, self.value > 0 ==> r == 1,
            {
                if self.value == 0 { 0 } else { 1 }
            }
        }
    } => HarnessOutcome::PassWithCovFuzzReport { harnesses: 2 }
}

// Coverage gates are fail-closed: malformed options must stop compilation
// instead of silently falling back to an informational report.
test_vcheck_one_file! {
    #[test] cov_fuzz_unknown_option_is_compile_error vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(unknown)]
        fn malformed_unknown(x: u8) -> (r: u8)
            ensures r == x,
        {
            x
        }
    } => HarnessOutcome::FailsBuildWith {
        needle: "unrecognized vcheck_cov_fuzz option `unknown`",
    }
}

test_vcheck_one_file! {
    #[test] cov_fuzz_threshold_over_100_is_compile_error vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz(threshold = 101)]
        fn malformed_threshold(x: u8) -> (r: u8)
            ensures r == x,
        {
            x
        }
    } => HarnessOutcome::FailsBuildWith {
        needle: "vcheck_cov_fuzz threshold must be 0..=100",
    }
}

test_vcheck_one_file! {
    #[test] cov_fuzz_name_value_is_compile_error vcheck_code! {
        pub struct Counter { pub value: u8 }

        impl Counter {
            #[vcheck]
            #[vcheck_cov_fuzz = "required"]
            pub fn malformed_name_value(&self) -> (r: u8)
                ensures r == self.value,
            {
                self.value
            }
        }
    } => HarnessOutcome::FailsBuildWith {
        needle: "expected #[vcheck_cov_fuzz(...)]",
    }
}
