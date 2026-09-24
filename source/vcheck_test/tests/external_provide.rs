mod common;
use common::*;

fn provide_snippet() -> String {
    vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;

        // Block 1: a separate preprocessing pass exporting only a spec
        // fn. Same module, so the contract below can name it directly.
        verus! {

        pub open spec fn is_sorted(s: Seq<i64>) -> bool {
            forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
        }

        }

        verus! {

        // The trusted exec twin of the external spec fn. Ordinary exec
        // Rust over the lowered (&[i64]) form.
        external_vcheck_provide! {
            fn is_sorted(s: Seq<i64>) -> bool {
                let mut i = 0;
                while i + 1 < s.len() {
                    if s[i] > s[i + 1] {
                        return false;
                    }
                    i += 1;
                }
                true
            }
        }

        #[vcheck]
        #[verifier::external_body]
        pub fn is_input_sorted(s: &[i64]) -> (b: bool)
            ensures b == is_sorted(s.deep_view()),
        {
            let mut i = 0;
            while i + 1 < s.len() {
                if s[i] > s[i + 1] {
                    return false;
                }
                i += 1;
            }
            true
        }

        } // verus!
    }
}

test_vcheck_one_file! {
    #[test] external_spec_fn_via_provide provide_snippet()
        => HarnessOutcome::Pass { harnesses: 1 }
}

test_verify_one_file! {
    #[test] verify_external_spec_fn_via_provide provide_snippet()
        => VerifyOutcome::Verifies
}

// The provided companion is the ground truth, so a buggy body must be
// caught.
test_vcheck_one_file! {
    #[test] buggy_body_vs_external_companion_is_caught vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;

        verus! {

        pub open spec fn is_sorted(s: Seq<i64>) -> bool {
            forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
        }

        }

        verus! {

        external_vcheck_provide! {
            fn is_sorted(s: Seq<i64>) -> bool {
                let mut i = 0;
                while i + 1 < s.len() {
                    if s[i] > s[i + 1] {
                        return false;
                    }
                    i += 1;
                }
                true
            }
        }

        #[vcheck]
        #[verifier::external_body]
        pub fn is_input_sorted_buggy(s: &[i64]) -> (b: bool)
            ensures b == is_sorted(s.deep_view()),
        {
            s.len() < 2 || s[0] <= s[1] // BUG: first pair only
        }

        } // verus!
    } => HarnessOutcome::FailsHarness
}
