mod common;
use common::*;

// Shared snippet: harness gate + verify gate at the bottom of this file.
fn path_form_snippet() -> String {
    vcheck_code! {
        pub open spec fn spec_safe_div(num: u32, den: u32) -> u32 {
            if den != 0u32 { num / den } else { 0u32 }
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn safe_div(num: u32, den: u32) -> (r: u32)
            ensures r == spec_safe_div(num, den),
        {
            let result = if den != 0u32 { num / den } else { 0u32 };
            #[vcheck] assert(den == 0u32 || result <= num);
            result
        }
    }
}

test_vcheck_one_file! {
    #[test] path_form_assert path_form_snippet()
        => HarnessOutcome::Pass { harnesses: 2 }
}

test_verify_one_file! {
    #[test] verify_path_form_assert path_form_snippet() => VerifyOutcome::Verifies
}

// Forall-form on its own: contract harness + sampled-predicate harness.
test_vcheck_one_file! {
    #[test] forall_form_assert vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn double(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == (x + x) as u32,
        {
            let r = x + x;
            #[vcheck] assert forall |w: u32|
                w <= u32::MAX / 2u32 implies w + w == 2u32 * w by { };
            r
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

// Both forms in one fn: each assert gets an independent harness.
test_vcheck_one_file! {
    #[test] both_forms_in_one_fn vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn triple(x: u32) -> (r: u32)
            requires x <= u32::MAX / 3,
            ensures r == (x + x + x) as u32,
        {
            let r = x + x + x;
            #[vcheck] assert(r >= x);
            #[vcheck] assert forall |w: u32|
                w <= u32::MAX / 3u32 implies w + w + w == 3u32 * w by { };
            r
        }
    } => HarnessOutcome::Pass { harnesses: 3 }
}

// A path-form assert that is actually false must be caught. Guards
// against the inline-assert harness degrading into a no-op (which the
// all-passing cases above could not distinguish).
test_vcheck_one_file! {
    #[test] false_path_assert_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn half(x: u32) -> (r: u32)
            ensures r == x / 2u32,
        {
            let result = x / 2u32;
            // FALSE for any sampled x >= 2.
            #[vcheck] assert(result == x);
            result
        }
    } => HarnessOutcome::FailsHarness
}
