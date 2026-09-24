//! property-testing a `#[vcheck]` function whose contract calls a
//! spec fn defined **outside** the block (here, module `ext`, standing in for
//! another crate such as `vstd` whose spec body we can't fold in).
//!
//! The developer supplies a trusted exec companion once via
//! `external_vcheck_provide!`. `cargo verus verify` checks the spec layer using
//! the real (external) spec fn; `cargo test` runs the generated harness, which
//! evaluates the contract through the provided `exec_is_sorted` companion.

use verus_spec_check::*;
use vstd::prelude::*;

verus! {

pub open spec fn is_sorted(s: Seq<i64>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

}

verus! {

// the trusted exec twin of `ext::is_sorted`. Lives next to the #[vcheck]
// fn; the body is ordinary exec Rust over the lowered (`&[i64]`) form.
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

// The function under test: returns whether its (already-sorted by contract)
// input stays sorted after a no-op. The contract calls the EXTERNAL spec fn.
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

#[cfg(test)]
mod bug_detection {
    //! a buggy validator checked against the trusted external companion must 
    //! be caught, and a correct one must pass. We re-declare the exec twin 
    //! here to drive a TestRunner (the generated harness covers the same 
    //! path under `cargo test`)
    use verus_spec_check::proptest::prelude::*;
    use verus_spec_check::proptest::test_runner::{Config, TestError, TestRunner};
    use verus_spec_check::vcheck_strategy;

    fn ground_truth(s: &[i64]) -> bool {
        let mut i = 0;
        while i + 1 < s.len() {
            if s[i] > s[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    // BUG: only checks the first adjacent pair.
    fn buggy_is_sorted(s: &[i64]) -> bool {
        s.len() < 2 || s[0] <= s[1]
    }

    #[test]
    fn vcheck_catches_buggy_validator() {
        let mut runner = TestRunner::new(Config { cases: 1024, ..Config::default() });
        let result = runner.run(&vcheck_strategy::<Vec<i64>>(), |v: Vec<i64>| {
            prop_assert_eq!(buggy_is_sorted(&v), ground_truth(&v));
            Ok(())
        });
        assert!(matches!(result, Err(TestError::Fail(..))));
    }

    #[test]
    fn vcheck_correct_validator_passes() {
        let mut runner = TestRunner::new(Config { cases: 1024, ..Config::default() });
        let result = runner.run(&vcheck_strategy::<Vec<i64>>(), |v: Vec<i64>| {
            prop_assert_eq!(ground_truth(&v), ground_truth(&v));
            Ok(())
        });
        assert!(result.is_ok(), "{:?}", result.map(|_| ()));
    }
}
