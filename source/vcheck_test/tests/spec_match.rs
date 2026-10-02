mod common;
use common::*;

test_vcheck_one_file! {
    #[test]
    guard_false_falls_through vcheck_code! {
        pub open spec fn is_positive(x: i8) -> bool {
            match x {
                n if n > 0 => true,
                _ => false,
            }
        }

        #[vcheck]
        #[verifier::external_body]
        pub fn always_positive(x: i8) -> (r: bool)
            ensures r == is_positive(x),
        {
            true
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test]
    guard_on_binding vcheck_code! {
        pub open spec fn has_positive(o: Option<i8>) -> bool {
            match o {
                Some(v) if v > 0 => true,
                Some(_) => false,
                None => false,
            }
        }

        #[vcheck]
        #[verifier::external_body]
        pub fn check_positive(o: Option<i8>) -> (r: bool)
            ensures r == has_positive(o),
        {
            match o {
                Some(v) => v > 0,
                None => false,
            }
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}
