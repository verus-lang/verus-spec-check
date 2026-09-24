mod common;
use common::*;

// Certified read through a shared permission.
// Checks the returned value against the sampled model.
fn read_through_snippet() -> String {
    vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;
        use vstd::simple_pptr::{PPtr, PointsTo};

        verus! {

        #[vcheck]
        pub fn read_through(
            ptr: PPtr<u32>,
            Tracked(perm): Tracked<&PointsTo<u32>>,
        ) -> (v: u32)
            requires
                perm.pptr() == ptr,
                perm.is_init(),
            ensures
                v == perm.value(),
        {
            *ptr.borrow(Tracked(perm))
        }

        } // verus!
    }
}

test_vcheck_one_file! {
    #[test] shared_perm_read read_through_snippet()
        => HarnessOutcome::Pass { harnesses: 1 }
}

test_verify_one_file! {
    #[test] verify_shared_perm_read read_through_snippet() => VerifyOutcome::Verifies
}

// exercises `perm.value()` in `requires` (model-filtered
// sampling) and in an `ensures` expression.
test_vcheck_one_file! {
    #[test] shared_perm_read_with_value_precondition vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;
        use vstd::simple_pptr::{PPtr, PointsTo};

        verus! {

        #[vcheck]
        pub fn read_plus_one(
            ptr: PPtr<u32>,
            Tracked(perm): Tracked<&PointsTo<u32>>,
        ) -> (v: u32)
            requires
                perm.pptr() == ptr,
                perm.is_init(),
                perm.value() < 1000,
            ensures
                v == perm.value() + 1,
        {
            *ptr.borrow(Tracked(perm)) + 1
        }

        } // verus!
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// `&mut` permission on the RAW tier (`*mut u32` + `raw_ptr::PointsTo`).
// `final(perm).is_init()` is an observation directive;
// `final(perm).value() == v` is asserted via the certified read-back.
// Also proves the raw-tier materializer's `::vstd::` paths resolve
// outside vstd itself.
test_vcheck_one_file! {
    #[test] raw_tier_mut_perm_write vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;

        verus! {

        #[vcheck]
        pub fn write_through(
            ptr: *mut u32,
            Tracked(perm): Tracked<&mut vstd::raw_ptr::PointsTo<u32>>,
            v: u32,
        )
            requires
                old(perm).ptr() == ptr,
            ensures
                final(perm).is_init(),
                final(perm).value() == v,
        {
            vstd::raw_ptr::ptr_mut_write(ptr, Tracked(perm), v)
        }

        } // verus!
    } => HarnessOutcome::Pass { harnesses: 1 }
}
