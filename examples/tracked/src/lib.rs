use verus_spec_check::*;
use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

verus! {

/// Certified read through a shared permission. The harness checks 
/// the returned value against the sampled model --
/// the "directly observable" row of the clause taxonomy.
#[vcheck]
pub fn read_through(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (v: u32)
    requires
        perm.pptr() == ptr,
        perm.is_init(),
    ensures
        v == perm.value(),
{
    *ptr.borrow(Tracked(perm))
}

/// Same shape with a value-constrained precondition and contract
/// arithmetic: exercises `perm.value()` in `requires` (model-filtered
/// sampling) and in an `ensures` expression.
#[vcheck]
pub fn read_plus_one(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (v: u32)
    requires
        perm.pptr() == ptr,
        perm.is_init(),
        perm.value() < 1000,
    ensures
        v == perm.value() + 1,
{
    *ptr.borrow(Tracked(perm)) + 1
}

/// `final(perm).is_init()` is an observation directive; 
/// `final(perm).value() == v` is asserted via
/// the certified read-back. Also proves the raw-tier materializer's
/// `::vstd::` paths resolve outside vstd itself.
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
