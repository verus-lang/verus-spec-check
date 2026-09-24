//! Demo for `#[vcheck]` on inline asserts.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Path-form: catches a body bug that the ensures clause doesn't pin
// down. `safe_div`'s ensures clause `r == spec_safe_div(num, den)` is
// strong, but the inline assert is a useful intermediate sanity check.
// ---------------------------------------------------------------------------

pub open spec fn spec_safe_div(num: u32, den: u32) -> u32 {
    if den != 0u32 { num / den } else { 0u32 }
}

#[vcheck]
#[verifier::external_body]
pub exec fn safe_div(num: u32, den: u32) -> (r: u32)
    ensures r == spec_safe_div(num, den),
{
    let result = if den != 0u32 { num / den } else { 0u32 };
    // Path-form inline assert: surface a body invariant. Captures
    // `result`, `num`, `den` from the enclosing scope.
    #[vcheck] assert(den == 0u32 || result <= num);
    result
}

// ---------------------------------------------------------------------------
// Forall-form on its own.
// ---------------------------------------------------------------------------

#[vcheck]
#[verifier::external_body]
pub exec fn double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == (x + x) as u32,
{
    let r = x + x;
    // Forall-form: sample `w` directly. Predicate must compile as exec.
    #[vcheck] assert forall |w: u32|
        w <= u32::MAX / 2u32 implies w + w == 2u32 * w by { };
    r
}

// ---------------------------------------------------------------------------
// Combined: path-form + forall-form in the same fn. Each gets its own
// `#[test]` harness independently.
// ---------------------------------------------------------------------------

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

}
