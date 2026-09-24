//! vcheck demo for `&mut <T>` parameters and `final(...)`/`old(...)` contracts.
//!
//! Verus requires postcondition references to `&mut` params to be
//! disambiguated with either `old(<id>)` or `final(<id>)`, so the demos
//! here use that syntax explicitly.

use vstd::prelude::*;
use verus_spec_check::*;

verus! {

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: append a single element.
// ---------------------------------------------------------------------------

#[vcheck(T = u32)]
#[verifier::external_body]
pub exec fn vec_push<T>(v: &mut Vec<T>, x: T)
    ensures
        final(v)@ == old(v)@.push(x),
{
    v.push(x);
}

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: in-place set at an index.
// ---------------------------------------------------------------------------

#[vcheck(T = u32)]
#[verifier::external_body]
pub exec fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires
        i < old(v)@.len(),
    ensures
        final(v)@ == old(v)@.update(i as int, x),
{
    v[i] = x;
}

// ---------------------------------------------------------------------------
// `&mut String`: append `&str`.
// ---------------------------------------------------------------------------

#[vcheck]
#[verifier::external_body]
pub exec fn string_append(s: &mut String, t: &str)
    ensures
        final(s)@ == old(s)@ + t@,
{
    s.push_str(t);
}

// ---------------------------------------------------------------------------
// `&mut Vec<T>`: clear.
// ---------------------------------------------------------------------------

#[vcheck(T = u32)]
#[verifier::external_body]
pub exec fn vec_clear<T>(v: &mut Vec<T>)
    ensures
        final(v)@.len() == 0,
{
    v.clear();
}

}
