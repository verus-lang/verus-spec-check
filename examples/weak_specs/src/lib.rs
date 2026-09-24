//! Mutation-coverage experiment for the weak-contract findings in vstd.
//!
//! For each finding, parallel implementations with identical bodies but
//! different contract styles. The cov_mutate engine reports per-fn kill
//! rates; LOOSE versions with surviving mutants are direct evidence
//! that the spec under-constrains the impl.

use verus_spec_check::*;
use vstd::prelude::*;

verus! {

// double_strong: contract pins down the exact value.
#[vcheck_cov_mutate]
#[vcheck]
pub exec fn double_strong(r: u32) -> (out: u32)
    requires r <= u32::MAX / 2,
    ensures out == r * 2,
{
    r * 2
}

// Mirrors the vstd `Result::map` style where the 
// contract is a predicate the closure satisfies, 
// not an exact value match.
#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn double_parity(r: u32) -> (out: u32)
    requires r <= u32::MAX / 2,
    ensures out % 2 == 0,
{
    r * 2
}

// double_vacuous: tautological contract. Mirrors `Result::map` when
// the closure has no `ensures` clause at all -- the spec permits any
// value of the right type.
#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn double_vacuous(r: u32) -> (out: u32)
    requires r <= u32::MAX / 2,
    ensures out >= 0,  // vacuous on u32
{
    r * 2
}

// vstd's `<u32 as PartialEq>::eq` has no direct ensures clause -- the
// meaning lives in the `PartialEqSpecImpl` trait extension. vcheck only
// sees the assume_specification's ensures, which is empty.

#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn eq_vacuous(x: u32, y: u32) -> (b: bool)
    ensures b || !b,  // tautology
{
    x == y
}

#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn eq_tight(x: u32, y: u32) -> (b: bool)
    ensures b == (x == y),
{
    x == y
}

// vstd's `Vec::index` uses `exists|s: &[T]| ...` to bridge to slice
// indexing. The harness's `prop_assert!` rewriter doesn't handle
// existentials inside ensures, so we can't directly probe the
// existential form. Instead we contrast a "matches some element"
// form (loose, but expressible without `exists`) against direct
// indexing.

// loose_vec_first: contract says only "the result is a u32" (vacuous on
// the value). The structural analog of vstd's existential bridge: a
// statement that doesn't pin any specific index.
#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn vec_first_loose(vec: Vec<u32>) -> (out: u32)
    requires
        vec.len() >= 1,
    ensures
        // LOOSE: out is bounded to a "valid range." For u32 this is
        // vacuous (`out >= 0` is always true), but it mirrors the
        // structural fact that an existential without index-pinning
        // doesn't constrain the specific value we got back.
        out >= 0,
{
    vec[0]
}

#[vcheck_cov_mutate]
#[vcheck]
#[verifier::external_body]
pub exec fn vec_first_tight(vec: Vec<u32>) -> (out: u32)
    requires
        vec.len() >= 1,
    ensures
        // TIGHT: pin to index 0 specifically.
        out == vec[0 as int],
{
    vec[0]
}

} // verus!
