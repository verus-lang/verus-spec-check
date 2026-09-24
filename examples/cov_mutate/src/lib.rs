//! `#[vcheck_cov_mutate]` mutation-coverage demo. Each marked fn produces
//! a coverage report comparing the body's mutants against the
//! `ensures` clause: a "killed" mutant means the contract caught the
//! mutation; a "survivor" means the spec missed it.

use verus_spec_check::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Pair of strong/weak ensures so survivors show up in the report.
// ---------------------------------------------------------------------

#[vcheck]
#[vcheck_cov_mutate]
fn strong_double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == x * 2,
{
    x + x
}

#[vcheck]
#[vcheck_cov_mutate]
fn weak_double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    // Looser ensures:
    ensures r >= x,
{
    x + x
}

// Two more strong/weak pairs over different shapes.

#[vcheck]
#[vcheck_cov_mutate]
fn triple_sum_strong(a: u8, b: u8, c: u8) -> (r: u32)
    ensures r == a as u32 + b as u32 + c as u32,
{
    a as u32 + b as u32 + c as u32
}

#[vcheck]
#[vcheck_cov_mutate]
fn triple_sum_weak(a: u8, b: u8, c: u8) -> (r: u32)
    ensures r <= 3 * 255u32,
{
    a as u32 + b as u32 + c as u32
}

#[vcheck]
#[vcheck_cov_mutate]
fn pack_u16(hi: u8, lo: u8) -> (r: u16)
    ensures r == ((hi as u16) * 256u16 + (lo as u16)) as u16,
{
    (hi as u16) * 256 + (lo as u16)
}

// #[vcheck]
#[vcheck_cov_mutate]
fn signed_double(x: i32) -> (r: i32)
    requires
        x >= -(i32::MAX / 2),
        x <= i32::MAX / 2,
    ensures r == x * 2,
{
    x + x
}

}
