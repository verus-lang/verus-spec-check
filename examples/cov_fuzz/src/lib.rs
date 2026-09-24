//! `#[vcheck_cov_fuzz]` branch-coverage demo. 

use verus_spec_check::*;
use vstd::prelude::*;

verus! {

// Fully reachable! every arm is reachable from the 
// unconstrained input domain, so `threshold = 100`
// is a safe gate

#[vcheck]
#[vcheck_cov_fuzz(threshold = 100)]
fn abs_diff(a: u8, b: u8) -> (r: u8)
    ensures
        a >= b ==> true,
        a < b ==> r == b - a,
{
    if a >= b {
        a - b
    } else {
        b - a
    }
}

#[vcheck]
#[vcheck_cov_fuzz(threshold = 100)]
fn both_big(a: u8, b: u8) -> (r: bool)
    ensures r == (a > 10 && b > 10),
{
    if a > 10 && b > 10 {
        true
    } else {
        false
    }
}

#[vcheck]
#[vcheck_cov_fuzz]
fn bounded_incr(x: u8) -> (r: u8)
    requires x <= 100,
    ensures r == x + 1,
{
    if x > 100 {
        0
    } else {
        x + 1
    }
}

#[vcheck]
#[vcheck_cov_fuzz(threshold = 100)]
fn classify(x: u8) -> (r: u8)
    ensures
        x == 0 ==> r == 0,
        x == 1 ==> r == 1,
        x >= 2 ==> r == 2,
{
    match x {
        0 => 0,
        1 => 1,
        _ => 2,
    }
}

#[vcheck]
#[vcheck_cov_fuzz(threshold = 100)]
fn count_to(n: u8) -> (r: u8)
    ensures r == n,
{
    let mut i: u8 = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

// External target: how much of std's `checked_add` does the assumed
// spec's domain exercise? Measured via the instrumented side profile

#[vcheck]
#[vcheck_cov_fuzz(threshold = 100)]
pub assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        r.is_some() ==> r.unwrap() == x + y,
        // r.is_none() ==> x + y > u32::MAX,
;

}
