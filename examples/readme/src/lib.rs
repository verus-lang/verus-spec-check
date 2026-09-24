use verus_spec_check::*;
use vstd::prelude::*;

verus! {

#[vcheck]
fn safe_double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == x * 2,
{
    x + x
}

fn midpoint(a: u32, b: u32) -> (m: u32)
    requires a <= b,
{
    let m = a + (b - a) / 2;
    #[vcheck] assert(a <= m && m <= b);
    m
}

#[vcheck]
assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        r.is_some() ==> r.unwrap() == x + y,
        r.is_none() ==> x + y > u32::MAX,
;

}

fn main() {}
