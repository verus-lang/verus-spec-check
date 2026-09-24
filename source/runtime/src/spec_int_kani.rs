//! `SpecInt` under Kani -- an `i128` model of the spec-int lift.
//!
//! This file is the `cfg(kani)` twin of `spec_int.rs` (see `lib.rs`,
//! which `#[path]`-selects one of the two). Same public surface, same
//! Verus semantics for every operation — but backed by `i128` instead
//! of `num_bigint::BigInt`.
//!
//! ## Why not BigInt under Kani?
//!
//! Every contract expression the rewriter emits routes its arithmetic
//! and comparisons through this module. `BigInt` is a heap-allocated
//! `Vec<u64>` of digits, and each op walks those digits in
//! data-dependent loops. Concrete execution doesn't care — but CBMC
//! must *unwind* those loops symbolically, and with symbolic inputs
//! there is no bound to find: even `eq(r, add(a, b))` on `u16`s spins
//! the digit-comparison loop past any unwind limit. In practice every
//! `mode = "kani"` harness with any contract arithmetic timed out.
//! With `i128` the same expressions become flat bitvector terms, which
//! is CBMC's native currency.
//!
//! ## The modeling boundary
//!
//! `i128` is not `int`. The model is exact while every intermediate
//! spec value fits in `i128`; an intermediate that doesn't (e.g.
//! `u128::MAX + 1`, or `u64::MAX * u64::MAX`) **panics with a
//! modeling-range message**, which Kani reports as a failure. That is
//! deliberately fail-loud: a spurious *failure* you can read and
//! diagnose is acceptable, a silently wrong verification result is
//! not. Contracts whose spec arithmetic genuinely needs values beyond
//! `i128` (or `real` contracts, whose `BigRational` backing has the
//! same loop-explosion problem) are outside the Kani tier — run them
//! on the proptest/fuzz tiers instead.
//!
//! Casts, division-by-zero, and shift-count checks keep the exact
//! panic message shapes of the BigInt implementation so failure
//! reports read identically across tiers.

use num_bigint::BigInt;

/// The Kani-tier math-integer model: plain `i128`. See the module docs
/// for the boundary; the BigInt-backed implementation in `spec_int.rs`
/// is the source of truth for the intended (unbounded) semantics.
pub type SpecInt = i128;

const RANGE_MSG: &str =
    "verus_spec_check: spec-int arithmetic exceeded the i128 modeling range under kani \
     (the kani tier models Verus `int` in i128; see spec_int_kani.rs)";

/// Trait-alias for "anything that can be converted to a `SpecInt`".
/// Mirrors `spec_int::IntoSpecInt`; conversions that cannot be exact in
/// `i128` (`u128` above `i128::MAX`, wide `BigInt`s) panic with the
/// modeling-range message.
pub trait IntoSpecInt {
    fn into_spec_int(self) -> SpecInt;
}

macro_rules! impl_into_spec_int {
    ($($t:ty),* $(,)?) => {
        $(
            impl IntoSpecInt for $t {
                #[inline]
                fn into_spec_int(self) -> SpecInt {
                    self as i128
                }
            }
        )*
    };
}

impl_into_spec_int!(u8, u16, u32, u64, usize, i8, i16, i32, i64, i128, isize);

impl IntoSpecInt for u128 {
    #[inline]
    fn into_spec_int(self) -> SpecInt {
        i128::try_from(self).unwrap_or_else(|_| panic!("{}", RANGE_MSG))
    }
}

impl IntoSpecInt for &SpecInt {
    #[inline]
    fn into_spec_int(self) -> SpecInt {
        *self
    }
}

/// `BigInt` bridge, so code that mixes the real lowering (whose `floor`
/// returns `BigInt`) with spec-int ops still COMPILES under a kani
/// build. Analysis of such a harness still explodes on the rational
/// backing — `real` contracts are outside the kani tier — but `cargo
/// kani --tests` compiles the whole test crate, so an unrelated
/// `real`-using harness must not break the build of the one being
/// checked.
impl IntoSpecInt for BigInt {
    #[inline]
    fn into_spec_int(self) -> SpecInt {
        use num_traits::ToPrimitive;
        self.to_i128().unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }
}

/// Explicit lift to `SpecInt` (`<expr> as int` / `as nat`).
#[inline]
pub fn lift(x: impl IntoSpecInt) -> SpecInt {
    x.into_spec_int()
}

/// Default `realize` for `#[vcheck_view]` opaque types (Display-decimal
/// parse). Values past `i128` hit the modeling boundary.
#[inline]
pub fn from_display<T: core::fmt::Display + ?Sized>(t: &T) -> SpecInt {
    let s = t.to_string();
    s.parse::<SpecInt>().unwrap_or_else(|_| {
        panic!(
            "verus_spec_check: #[vcheck_view] default `realize` failed: `{}` is not a decimal \
             integer in the i128 modeling range (kani tier). Supply an explicit \
             `realize = <fn>` for this type.",
            s
        )
    })
}

// ---------------------------------------------------------------------------
// Arithmetic — checked, fail-loud at the modeling boundary.

#[inline]
pub fn add(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int()
        .checked_add(b.into_spec_int())
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

#[inline]
pub fn sub(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int()
        .checked_sub(b.into_spec_int())
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

#[inline]
pub fn mul(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int()
        .checked_mul(b.into_spec_int())
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

/// Euclidean division, matching Verus spec `/` (and the BigInt impl).
#[inline]
pub fn div(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    let b = b.into_spec_int();
    if b == 0 {
        panic!("__vcheck_int::div: division by zero in contract evaluation");
    }
    a.into_spec_int()
        .checked_div_euclid(b)
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

/// Euclidean remainder, matching Verus spec `%` (and the BigInt impl).
#[inline]
pub fn rem(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    let b = b.into_spec_int();
    if b == 0 {
        panic!("__vcheck_int::rem: modulo by zero in contract evaluation");
    }
    a.into_spec_int()
        .checked_rem_euclid(b)
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

#[inline]
pub fn neg(a: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int()
        .checked_neg()
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

// ---------------------------------------------------------------------------
// Comparisons — direct on i128.

#[inline]
pub fn lt(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() < b.into_spec_int()
}

#[inline]
pub fn le(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() <= b.into_spec_int()
}

#[inline]
pub fn gt(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() > b.into_spec_int()
}

#[inline]
pub fn ge(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() >= b.into_spec_int()
}

#[inline]
pub fn eq(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() == b.into_spec_int()
}

#[inline]
pub fn ne(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
    a.into_spec_int() != b.into_spec_int()
}

// ---------------------------------------------------------------------------
// Narrowing casts — same out-of-range panic contract as the BigInt impl.

macro_rules! to_int {
    ($name:ident, $t:ty) => {
        #[inline]
        pub fn $name(x: impl IntoSpecInt) -> $t {
            let x = x.into_spec_int();
            <$t>::try_from(x).unwrap_or_else(|_| {
                panic!(
                    "__vcheck_int::{}: value out of range for {}: {}",
                    stringify!($name),
                    stringify!($t),
                    x,
                )
            })
        }
    };
}

to_int!(to_u8, u8);
to_int!(to_u16, u16);
to_int!(to_u32, u32);
to_int!(to_u64, u64);
to_int!(to_u128, u128);
to_int!(to_usize, usize);
to_int!(to_i8, i8);
to_int!(to_i16, i16);
to_int!(to_i32, i32);
to_int!(to_i64, i64);
to_int!(to_i128, i128);
to_int!(to_isize, isize);

// ---------------------------------------------------------------------------
// Shifts. Verus spec `x << n` is `x * 2^n` in int; model it as checked
// multiplication so shifted-out bits hit the modeling boundary instead
// of being silently dropped (i128's native `<<` truncates).

#[inline]
pub fn shl(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
    let a = a.into_spec_int();
    let n = n.into_spec_int();
    let n = u32::try_from(n)
        .unwrap_or_else(|_| panic!("__vcheck_int::shl: shift count out of range for u32: {}", n));
    if n >= 127 {
        // 2^127 is already unrepresentable; only a == 0 survives.
        if a == 0 {
            return 0;
        }
        panic!("{}", RANGE_MSG);
    }
    a.checked_mul(1i128 << n)
        .unwrap_or_else(|| panic!("{}", RANGE_MSG))
}

/// `x >> n` in spec semantics is floor division by `2^n`; arithmetic
/// shift right on `i128` computes exactly that for in-range counts, and
/// counts >= 127 saturate to the sign (0 or -1), matching BigInt.
#[inline]
pub fn shr(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
    let a = a.into_spec_int();
    let n = n.into_spec_int();
    let n = u32::try_from(n)
        .unwrap_or_else(|_| panic!("__vcheck_int::shr: shift count out of range for u32: {}", n));
    if n >= 127 {
        return if a < 0 { -1 } else { 0 };
    }
    a >> n
}

// ---------------------------------------------------------------------------
// Bitwise -- two's-complement on i128 matches BigInt's semantics for all
// in-model values.

#[inline]
pub fn bitand(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() & b.into_spec_int()
}

#[inline]
pub fn bitor(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() | b.into_spec_int()
}

#[inline]
pub fn bitxor(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() ^ b.into_spec_int()
}
