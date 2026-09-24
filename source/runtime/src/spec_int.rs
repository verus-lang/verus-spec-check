//! `SpecInt` -- a faithful runtime mirror of Verus's spec `int` type.
//!
//! Verus's contract expressions evaluate in unbounded mathematical
//! integers (`int`/`nat`). At verification time those expressions never
//! overflow; the only narrowing happens at explicit `as $T` casts and
//! at the boundary into the runtime call. To preserve that semantics
//! when we evaluate the same contracts at *runtime* (under proptest),
//! the engine routes every arithmetic op and comparison appearing in a
//! contract through this module, so that e.g.
//!
//! ```text
//!     // Verus spec source:
//!     if x + y > <u8>::MAX { None } else { Some((x + y) as u8) }
//! ```
//!
//! becomes (after rewriting):
//!
//! ```text
//!     if ::verus_spec_check::__vcheck_int::gt(
//!            ::verus_spec_check::__vcheck_int::add(x, y),
//!            <u8>::MAX,
//!        ) {
//!         None
//!     } else {
//!         Some(::verus_spec_check::__vcheck_int::to_u8(
//!             ::verus_spec_check::__vcheck_int::add(x, y),
//!         ))
//!     }
//! ```
//!
//! For `x = 80u8, y = 176u8`, the bare `x + y` would panic in Rust
//! (`attempt to add with overflow`). The lifted form evaluates as
//! `256i32`-as-`BigInt > 255` -> `true` -> returns `None`, matching the
//! Verus spec exactly.
//!
//! ## Why BigInt?
//!
//! For `u128 + u128` the result genuinely doesn't fit in any fixed-
//! width type. We could special-case the common widths, but a
//! `BigInt`-backed implementation is uniform and faithful to the spec
//! semantics. Property tests run for ~1k iterations per test; the
//! allocation cost is negligible.
//!
//! ## Casts
//!
//! `as $T` on a `SpecInt` becomes `to_$T(_)` which *checks* the value
//! fits. This intentionally panics on out-of-range — matching Verus's
//! verification obligation that the cast value is in-range. A panic
//! here is a real spec bug: the contract claimed a narrowed value but
//! the computation produced an out-of-range result.

use num_bigint::BigInt;

/// Alias over `num_bigint::BigInt`
pub type SpecInt = BigInt;

/// Trait-alias for "anything that can be converted to a `SpecInt`".
/// All primitive integer types (and `SpecInt` itself) impl this via the
/// blanket `From<T> for BigInt` impls in `num_bigint`. Using this trait
/// in the helper signatures lets us write `add(2u8, 250u8)` directly —
/// the conversion happens at the call site.
pub trait IntoSpecInt {
    fn into_spec_int(self) -> SpecInt;
}

macro_rules! impl_into_spec_int {
    ($($t:ty),* $(,)?) => {
        $(
            impl IntoSpecInt for $t {
                #[inline]
                fn into_spec_int(self) -> SpecInt {
                    SpecInt::from(self)
                }
            }
        )*
    };
}

impl_into_spec_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl IntoSpecInt for SpecInt {
    #[inline]
    fn into_spec_int(self) -> SpecInt {
        self
    }
}

impl IntoSpecInt for &SpecInt {
    #[inline]
    fn into_spec_int(self) -> SpecInt {
        self.clone()
    }
}

/// Explicit lift to `SpecInt`. Used by the contract rewriter for
/// `<expr> as int` / `<expr> as nat`: those are spec-only casts in
/// Verus whose runtime equivalent is "promote this primitive into the
/// math-int domain". Once promoted, downstream arithmetic stays in
/// `SpecInt` until an explicit narrowing cast.
#[inline]
pub fn lift(x: impl IntoSpecInt) -> SpecInt {
    x.into_spec_int()
}

/// Default `realize` for `#[vcheck_view]` opaque types: interpret a value's
/// `Display` (decimal) as a `SpecInt`. Works for integer-like opaque types
/// (`UBig`, `IBig`, ...) whose `Display` is their mathematical value. Panics
/// with a clear message if the display isn't a valid integer — a signal that
/// the type needs an explicit `realize` fn.
#[inline]
pub fn from_display<T: core::fmt::Display + ?Sized>(t: &T) -> SpecInt {
    let s = t.to_string();
    s.parse::<SpecInt>().unwrap_or_else(|_| {
        panic!(
            "verus_spec_check: #[vcheck_view] default `realize` failed: `{}` is not a decimal \
             integer. Supply an explicit `realize = <fn>` for this type.",
            s
        )
    })
}

// ---------------------------------------------------------------------------
// Arithmetic
//
// Each op takes any two `IntoSpecInt` operands and returns a `SpecInt`.
// Allocations are unavoidable for true unbounded arithmetic; the cost
// is bounded by proptest iteration count (typically 256-1024 per test).

#[inline]
pub fn add(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() + b.into_spec_int()
}

#[inline]
pub fn sub(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() - b.into_spec_int()
}

#[inline]
pub fn mul(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    a.into_spec_int() * b.into_spec_int()
}

/// Verus's spec semantics for `/` and `%` on integer types is
/// **Euclidean** division (always non-negative remainder), not Rust's
/// truncated division. `num_bigint::BigInt`'s native `/` and `%`
/// operators perform truncated division, so we explicitly call
/// `num_integer::Integer::div_euclid` / `mod_floor` to match Verus.
///
/// This matters for negative operands: `(-1i8).div_euclid(-2i8)` is
/// `1` (Euclidean), whereas truncated `-1 / -2 = 0`. The same kind of
/// mismatch shows up in `i8::checked_div_euclid`'s spec, which writes
/// `lhs / rhs` and expects the result to be the Euclidean quotient.
#[inline]
pub fn div(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    use num_traits::Euclid;
    let b = b.into_spec_int();
    if b.sign() == num_bigint::Sign::NoSign {
        panic!("__vcheck_int::div: division by zero in contract evaluation");
    }
    a.into_spec_int().div_euclid(&b)
}

#[inline]
pub fn rem(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
    use num_traits::Euclid;
    let b = b.into_spec_int();
    if b.sign() == num_bigint::Sign::NoSign {
        panic!("__vcheck_int::rem: modulo by zero in contract evaluation");
    }
    a.into_spec_int().rem_euclid(&b)
}

#[inline]
pub fn neg(a: impl IntoSpecInt) -> SpecInt {
    -a.into_spec_int()
}

// ---------------------------------------------------------------------------
// Comparisons
//
// Each op takes any two `IntoSpecInt` operands and returns a `bool`.
// These are used by the rewriter to lift *any* comparison whose
// arguments may have been promoted to `SpecInt` (because a sibling
// subexpression performed arithmetic that overflowed the primitive
// width). Comparing `BigInt::from(256) > BigInt::from(255)` works
// naturally.

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
// Narrowing casts
//
// `(expr) as $T` on a `SpecInt`-typed expression checks that the value
// fits in `$T`. Out-of-range is a *spec bug* by construction: the Verus
// source claimed `(x + y) as u8` is in-range, but the runtime
// evaluation found it isn't. Panicking here turns into a property-test
// failure with a clear message.

macro_rules! to_int {
    ($name:ident, $t:ty, $to_fn:ident) => {
        #[inline]
        pub fn $name(x: impl IntoSpecInt) -> $t {
            use num_traits::ToPrimitive;
            let x = x.into_spec_int();
            x.$to_fn().unwrap_or_else(|| {
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

to_int!(to_u8, u8, to_u8);
to_int!(to_u16, u16, to_u16);
to_int!(to_u32, u32, to_u32);
to_int!(to_u64, u64, to_u64);
to_int!(to_u128, u128, to_u128);
to_int!(to_usize, usize, to_usize);
to_int!(to_i8, i8, to_i8);
to_int!(to_i16, i16, to_i16);
to_int!(to_i32, i32, to_i32);
to_int!(to_i64, i64, to_i64);
to_int!(to_i128, i128, to_i128);
to_int!(to_isize, isize, to_isize);

// ---------------------------------------------------------------------------
// Shifts.
//
// Verus's spec semantics for `x << n` is multiplication by `2^n` in
// `int`. For shifts that would overflow the runtime type, the spec
// produces a value that — when narrowed — yields the wrapped result.
// Matching that exactly here: shift in BigInt, expect a later `as $T`
// to truncate.

#[inline]
pub fn shl(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
    use num_traits::ToPrimitive;
    let a = a.into_spec_int();
    let n = n.into_spec_int();
    let n = n
        .to_u32()
        .unwrap_or_else(|| panic!("__vcheck_int::shl: shift count out of range for u32: {}", n));
    a << n
}

#[inline]
pub fn shr(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
    use num_traits::ToPrimitive;
    let a = a.into_spec_int();
    let n = n.into_spec_int();
    let n = n
        .to_u32()
        .unwrap_or_else(|| panic!("__vcheck_int::shr: shift count out of range for u32: {}", n));
    a >> n
}

// ---------------------------------------------------------------------------
// Bitwise.
//
// Verus's spec bitwise ops on `int` use two's-complement semantics on
// non-negative integers; for negative values the answer depends on the
// width context. `num_bigint` implements `&`/`|`/`^` directly. Like
// shifts, the result is `SpecInt` and a later `as $T` narrows.

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_widens_past_u8() {
        // 80u8 + 176u8 overflows u8 in plain Rust; here we get 256.
        assert!(gt(add(80u8, 176u8), 255u8));
        assert!(eq(add(80u8, 176u8), 256u16));
    }

    #[test]
    fn add_widens_past_u128() {
        // u128::MAX + u128::MAX = 2 * u128::MAX, well past i128 range.
        let max = SpecInt::from(u128::MAX);
        let sum = add(&max, &max);
        assert!(gt(sum, u128::MAX));
    }

    #[test]
    fn narrow_in_range() {
        // (100 + 100) as u8 = 200, fits in u8.
        assert_eq!(to_u8(add(100u8, 100u8)), 200u8);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn narrow_out_of_range_panics() {
        // (200 + 200) as u8 = 400, doesn't fit in u8 -> panic.
        let _ = to_u8(add(200u8, 200u8));
    }

    #[test]
    fn sub_goes_negative() {
        assert!(lt(sub(5u8, 10u8), 0i32));
        assert!(eq(sub(5u8, 10u8), -5i32));
    }

    #[test]
    fn mixed_signed_unsigned() {
        // x: u8 + y: i8 where the sum is negative -> SpecInt < 0.
        assert!(lt(add(2u8, -10i8), 0i32));
    }
}

// Differential tests for the int lift
//
// Oracle strategy:
//   - For arithmetic with operands in `i64` range: use `i128`
//     widening, which has well-defined wraparound at known limits and
//     covers the full range of binary operations on `i64` inputs.
//   - For Euclidean div/rem: use Rust's built-in `i64::div_euclid` /
//     `rem_euclid` (stable since 1.38, well-tested) as oracle. This
//     is a *different code path* than `num-traits::Euclid` for BigInt,
//     so it independently checks our lift.
//   - For narrowing: explicit range-check + `as $T` cast.
//   - For comparisons: plain `<`/`<=`/etc. on `i128` widening.
//
// We use `prop_oneof!` to bias inputs toward edges (`MIN`, `MAX`, `0`,
// `-1`, `1`) so signed-overflow edge cases are reliably exercised.

#[cfg(test)]
mod lift_tests {
    use super::*;
    use proptest::prelude::*;

    // ---- Strategies with edge biasing -----------------------------------

    fn small_signed() -> impl Strategy<Value = i64> {
        // Bias toward edges where signed-overflow bugs live.
        prop_oneof![
            3 => Just(i64::MIN),
            3 => Just(i64::MIN + 1),
            3 => Just(-1i64),
            3 => Just(0i64),
            3 => Just(1i64),
            3 => Just(i64::MAX - 1),
            3 => Just(i64::MAX),
            14 => any::<i64>(),
        ]
    }

    fn small_unsigned() -> impl Strategy<Value = u64> {
        prop_oneof![
            3 => Just(0u64),
            3 => Just(1u64),
            3 => Just(u64::MAX - 1),
            3 => Just(u64::MAX),
            18 => any::<u64>(),
        ]
    }

    fn nonzero_signed() -> impl Strategy<Value = i64> {
        small_signed().prop_filter("nonzero", |x| *x != 0)
    }

    fn nonzero_unsigned() -> impl Strategy<Value = u64> {
        small_unsigned().prop_filter("nonzero", |x| *x != 0)
    }

    // ---- Arithmetic ------------------------------------------------------

    proptest! {
        /// `__vcheck_int::add` on two `i64`s must equal the `i128`-widened
        /// addition. Any value that fits in `i64` widens to `i128`
        /// without loss, and `i128` add is well-defined.
        #[test]
        fn add_matches_i128_oracle(a in small_signed(), b in small_signed()) {
            let lifted = add(a, b);
            let oracle = a as i128 + b as i128;
            prop_assert!(eq(&lifted, oracle));
        }

        #[test]
        fn sub_matches_i128_oracle(a in small_signed(), b in small_signed()) {
            let lifted = sub(a, b);
            let oracle = a as i128 - b as i128;
            prop_assert!(eq(&lifted, oracle));
        }

        #[test]
        fn mul_matches_i128_oracle(a in small_signed(), b in small_signed()) {
            // i64 * i64 fits in i128 (both ≤ 2^63, product ≤ 2^126).
            let lifted = mul(a, b);
            let oracle = a as i128 * b as i128;
            prop_assert!(eq(&lifted, oracle));
        }

        /// Euclidean div on signed: oracle is Rust's `i64::div_euclid`,
        /// which is a completely separate implementation from
        /// `num-traits::Euclid` on BigInt.
        #[test]
        fn div_matches_rust_euclid_signed(
            a in small_signed(),
            b in nonzero_signed(),
        ) {
            // Avoid `i64::MIN / -1` which overflows in `i64::div_euclid`
            // (panics in debug). In SpecInt the result is just `2^63`,
            // which doesn't fit in i64 — that's a *real* value we
            // produce, but the oracle would panic, so we exclude the
            // pair from this differential test.
            //
            // (Verus's spec evaluator on `int` also doesn't overflow
            // here; our lift matches Verus, not Rust's primitive.)
            prop_assume!(!(a == i64::MIN && b == -1));
            let lifted = div(a, b);
            let oracle: i64 = a.div_euclid(b);
            prop_assert!(eq(&lifted, oracle));
        }

        #[test]
        fn rem_matches_rust_euclid_signed(
            a in small_signed(),
            b in nonzero_signed(),
        ) {
            prop_assume!(!(a == i64::MIN && b == -1));
            let lifted = rem(a, b);
            let oracle: i64 = a.rem_euclid(b);
            prop_assert!(eq(&lifted, oracle));
        }

        /// Euclidean div on unsigned matches Rust's `u64::div_euclid`
        /// (which is just truncated div for non-negative operands).
        #[test]
        fn div_matches_rust_unsigned(
            a in small_unsigned(),
            b in nonzero_unsigned(),
        ) {
            let lifted = div(a, b);
            let oracle: u64 = a.div_euclid(b);
            prop_assert!(eq(&lifted, oracle));
        }

        #[test]
        fn rem_matches_rust_unsigned(
            a in small_unsigned(),
            b in nonzero_unsigned(),
        ) {
            let lifted = rem(a, b);
            let oracle: u64 = a.rem_euclid(b);
            prop_assert!(eq(&lifted, oracle));
        }

        /// The defining identity of Euclidean division: `a == q*b + r`
        /// where `0 <= r < |b|`. This holds for signed and unsigned.
        #[test]
        fn div_rem_identity_signed(
            a in small_signed(),
            b in nonzero_signed(),
        ) {
            prop_assume!(!(a == i64::MIN && b == -1));
            let q = div(a, b);
            let r = rem(a, b);
            // a == q*b + r
            let recovered = add(mul(&q, b), &r);
            prop_assert!(eq(&recovered, a));
            // 0 <= r < |b|
            prop_assert!(ge(&r, 0i64));
            let abs_b = if b < 0 { neg(b) } else { lift(b) };
            prop_assert!(lt(&r, &abs_b));
        }

        #[test]
        fn div_rem_identity_unsigned(
            a in small_unsigned(),
            b in nonzero_unsigned(),
        ) {
            let q = div(a, b);
            let r = rem(a, b);
            let recovered = add(mul(&q, b), &r);
            prop_assert!(eq(&recovered, a));
            prop_assert!(ge(&r, 0u64));
            prop_assert!(lt(&r, b));
        }

        /// Negation: `-x == 0 - x`.
        #[test]
        fn neg_matches_sub_from_zero(a in small_signed()) {
            let lifted = neg(a);
            let oracle = sub(0i64, a);
            prop_assert!(eq(&lifted, &oracle));
        }
    }

    // ---- Comparisons -----------------------------------------------------

    proptest! {
        #[test]
        fn lt_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(lt(a, b), (a as i128) < (b as i128));
        }

        #[test]
        fn le_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(le(a, b), (a as i128) <= (b as i128));
        }

        #[test]
        fn gt_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(gt(a, b), (a as i128) > (b as i128));
        }

        #[test]
        fn ge_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(ge(a, b), (a as i128) >= (b as i128));
        }

        #[test]
        fn eq_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(eq(a, b), (a as i128) == (b as i128));
        }

        #[test]
        fn ne_matches_i128(a in small_signed(), b in small_signed()) {
            prop_assert_eq!(ne(a, b), (a as i128) != (b as i128));
        }

        /// Comparisons across mixed signed/unsigned. The lift converts
        /// both to `SpecInt`, which means the comparison happens in
        /// `int` regardless of operand width. Oracle: explicit
        /// `i128`-widening from each side.
        #[test]
        fn lt_mixed_signed_unsigned(a in small_signed(), b in small_unsigned()) {
            // `b: u64` widens cleanly to `i128`. `a: i64` does too.
            prop_assert_eq!(lt(a, b), (a as i128) < (b as i128));
        }
    }

    // ---- Shifts ----------------------------------------------------------

    proptest! {
        /// `shl(a, n) == a * 2^n` for `n` in the valid range.
        #[test]
        fn shl_matches_multiply(
            a in small_signed(),
            n in 0u32..32,
        ) {
            let lifted = shl(a, n);
            // Oracle: a as i128 * 2^n. n < 32 so 2^n fits.
            let oracle = (a as i128) << n;
            prop_assert!(eq(&lifted, oracle));
        }

        /// `shr(a, n) == a / 2^n` (Euclidean div by `2^n`).
        /// Note BigInt's `>>` for negative values follows
        /// arithmetic-shift semantics, matching Rust's `i64 >> n`.
        #[test]
        fn shr_matches_divide(
            a in small_signed(),
            n in 0u32..32,
        ) {
            let lifted = shr(a, n);
            let oracle = (a as i128) >> n;
            prop_assert!(eq(&lifted, oracle));
        }
    }

    // ---- Narrowing casts -------------------------------------------------

    proptest! {
        /// For in-range values, `to_u8(x) == x as u8`.
        #[test]
        fn to_u8_matches_as_cast_in_range(x in 0u8..=255u8) {
            prop_assert_eq!(to_u8(x), x);
            // Through arithmetic that stays in-range.
            if x < 100 {
                prop_assert_eq!(to_u8(add(x, 10u8)), x + 10);
            }
        }

        /// For in-range values, `to_i8(x) == x as i8`.
        #[test]
        fn to_i8_matches_as_cast_in_range(x in i8::MIN..=i8::MAX) {
            prop_assert_eq!(to_i8(x), x);
        }

        /// Differential: `to_<T>(lift(x))` is identity for `x: T`.
        #[test]
        fn to_u32_roundtrip(x in any::<u32>()) {
            prop_assert_eq!(to_u32(x), x);
        }

        #[test]
        fn to_i64_roundtrip(x in any::<i64>()) {
            prop_assert_eq!(to_i64(x), x);
        }

        #[test]
        fn to_u128_roundtrip(x in any::<u128>()) {
            prop_assert_eq!(to_u128(x), x);
        }

        /// Round-trip through wider type and back.
        #[test]
        fn to_u8_after_add_in_range(a in 0u8..=127u8, b in 0u8..=127u8) {
            // a + b ≤ 254, in u8 range.
            prop_assert_eq!(to_u8(add(a, b)), a + b);
        }
    }

    // ---- Out-of-range narrowing must panic --------------------------------

    proptest! {
        /// For any `(a, b)` whose sum exceeds `u8::MAX`, narrowing to
        /// u8 must panic. This is the spec-bug-detection behavior we
        /// rely on: if a contract claims `(x + y) as u8` is in-range
        /// but the runtime evaluation says it isn't, the panic
        /// surfaces as a test failure.
        #[test]
        fn to_u8_panics_when_out_of_range(
            a in 128u8..=255u8,
            b in 128u8..=255u8,
        ) {
            // Use catch_unwind to assert the panic happens. (We can't
            // use #[should_panic] inside proptest!.)
            let result = std::panic::catch_unwind(|| to_u8(add(a, b)));
            prop_assert!(result.is_err());
        }
    }

    // ---- Wrapping-formula correctness ------------------------------------
    //
    // This is the formula the engine inlines for `u8_specs::wrapping_add(x, y)`:
    //   ((x + y) % 256) as u8
    // It should equal Rust's `u8::wrapping_add(x, y)` for *all* inputs.
    // Same for sub and mul.

    proptest! {
        #[test]
        fn inlined_wrapping_add_matches_intrinsic(
            x in any::<u8>(),
            y in any::<u8>(),
        ) {
            let lifted = to_u8(rem(add(x, y), 256u32));
            let oracle = x.wrapping_add(y);
            prop_assert_eq!(lifted, oracle);
        }

        #[test]
        fn inlined_wrapping_sub_matches_intrinsic(
            x in any::<u8>(),
            y in any::<u8>(),
        ) {
            let lifted = to_u8(rem(sub(x, y), 256u32));
            let oracle = x.wrapping_sub(y);
            prop_assert_eq!(lifted, oracle);
        }

        #[test]
        fn inlined_wrapping_mul_matches_intrinsic(
            x in any::<u8>(),
            y in any::<u8>(),
        ) {
            let lifted = to_u8(rem(mul(x, y), 256u32));
            let oracle = x.wrapping_mul(y);
            prop_assert_eq!(lifted, oracle);
        }

        /// Signed wrapping_add: the engine's inlined formula uses the
        /// `signed_crop` shape — `% range`, then if > MAX subtract
        /// `range`. Validate against `i8::wrapping_add`.
        #[test]
        fn inlined_wrapping_add_i8_matches_intrinsic(
            x in any::<i8>(),
            y in any::<i8>(),
        ) {
            let r = rem(add(x, y), 256u32);  // [0, 256)
            let lifted_si = if gt(&r, i8::MAX) {
                sub(&r, 256u32)
            } else {
                r
            };
            let lifted = to_i8(lifted_si);
            let oracle = x.wrapping_add(y);
            prop_assert_eq!(lifted, oracle);
        }

        #[test]
        fn inlined_wrapping_mul_i8_matches_intrinsic(
            x in any::<i8>(),
            y in any::<i8>(),
        ) {
            let r = rem(mul(x, y), 256u32);
            let lifted_si = if gt(&r, i8::MAX) {
                sub(&r, 256u32)
            } else {
                r
            };
            let lifted = to_i8(lifted_si);
            let oracle = x.wrapping_mul(y);
            prop_assert_eq!(lifted, oracle);
        }
    }

    // ---- Bitwise ---------------------------------------------------------

    proptest! {
        #[test]
        fn bitand_matches_u64(a in any::<u64>(), b in any::<u64>()) {
            prop_assert!(eq(bitand(a, b), a & b));
        }

        #[test]
        fn bitor_matches_u64(a in any::<u64>(), b in any::<u64>()) {
            prop_assert!(eq(bitor(a, b), a | b));
        }

        #[test]
        fn bitxor_matches_u64(a in any::<u64>(), b in any::<u64>()) {
            prop_assert!(eq(bitxor(a, b), a ^ b));
        }
    }
}
