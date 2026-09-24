//! `SpecReal` -- a faithful runtime mirror of Verus's spec `real` type.
//!
//! Verus's `real` is the mathematical reals: an ordered field with exact
//! `+ - * /` (real division — no rounding, no remainder) plus `floor`. The
//! only operations expressible without axioms are those field ops and floor,
//! all of which are *exact on rationals*. So we back `SpecReal` with
//! [`num_rational::BigRational`] (a `BigInt`-backed rational), exactly mirroring
//! the way [`crate::spec_int::SpecInt`] backs `int`/`nat` with `BigInt`.
//!
//! Why not `f64`? Verus `real` contracts assert *exact* equalities (e.g.
//! `(x as real) / 3 * 3 == x as real`). `f64` rounding would produce spurious
//! property-test pass/fail. `BigRational` evaluates the field ops exactly.
//!
//! ## Conventions
//!
//! - **`int as real`** (`to_real`): exact. `From<BigInt>`.
//! - **`f32`/`f64` as real** (`fp.to_real`): exact for *finite* floats (a
//!   float's value is a dyadic rational). **Unspecified** for `NaN` / `±inf`,
//!   so [`from_f64`] / [`from_f32`] return `None` and the harness *skips* the
//!   case (like a `requires` rejection) rather than asserting a bogus value.
//! - **`real / 0`**: unspecified in Verus (SMT Reals `/`-by-zero is
//!   arbitrary-but-fixed; Verus adds no div-by-zero obligation for `real`,
//!   unlike `int`). [`div`] returns `None` ⇒ the harness skips. It never panics.
//! - **`real as int`** / **`real::floor()`**: floor (largest integer ≤ self).
//!
//! The two `None`-returning conversions/ops are the *unconstrained* cases: the
//! Verus spec makes no claim there, so a property test can only skip them.

use std::cell::Cell;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

/// Runtime mirror of Verus `real`. Exact rational — the `real` analogue of
/// [`crate::spec_int::SpecInt`] (`= BigInt`).
pub type SpecReal = BigRational;

// ---------------------------------------------------------------------------
// "Defined" flag for the unconstrained cases.
//
// Verus leaves two real operations UNSPECIFIED: `real / 0` and the real value
// of a non-finite float (`NaN`/`±inf`). The spec claims nothing there, so a
// property test must *skip* such a case rather than assert a bogus value.
//
// Threading `Option` through every nested real expression would be invasive
// and would make the rewriter's output diverge from the clean `__vcheck_int::*`
// shape. Instead, the helpers that can hit an unspecified case set a
// thread-local "undefined" flag and return a placeholder (`0`). The generated
// harness calls `reset_defined()` before evaluating a clause and `is_defined()`
// after; if the clause touched an unspecified value, it skips the case.
// ---------------------------------------------------------------------------
thread_local! {
    static UNDEFINED: Cell<bool> = const { Cell::new(false) };
}

/// Clear the "undefined" flag. The harness calls this immediately before
/// evaluating a `requires` / `ensures` clause that references `real`.
#[inline]
pub fn reset_defined() {
    UNDEFINED.with(|u| u.set(false));
}

/// `true` iff no unspecified real operation (`÷0` or non-finite float->real)
/// occurred since the last [`reset_defined`]. The harness skips the case when
/// this is `false`.
#[inline]
pub fn is_defined() -> bool {
    UNDEFINED.with(|u| !u.get())
}

#[inline]
fn mark_undefined() {
    UNDEFINED.with(|u| u.set(true));
}

/// Trait-alias for "anything that can be converted *infallibly* to a
/// `SpecReal`": integer primitives and [`SpecInt`](crate::spec_int::SpecInt).
/// Floats are deliberately excluded here (their conversion is fallible — see
/// [`from_f64`] / [`from_f32`]).
pub trait IntoSpecReal {
    fn into_spec_real(self) -> SpecReal;
}

macro_rules! impl_into_spec_real {
    ($($t:ty),* $(,)?) => {
        $(
            impl IntoSpecReal for $t {
                #[inline]
                fn into_spec_real(self) -> SpecReal {
                    BigRational::from(BigInt::from(self))
                }
            }
        )*
    };
}

impl_into_spec_real!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl IntoSpecReal for BigInt {
    #[inline]
    fn into_spec_real(self) -> SpecReal {
        BigRational::from(self)
    }
}

impl IntoSpecReal for SpecReal {
    #[inline]
    fn into_spec_real(self) -> SpecReal {
        self
    }
}

impl IntoSpecReal for &SpecReal {
    #[inline]
    fn into_spec_real(self) -> SpecReal {
        self.clone()
    }
}

// Floats convert via `fp.to_real`: exact for finite values, unspecified for
// `NaN`/`±inf` (marks the clause undefined and yields a placeholder `0`). This
// lets `x as real` lower to a single `cast(x)` regardless of whether `x` is an
// integer or a float — no type info needed at rewrite time.
impl IntoSpecReal for f64 {
    #[inline]
    fn into_spec_real(self) -> SpecReal {
        from_f64(self)
    }
}

impl IntoSpecReal for f32 {
    #[inline]
    fn into_spec_real(self) -> SpecReal {
        from_f32(self)
    }
}

/// `x as real` for any integer or float `x`. The single entry point the
/// rewriter emits for an `as real` cast — dispatches through [`IntoSpecReal`],
/// so integers convert exactly and floats go through the finite/non-finite
/// path in [`from_f64`] / [`from_f32`].
#[inline]
pub fn cast(x: impl IntoSpecReal) -> SpecReal {
    x.into_spec_real()
}

/// Parse an exact decimal `real` literal (e.g. `"1.5"`, `"100"`, `"-0.25"`).
/// Verus `real` literals denote the *exact* decimal value, so `0.1real` is
/// `1/10` — NOT the `f64` approximation. Emitted by the rewriter for a
/// `<digits>real` / `<digits>.<digits>real` literal.
pub fn from_str(s: &str) -> SpecReal {
    let (sign, s) = match s.strip_prefix('-') {
        Some(rest) => (-1, rest),
        None => (1, s.trim_start_matches('+')),
    };
    let (int_part, frac_part) = match s.split_once('.') {
        Some((i, f)) => (i, f),
        None => (s, ""),
    };
    let mut digits = String::new();
    digits.push_str(int_part);
    digits.push_str(frac_part);
    if digits.is_empty() {
        digits.push('0');
    }
    let numer = digits
        .parse::<BigInt>()
        .unwrap_or_else(|_| panic!("verus_spec_check: malformed real literal `{s}`"));
    let denom = num_traits::pow(BigInt::from(10u8), frac_part.len());
    BigRational::new(BigInt::from(sign) * numer, denom)
}

/// Identity/normalization helper (mirrors [`crate::spec_int::lift`]). Marks a
/// value as flowing in the unbounded real domain.
#[inline]
pub fn lift(x: impl IntoSpecReal) -> SpecReal {
    x.into_spec_real()
}

/// `int as real` (and any integer primitive -> real): exact.
#[inline]
pub fn from_int(x: impl IntoSpecReal) -> SpecReal {
    x.into_spec_real()
}

/// `f64 as real`. Exact rational for finite floats. For `NaN`/`±inf`
/// (unspecified in Verus) it marks the current clause *undefined* (so the
/// harness skips) and returns a placeholder `0`.
#[inline]
pub fn from_f64(f: f64) -> SpecReal {
    match BigRational::from_float(f) {
        Some(r) => r,
        None => {
            mark_undefined();
            BigRational::zero()
        }
    }
}

/// `f32 as real`. Same contract as [`from_f64`].
#[inline]
pub fn from_f32(f: f32) -> SpecReal {
    match BigRational::from_float(f) {
        Some(r) => r,
        None => {
            mark_undefined();
            BigRational::zero()
        }
    }
}

#[inline]
pub fn add(a: impl IntoSpecReal, b: impl IntoSpecReal) -> SpecReal {
    a.into_spec_real() + b.into_spec_real()
}

#[inline]
pub fn sub(a: impl IntoSpecReal, b: impl IntoSpecReal) -> SpecReal {
    a.into_spec_real() - b.into_spec_real()
}

#[inline]
pub fn mul(a: impl IntoSpecReal, b: impl IntoSpecReal) -> SpecReal {
    a.into_spec_real() * b.into_spec_real()
}

/// Real division. When the divisor is zero (unspecified in Verus) it marks the
/// current clause *undefined* (so the harness skips) and returns a placeholder
/// `0`. Never panics.
#[inline]
pub fn div(a: impl IntoSpecReal, b: impl IntoSpecReal) -> SpecReal {
    let b = b.into_spec_real();
    if b.is_zero() {
        mark_undefined();
        BigRational::zero()
    } else {
        a.into_spec_real() / b
    }
}

#[inline]
pub fn neg(a: impl IntoSpecReal) -> SpecReal {
    -a.into_spec_real()
}

/// `real as int` / `real::floor()`: the largest integer ≤ `a`. Returns a
/// [`SpecInt`](crate::spec_int::SpecInt) so the result plugs straight into the
/// existing integer lowering.
#[inline]
pub fn floor(a: impl IntoSpecReal) -> BigInt {
    a.into_spec_real().floor().to_integer()
}

#[inline]
pub fn lt(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() < b.into_spec_real()
}

#[inline]
pub fn le(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() <= b.into_spec_real()
}

#[inline]
pub fn gt(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() > b.into_spec_real()
}

#[inline]
pub fn ge(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() >= b.into_spec_real()
}

#[inline]
pub fn eq(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() == b.into_spec_real()
}

#[inline]
pub fn ne(a: impl IntoSpecReal, b: impl IntoSpecReal) -> bool {
    a.into_spec_real() != b.into_spec_real()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64, d: i64) -> SpecReal {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn int_to_real_exact_and_arithmetic() {
        reset_defined();
        assert_eq!(from_int(5i64), r(5, 1));
        // (1/3) * 3 == 1 exactly — the property f64 gets wrong.
        let third = div(from_int(1u8), from_int(3u8));
        assert!(is_defined());
        assert!(eq(mul(&third, from_int(3u8)), from_int(1u8)));
    }

    #[test]
    fn div_by_zero_marks_undefined() {
        reset_defined();
        let _ = div(from_int(1u8), from_int(0u8));
        assert!(!is_defined(), "÷0 must mark the clause undefined");
        reset_defined();
        assert!(is_defined(), "reset clears the flag");
    }

    #[test]
    fn floor_rounds_toward_neg_inf() {
        assert_eq!(floor(r(7, 2)), BigInt::from(3));
        assert_eq!(floor(r(-7, 2)), BigInt::from(-4));
    }

    #[test]
    fn finite_float_exact_nonfinite_marks_undefined() {
        reset_defined();
        assert_eq!(from_f64(0.5), r(1, 2));
        // 0.1 is not exactly 1/10; fp.to_real gives the exact dyadic value.
        assert_ne!(from_f64(0.1), r(1, 10));
        assert!(from_f32(0.25f32) == r(1, 4));
        assert!(is_defined(), "finite floats keep the clause defined");

        reset_defined();
        let _ = from_f64(f64::NAN);
        assert!(!is_defined());
        reset_defined();
        let _ = from_f64(f64::INFINITY);
        assert!(!is_defined());
        reset_defined();
        let _ = from_f32(f32::NEG_INFINITY);
        assert!(!is_defined());
    }

    #[test]
    fn mixed_int_and_float_compare() {
        // (3 as real)/(2 as real) == 1.5f64 as real
        assert!(eq(div(from_int(3u8), from_int(2u8)), from_f64(1.5)));
    }

    #[test]
    fn sub_lift_and_bigint_into() {
        assert_eq!(sub(from_int(5u8), from_int(2u8)), r(3, 1));
        // `lift` is the identity/normalization entry point.
        assert_eq!(lift(4u8), r(4, 1));
        // `IntoSpecReal for BigInt` (the `SpecInt` bridge).
        assert_eq!(BigInt::from(7).into_spec_real(), r(7, 1));
    }

    #[test]
    fn from_str_integer_and_sign_forms() {
        assert_eq!(from_str("42"), r(42, 1));
        assert_eq!(from_str("+1.5"), r(3, 2)); // leading `+` accepted
        assert_eq!(from_str("-3"), r(-3, 1));
        assert_eq!(from_str("0"), r(0, 1));
    }

    #[test]
    #[should_panic(expected = "malformed real literal")]
    fn from_str_malformed_panics() {
        let _ = from_str("1.2.3");
    }

    #[test]
    fn from_str_is_exact_decimal() {
        // `0.1real` is EXACTLY 1/10 (not the f64 approximation).
        assert_eq!(from_str("0.1"), r(1, 10));
        assert_eq!(from_str("1.5"), r(3, 2));
        assert_eq!(from_str("100"), r(100, 1));
        assert_eq!(from_str("-0.25"), r(-1, 4));
        // And it differs from the float rounding of the same decimal.
        assert_ne!(from_str("0.1"), from_f64(0.1));
    }

    #[test]
    fn cast_dispatches_int_and_float() {
        reset_defined();
        assert_eq!(cast(3u32), r(3, 1));
        assert_eq!(cast(1.5f64), r(3, 2));
        assert!(is_defined());
        reset_defined();
        let _ = cast(f64::NAN);
        assert!(!is_defined(), "non-finite float cast marks undefined");
    }

    #[test]
    fn comparisons() {
        assert!(lt(from_int(1u8), from_int(2u8)));
        assert!(le(r(1, 2), r(1, 2)) && !lt(r(1, 2), r(1, 2)));
        assert!(gt(from_int(2u8), from_int(1u8)) && ge(from_int(2u8), from_int(2u8)));
        assert!(ne(r(1, 3), r(1, 4)));
        assert_eq!(neg(from_int(3u8)), r(-3, 1));
    }
}
