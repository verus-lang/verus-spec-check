//! Bolero backend generator layer, the `VcheckGen` mirror of [`VcheckStrategy`].
//!
//! This module is the bolero-side counterpart to the proptest
//! [`crate::VcheckStrategy`] trait. Where `VcheckStrategy` produces a
//! `proptest::Strategy`, [`VcheckGen`] produces a `bolero_generator::ValueGenerator`.
//! The two layers are kept deliberately parallel so the engine can emit either
//! `::verus_spec_check::vcheck_strategy::<T>()` or `::verus_spec_check::vcheck_gen::<T>()` from the
//! same harness-shaping code, selecting the backend per `#[vcheck]`.
//!
//! Compiled only under the `bolero` feature (see the crate's `Cargo.toml`).
//!
//! ## Edge biasing
//!
//! The integer generators reproduce the same edge-biasing rationale as the
//! proptest impls in [`crate`]: uniform sampling rarely hits `T::MIN`,
//! `T::MAX`, `0`, `1`, `-1` for wide types, yet that's exactly where
//! spec-vs-impl mismatches live (e.g. `iN::MIN / -1` overflow). We compose a
//! selector byte with a uniform sample and route ~40% of draws to an edge
//! value. Under coverage-guided fuzzing the fuzzer drives the selector byte
//! itself, so this biasing degrades gracefully to "the fuzzer decides".

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::num::NonZero;
use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use bolero_generator::prelude::*;

use crate::{
    VcheckRangeIdx, ASCII_CHAR_EDGES, DEFAULT_COLLECTION_MAX, NON_ASCII_CHAR_EDGES,
    SLICE_INDEX_WINDOW, STR_INDEX_WINDOW, ZST_BOUNDARY_LENS,
};

/// Bridge trait between `verus_spec_check_*` harnesses and `bolero_generator`. The
/// bolero-backend analogue of [`crate::VcheckStrategy`]: for every parameter type
/// in a contract-bearing exec fn the macro emits `vcheck_gen::<T>()` and hands the
/// resulting generator to `bolero::check!().with_generator(...)`.
///
/// Uses a return-position `impl Trait` (RPITIT) so implementations don't have
/// to name bolero's combinator types (which are deeply nested and unnameable
/// in practice). `ValueGenerator::Output` is `'static`, so implementers must be
/// `'static` too — true for every type the engine samples.
pub trait VcheckGen: Sized {
    /// Build the value generator for `Self`.
    fn vcheck_gen() -> impl ValueGenerator<Output = Self>;
}

/// Convenience function used by the macro-generated bolero harnesses. Mirrors
/// [`crate::vcheck_strategy`].
pub fn vcheck_gen<T: VcheckGen>() -> impl ValueGenerator<Output = T> {
    T::vcheck_gen()
}

// ---------------------------------------------------------------------------
// Edge-biased integer generators.
//
// Selector modulo a fixed total picks between edge values and a uniform draw.
// Weights mirror the proptest impls closely enough to preserve the intent
// (heavy weight on MIN / -1 for signed types).
// ---------------------------------------------------------------------------

macro_rules! impl_unsigned_gen {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckGen for $t {
                fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
                    (produce::<u8>(), produce::<$t>()).map_gen(
                        |(sel, raw): (u8, $t)| match sel % 24 {
                            0 | 1 => <$t>::MIN,
                            2 | 3 => <$t>::MAX,
                            4 | 5 => 0 as $t,
                            6 | 7 => 1 as $t,
                            8 | 9 => <$t>::MAX.saturating_sub(1),
                            _ => raw,
                        },
                    )
                }
            }
        )*
    };
}

macro_rules! impl_signed_gen {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckGen for $t {
                fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
                    // Total of 30 buckets: MIN(4) MAX(2) 0(2) 1(2) -1(4)
                    // MAX-1(2) MIN+1(2) uniform(12). Weights the MIN / -1
                    // pair heavily, matching the proptest signed impl.
                    (produce::<u8>(), produce::<$t>()).map_gen(
                        |(sel, raw): (u8, $t)| match sel % 30 {
                            0..=3 => <$t>::MIN,
                            4 | 5 => <$t>::MAX,
                            6 | 7 => 0 as $t,
                            8 | 9 => 1 as $t,
                            10..=13 => -1 as $t,
                            14 | 15 => <$t>::MAX.saturating_sub(1),
                            16 | 17 => <$t>::MIN.saturating_add(1),
                            _ => raw,
                        },
                    )
                }
            }
        )*
    };
}

impl_unsigned_gen!(u8, u16, u32, u64, u128, usize);
impl_signed_gen!(i8, i16, i32, i64, i128, isize);

// `bool` / `char` / floats: no meaningful "edge" beyond uniform sampling.
// `produce::<f*>()` already covers the IEEE special values (NaN / inf /
// subnormals), matching proptest's `any::<f*>()` behavior.
impl VcheckGen for bool {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<bool>()
    }
}
impl VcheckGen for char {
    // UTF-8 boundary, NUL, and char::MAX biased
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        (produce::<u8>(), produce::<char>(), produce::<u8>()).map_gen(
            |(sel, raw, byte): (u8, char, u8)| {
                let ascii_end = 4 + ASCII_CHAR_EDGES.len();
                let wide_end = ascii_end + NON_ASCII_CHAR_EDGES.len();
                match sel as usize % 48 {
                    0 | 1 => '\u{0}',
                    2 | 3 => char::MAX,
                    s if s < ascii_end => ASCII_CHAR_EDGES[s - 4],
                    s if s < wide_end => NON_ASCII_CHAR_EDGES[s - ascii_end],
                    s if s < wide_end + 8 => char::from(byte & 0x7f),
                    _ => raw,
                }
            },
        )
    }
}
impl VcheckGen for f32 {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<f32>()
    }
}
impl VcheckGen for f64 {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<f64>()
    }
}
impl VcheckGen for String {
    // Build from edge-biased `char`s (see `VcheckGen for char`) rather than
    // bolero's default `String` generator, so sampled strings actually contain
    // multi-byte scalars and surrogate-adjacent boundaries. This is what makes
    // UTF-8 specs (`str::is_ascii`, `is_char_boundary`, ...) exercise their
    // real logic instead of degenerating to the ASCII-only case.
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        let ascii = produce::<Vec<u8>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .values(0u8..=0x7f);
        (
            produce::<u8>(),
            <Vec<char> as VcheckGen>::vcheck_gen(),
            ascii,
            produce::<u8>(),
            produce::<usize>(),
        )
            .map_gen(
                |(sel, mixed, ascii, pick, pos): (u8, Vec<char>, Vec<u8>, u8, usize)| {
                    let ascii: Vec<char> = ascii.into_iter().map(char::from).collect();
                    match sel % 8 {
                        0 => String::new(),
                        1 | 2 => ascii.into_iter().collect(),
                        3 | 4 => {
                            let wide = NON_ASCII_CHAR_EDGES[pick as usize % NON_ASCII_CHAR_EDGES.len()];
                            crate::inject_char(ascii, wide, pos)
                        }
                        _ => mixed.into_iter().collect(),
                    }
                },
            )
    }
}

// ---------------------------------------------------------------------------
// Collections. Elements are drawn from the recursive `VcheckGen` generator so
// edge-biasing carries into container contents (e.g. a `Vec<i64>` can contain
// `i64::MIN`). The base `T: TypeGenerator` bound is required by bolero's
// collection builder; `.values(...)` overrides the actual element generation.
// Primitives implement `TypeGenerator` already, and the engine emits it for
// user types, so the bound is always satisfiable.
// ---------------------------------------------------------------------------

/// Unit: single value, zero bytes. Enables `#[vcheck(T = ())]` container
/// instantiations, where maximum-length containers are O(1) memory —
/// the only practical route to length-arithmetic boundaries
/// (`usize::MAX` in `append`-style growth specs).
impl VcheckGen for () {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<u8>().map_gen(|_| ())
    }
}

impl<T: VcheckGen + TypeGenerator> VcheckGen for Vec<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        let base = produce::<Vec<T>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .values(T::vcheck_gen());
        // Zero-sized, drop-free element types additionally sample
        // length-boundary vecs (mirrors the proptest strategy; see
        // `crate::zst_vec_with_len`). A selector byte routes between
        // the ordinary small vec and one of the boundary lengths, so a
        // pair of independently drawn ZST vecs frequently crosses
        // usize::MAX combined length.
        (produce::<u8>(), base).map_gen(|(selector, mut small): (u8, Vec<T>)| {
            if !crate::is_zst_no_drop::<T>() {
                return small;
            }
            let Some(witness) = small.pop() else {
                return small;
            };
            match ZST_BOUNDARY_LENS.get(selector as usize % (2 * ZST_BOUNDARY_LENS.len())) {
                Some(&len) => crate::zst_vec_with_len(witness, len),
                None => {
                    small.push(witness);
                    small
                }
            }
        })
    }
}

impl<T: VcheckGen + TypeGenerator + 'static> VcheckGen for VecDeque<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        // Exercise both physical representations. `VecDeque::from` starts at
        // head zero (contiguous). For the wrapped case, advance the head just
        // beyond the final contiguous start position; moving owned elements
        // needs no `Clone` bound. The logical sequence is rotated, which is
        // harmless because the generated element order is unconstrained.
        (<Vec<T> as VcheckGen>::vcheck_gen(), produce::<bool>()).map_gen(
            |(values, wrapped): (Vec<T>, bool)| {
                let mut deque = VecDeque::from(values);
                if wrapped && deque.len() >= 2 {
                    let steps = deque.capacity() - deque.len() + 1;
                    for _ in 0..steps {
                        let value = deque
                            .pop_front()
                            .expect("non-empty while constructing wrapped VecDeque");
                        deque.push_back(value);
                    }
                    debug_assert!(!deque.as_slices().1.is_empty());
                }
                deque
            },
        )
    }
}

/// `Box<T>`: generate the payload, box it. Mirrors the proptest-side
/// `VcheckStrategy for Box<T>`.
impl<T: VcheckGen + 'static> VcheckGen for Box<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        T::vcheck_gen().map_gen(Box::new)
    }
}

impl<T: VcheckGen + 'static> VcheckGen for Option<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        (produce::<bool>(), T::vcheck_gen())
            .map_gen(|(is_some, v)| if is_some { Some(v) } else { None })
    }
}

impl<T: VcheckGen + 'static, E: VcheckGen + 'static> VcheckGen for Result<T, E> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        (produce::<bool>(), T::vcheck_gen(), E::vcheck_gen())
            .map_gen(|(is_ok, t, e)| if is_ok { Ok(t) } else { Err(e) })
    }
}

impl<K, V> VcheckGen for HashMap<K, V>
where
    K: VcheckGen + TypeGenerator + Eq + Hash,
    V: VcheckGen + TypeGenerator,
{
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<HashMap<K, V>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .keys(K::vcheck_gen())
            .values(V::vcheck_gen())
    }
}

impl<T> VcheckGen for HashSet<T>
where
    T: VcheckGen + TypeGenerator + Eq + Hash,
{
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<HashSet<T>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .values(T::vcheck_gen())
    }
}

impl<K, V> VcheckGen for BTreeMap<K, V>
where
    K: VcheckGen + TypeGenerator + Ord,
    V: VcheckGen + TypeGenerator,
{
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<BTreeMap<K, V>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .keys(K::vcheck_gen())
            .values(V::vcheck_gen())
    }
}

impl<T> VcheckGen for BTreeSet<T>
where
    T: VcheckGen + TypeGenerator + Ord,
{
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<BTreeSet<T>>()
            .with()
            .len(0usize..=DEFAULT_COLLECTION_MAX)
            .values(T::vcheck_gen())
    }
}

/// Mirror of [`crate::range_endpoint_strategy`].
pub fn range_endpoint_gen<T: VcheckGen + VcheckRangeIdx>() -> impl ValueGenerator<Output = T> {
    (produce::<u8>(), T::vcheck_gen(), 0usize..=STR_INDEX_WINDOW).map_gen(
        |(sel, edge, offset): (u8, T, usize)| {
            let window = match sel % 13 {
                0..=7 => T::vcheck_slice_offset(offset % (SLICE_INDEX_WINDOW + 1)),
                8 | 9 => T::vcheck_slice_offset(offset),
                _ => None,
            };
            window.unwrap_or(edge)
        },
    )
}

impl<T: VcheckGen + VcheckRangeIdx> VcheckGen for Range<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        (produce::<u8>(), range_endpoint_gen::<T>(), range_endpoint_gen::<T>()).map_gen(
            |(sel, a, b): (u8, T, T)| match sel % 8 {
                0..=2 if a <= b => a..b,
                0..=2 => b..a,
                3..=5 => a..b,
                6 => a.clone()..a,
                _ => match a.vcheck_succ() {
                    Some(next) => a..next,
                    None => a.clone()..a,
                },
            },
        )
    }
}

impl<T: VcheckGen + VcheckRangeIdx> VcheckGen for RangeInclusive<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        (produce::<u8>(), range_endpoint_gen::<T>(), range_endpoint_gen::<T>()).map_gen(
            |(sel, a, b): (u8, T, T)| match sel % 8 {
                0..=2 if a <= b => a..=b,
                0..=2 => b..=a,
                3..=5 => a..=b,
                6 => a.clone()..=a,
                _ => T::vcheck_exhausted(a),
            },
        )
    }
}

impl<T: VcheckGen + VcheckRangeIdx> VcheckGen for RangeFrom<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        range_endpoint_gen::<T>().map_gen(|a: T| a..)
    }
}

impl<T: VcheckGen + VcheckRangeIdx> VcheckGen for RangeTo<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        range_endpoint_gen::<T>().map_gen(|b: T| ..b)
    }
}

impl<T: VcheckGen + VcheckRangeIdx> VcheckGen for RangeToInclusive<T> {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        range_endpoint_gen::<T>().map_gen(|b: T| ..=b)
    }
}

impl VcheckGen for RangeFull {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        bolero_generator::constant(..)
    }
}

impl VcheckGen for Ordering {
    fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
        produce::<u8>().map_gen(|sel: u8| crate::ORDERINGS[sel as usize % 3])
    }
}

macro_rules! impl_nonzero_unsigned_gen {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckGen for NonZero<$t> {
                fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
                    (produce::<u8>(), produce::<$t>()).map_gen(|(sel, raw): (u8, $t)| {
                        let v = match sel % 24 {
                            0 | 1 => 1 as $t,
                            2 | 3 => 2 as $t,
                            4 | 5 => <$t>::MAX,
                            6 | 7 => <$t>::MAX - 1,
                            8 | 9 => (1 as $t) << (<$t>::BITS - 1),
                            _ => raw,
                        };
                        NonZero::new(v).unwrap_or(NonZero::<$t>::MIN)
                    })
                }
            }
        )*
    };
}

macro_rules! impl_nonzero_signed_gen {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckGen for NonZero<$t> {
                fn vcheck_gen() -> impl ValueGenerator<Output = Self> {
                    (produce::<u8>(), produce::<$t>()).map_gen(|(sel, raw): (u8, $t)| {
                        let v = match sel % 30 {
                            0..=3 => <$t>::MIN,
                            4 | 5 => <$t>::MAX,
                            6 | 7 => 1 as $t,
                            8..=11 => -1 as $t,
                            12 | 13 => <$t>::MIN + 1,
                            14 | 15 => <$t>::MAX - 1,
                            _ => raw,
                        };
                        NonZero::new(v).unwrap_or(NonZero::<$t>::MIN)
                    })
                }
            }
        )*
    };
}

impl_nonzero_unsigned_gen!(u8, u16, u32, u64, u128, usize);
impl_nonzero_signed_gen!(i8, i16, i32, i64, i128, isize);

// ---------------------------------------------------------------------------
// ExecMultiset<T> inner-shape helper. The bolero mirror of
// [`crate::multiset_inner_strategy`]. Produces a `HashMap<T, usize>` whose
// counts are bounded by `count_max`, from which the macro bootstraps an
// `ExecMultiset<T>` without this crate having to know the vstd type.
// ---------------------------------------------------------------------------

/// Build a generator producing an `ExecMultiset`-shaped `HashMap<T, usize>`
/// with counts bounded by `count_max`. Mirrors
/// [`crate::multiset_inner_strategy`] for the bolero backend.
pub fn multiset_inner_gen<T>(count_max: u32) -> impl ValueGenerator<Output = HashMap<T, usize>>
where
    T: VcheckGen + TypeGenerator + Eq + Hash,
{
    produce::<HashMap<T, usize>>()
        .with()
        .len(0usize..=DEFAULT_COLLECTION_MAX)
        .keys(T::vcheck_gen())
        .values(0usize..=count_max as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bolero_generator::driver::ByteSliceDriver;

    fn sample<G: ValueGenerator>(g: &G, seed: u64) -> Option<G::Output> {
        let bytes = seed.to_le_bytes();
        let mut d = ByteSliceDriver::new(&bytes, &Default::default());
        g.generate(&mut d)
    }

    // Spread of deterministic seeds for coverage assertions.
    fn seeds() -> impl Iterator<Item = u64> {
        (0..8000u64).map(|s| s.wrapping_mul(0x9E37_79B9_7F4A_7C15))
    }

    #[test]
    fn unsigned_hits_min_and_max() {
        let g = vcheck_gen::<u32>();
        let mut saw_min = false;
        let mut saw_max = false;
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                saw_min |= v == u32::MIN;
                saw_max |= v == u32::MAX;
            }
        }
        assert!(saw_min && saw_max, "min={saw_min} max={saw_max}");
    }

    #[test]
    fn signed_hits_min_and_neg_one() {
        let g = vcheck_gen::<i64>();
        let mut saw_min = false;
        let mut saw_neg1 = false;
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                saw_min |= v == i64::MIN;
                saw_neg1 |= v == -1;
            }
        }
        assert!(saw_min && saw_neg1, "min={saw_min} neg1={saw_neg1}");
    }

    #[test]
    fn vec_respects_bound_and_nonempty() {
        let g = vcheck_gen::<Vec<i64>>();
        let mut max_len = 0usize;
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                assert!(v.len() <= DEFAULT_COLLECTION_MAX);
                max_len = max_len.max(v.len());
            }
        }
        assert!(max_len > 0, "only empty vecs generated");
    }

    #[test]
    fn option_generates_some_and_none() {
        let g = vcheck_gen::<Option<u32>>();
        let (mut some, mut none) = (false, false);
        for s in seeds() {
            match sample(&g, s) {
                Some(Some(_)) => some = true,
                Some(None) => none = true,
                None => {}
            }
        }
        assert!(some && none, "some={some} none={none}");
    }

    #[test]
    fn result_generates_ok_and_err() {
        let g = vcheck_gen::<Result<u8, i8>>();
        let (mut ok, mut err) = (false, false);
        for s in seeds() {
            match sample(&g, s) {
                Some(Ok(_)) => ok = true,
                Some(Err(_)) => err = true,
                None => {}
            }
        }
        assert!(ok && err, "ok={ok} err={err}");
    }

    #[test]
    fn hashmap_and_hashset_generate() {
        let mg = vcheck_gen::<HashMap<u16, u8>>();
        let sg = vcheck_gen::<HashSet<u16>>();
        let (mut m_nonempty, mut s_nonempty) = (false, false);
        for s in seeds() {
            if let Some(m) = sample(&mg, s) {
                assert!(m.len() <= DEFAULT_COLLECTION_MAX);
                m_nonempty |= !m.is_empty();
            }
            if let Some(set) = sample(&sg, s) {
                assert!(set.len() <= DEFAULT_COLLECTION_MAX);
                s_nonempty |= !set.is_empty();
            }
        }
        assert!(m_nonempty && s_nonempty);
    }

    #[test]
    fn multiset_inner_counts_bounded() {
        let g = multiset_inner_gen::<u16>(3);
        for s in seeds() {
            if let Some(m) = sample(&g, s) {
                for (_k, count) in &m {
                    assert!(*count <= 3, "count {count} exceeded max");
                }
            }
        }
    }

    // Every unsigned width must be able to produce MIN and MAX (the edge
    // values uniform sampling misses for wide types).
    macro_rules! unsigned_edge_test {
        ($name:ident, $t:ty) => {
            #[test]
            fn $name() {
                let g = vcheck_gen::<$t>();
                let (mut lo, mut hi) = (false, false);
                for s in seeds() {
                    if let Some(v) = sample(&g, s) {
                        lo |= v == <$t>::MIN;
                        hi |= v == <$t>::MAX;
                    }
                }
                assert!(lo && hi, "{}: min={lo} max={hi}", stringify!($t));
            }
        };
    }
    unsigned_edge_test!(edge_u8, u8);
    unsigned_edge_test!(edge_u16, u16);
    unsigned_edge_test!(edge_u64, u64);
    unsigned_edge_test!(edge_u128, u128);
    unsigned_edge_test!(edge_usize, usize);

    // Every signed width must reach MIN and -1 (the `iN::MIN / -1` overflow
    // pair is the canonical spec-vs-impl mismatch).
    macro_rules! signed_edge_test {
        ($name:ident, $t:ty) => {
            #[test]
            fn $name() {
                let g = vcheck_gen::<$t>();
                let (mut min, mut neg1) = (false, false);
                for s in seeds() {
                    if let Some(v) = sample(&g, s) {
                        min |= v == <$t>::MIN;
                        neg1 |= v == -1;
                    }
                }
                assert!(min && neg1, "{}: min={min} neg1={neg1}", stringify!($t));
            }
        };
    }
    signed_edge_test!(edge_i8, i8);
    signed_edge_test!(edge_i16, i16);
    signed_edge_test!(edge_i32, i32);
    signed_edge_test!(edge_i128, i128);
    signed_edge_test!(edge_isize, isize);

    #[test]
    fn bool_generates_both() {
        let g = vcheck_gen::<bool>();
        let (mut t, mut f) = (false, false);
        for s in seeds() {
            match sample(&g, s) {
                Some(true) => t = true,
                Some(false) => f = true,
                None => {}
            }
        }
        assert!(t && f, "true={t} false={f}");
    }

    #[test]
    fn char_and_floats_generate_without_panicking() {
        let cg = vcheck_gen::<char>();
        let f32g = vcheck_gen::<f32>();
        let f64g = vcheck_gen::<f64>();
        let (mut c_any, mut f32_any, mut f64_any) = (false, false, false);
        for s in seeds() {
            if sample(&cg, s).is_some() {
                c_any = true;
            }
            if sample(&f32g, s).is_some() {
                f32_any = true;
            }
            if sample(&f64g, s).is_some() {
                f64_any = true;
            }
        }
        assert!(c_any && f32_any && f64_any);
    }

    #[test]
    fn string_generates_nonempty_sometimes() {
        let g = vcheck_gen::<String>();
        let mut saw_nonempty = false;
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                saw_nonempty |= !v.is_empty();
            }
        }
        assert!(saw_nonempty, "only empty strings generated");
    }

    // Nested collections: the `T: VcheckGen + TypeGenerator` bound composes, so
    // `Vec<Option<_>>`, `Vec<Vec<_>>`, and `Option<Vec<_>>` all work and honor
    // the element bounds.
    #[test]
    fn nested_vec_of_option_generates_variants() {
        let g = vcheck_gen::<Vec<Option<u8>>>();
        let (mut some, mut none) = (false, false);
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                assert!(v.len() <= DEFAULT_COLLECTION_MAX);
                for e in &v {
                    match e {
                        Some(_) => some = true,
                        None => none = true,
                    }
                }
            }
        }
        assert!(some && none, "some={some} none={none}");
    }

    #[test]
    fn nested_vec_of_vec_respects_outer_bound() {
        let g = vcheck_gen::<Vec<Vec<u8>>>();
        let mut saw_inner = false;
        for s in seeds() {
            if let Some(v) = sample(&g, s) {
                assert!(v.len() <= DEFAULT_COLLECTION_MAX);
                for inner in &v {
                    assert!(inner.len() <= DEFAULT_COLLECTION_MAX);
                    saw_inner |= !inner.is_empty();
                }
            }
        }
        assert!(saw_inner, "never generated a non-empty inner vec");
    }

    #[test]
    fn option_of_vec_generates() {
        let g = vcheck_gen::<Option<Vec<u8>>>();
        let (mut some, mut none) = (false, false);
        for s in seeds() {
            match sample(&g, s) {
                Some(Some(v)) => {
                    assert!(v.len() <= DEFAULT_COLLECTION_MAX);
                    some = true;
                }
                Some(None) => none = true,
                None => {}
            }
        }
        assert!(some && none);
    }

    // The free `vcheck_gen::<T>()` fn must be equivalent to `T::vcheck_gen()`.
    #[test]
    fn free_vcheck_gen_matches_trait_method() {
        let via_fn = vcheck_gen::<u32>();
        let via_trait = <u32 as VcheckGen>::vcheck_gen();
        // Same seed -> same value (both are the identical edge-biased gen).
        for s in seeds().take(200) {
            assert_eq!(sample(&via_fn, s), sample(&via_trait, s));
        }
    }

    fn entropy(seed: u64) -> Vec<u8> {
        let mut state = seed;
        (0..32)
            .flat_map(|_| {
                state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
                let mut z = state;
                z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
                (z ^ (z >> 31)).to_le_bytes()
            })
            .collect()
    }

    fn draws<T: VcheckGen>(n: u64) -> Vec<T> {
        let g = vcheck_gen::<T>();
        (0..n)
            .filter_map(|seed| {
                let bytes = entropy(seed);
                let mut d = ByteSliceDriver::new(&bytes, &Default::default());
                g.generate(&mut d)
            })
            .collect()
    }

    #[test]
    fn char_and_string_hit_edges() {
        let chars = draws::<char>(4000);
        for c in ASCII_CHAR_EDGES.iter().chain(NON_ASCII_CHAR_EDGES.iter()) {
            assert!(chars.contains(c), "edge {:?} never generated", c);
        }
        let strings = draws::<String>(2000);
        assert!(strings.iter().any(|s| !s.is_empty() && s.is_ascii()));
        assert!(strings.iter().any(|s| {
            s.chars().filter(|c| !c.is_ascii()).count() == 1 && s.chars().count() > 1
        }));
    }

    #[test]
    fn zst_vec_reaches_every_boundary_len() {
        let lens: Vec<usize> = draws::<Vec<()>>(4000).iter().map(Vec::len).collect();
        for want in ZST_BOUNDARY_LENS {
            assert!(lens.contains(&want), "boundary len {want} never generated");
        }
    }

    #[test]
    fn ranges_cover_slice_index_shapes_and_exhaustion() {
        let ranges = draws::<Range<usize>>(4000);
        let slice = [0u8; DEFAULT_COLLECTION_MAX];
        let hits = ranges.iter().filter(|r| slice.get((*r).clone()).is_some()).count();
        assert!(hits * 4 > ranges.len(), "only {hits} in-bounds ranges");
        assert!(ranges.iter().any(|r| r.start > r.end));
        let inclusive = draws::<RangeInclusive<usize>>(4000);
        assert!(inclusive.iter().any(|r| r.is_empty() && r.start() == r.end()));
    }

    #[test]
    fn ordering_and_nonzero_generate_edges() {
        let seen: HashSet<Ordering> = draws::<Ordering>(200).into_iter().collect();
        assert_eq!(seen, HashSet::from(crate::ORDERINGS));
        let values: Vec<i32> = draws::<NonZero<i32>>(4000).iter().map(|n| n.get()).collect();
        assert!(values.contains(&i32::MIN) && values.contains(&-1));
    }
}
