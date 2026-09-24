//! Runtime support for the `verus_spec_check_unverified!` and `verus_spec_check_verified!`
//! macros (defined in the sibling `verus-spec-check-macros` crate).
//!
//! The macros generate `proptest!` harness modules that call
//! `vcheck_strategy::<T>()` once per function parameter. Implementations of
//! [`VcheckStrategy`] for primitives, `Vec<T>`, `Option<T>`, `Result<T, E>`,
//! `HashMap<K, V>` and `HashSet<T>` are provided here. The macro
//! additionally emits a `VcheckStrategy` impl alongside every user-defined
//! `Exec*` struct/enum it generates.
//!
//! This crate is intentionally minimal, and should only depend on vcheck crates.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use proptest::collection::{hash_map, hash_set, vec};
use proptest::prelude::any;
use proptest::strategy::{BoxedStrategy, Strategy};

// ---------------------------------------------------------------------------
// proptest re-export
//
// We re-export the entire `proptest` crate at `verus_spec_check_runtime::proptest`
// so users don't need a separate `proptest = "1"` dev-dependency. The
// macro-generated harnesses reference proptest through this re-export
// (e.g. `::verus_spec_check_runtime::proptest::strategy::Strategy` rather than
// `::proptest::strategy::Strategy`), so adding `verus_spec_check_runtime` to a
// project's `[dev-dependencies]` is sufficient.
//
// ---------------------------------------------------------------------------

/// Re-export of the `proptest` crate at our pinned version.
pub use proptest;

// feature-gated bolero re-exports, such that `verus_spec_check::bolero`
// and `verus_spec_check::bolero_generator` can be used without any additional dependencies.

#[cfg(feature = "bolero")]
pub use bolero; // re-export of the bolero front-end crate; `verus_spec_check::bolero`

// For `ValueGenerator` and `TypeGenerator` traits
#[cfg(feature = "bolero")]
pub use bolero_generator; // reached as `verus_spec_check::bolero_generator`

// Bolero back-end generator
#[cfg(feature = "bolero")]
pub mod bolero_gen;

// Re-export the bolero `VcheckGen` trait and `vcheck_gen()` helper at the crate
// root so the engine can emit `::verus_spec_check::vcheck_gen::<T>()` symmetrically
// with `::verus_spec_check::vcheck_strategy::<T>()`.
#[cfg(feature = "bolero")]
pub use bolero_gen::{vcheck_gen, VcheckGen};

// A default upper-bound for the size of generated collections, e.g.
// `Vec`, `HashMap`, `HashSet`, etc. Eventually this should be
// an option acceptable from `#[vcheck(collection_max = 420)]` ...
pub const DEFAULT_COLLECTION_MAX: usize = 16;

// Sampled predicate values for higher-order contracts
// (`pred: impl Fn(&T) -> bool` parameters).
pub mod pred;
pub use pred::{VcheckPred, PredKind};

pub mod cov_mutate; // #[vcheck_cov_mutate]

#[cfg(not(kani))]
pub mod kani_orch; // #[vcheck(mode = "kani")]

pub mod cov_fuzz; // #[vcheck_cov_fuzz]
mod cov_fuzz_ext; // instrumentation helpers
mod cov_mir; // MIR branch-manifest resolution (covdriver orchestration)

#[cfg(not(kani))]
pub mod spec_int; // runtime mirror of Verus's int type with num_bigint
#[cfg(kani)]
#[path = "spec_int_kani.rs"]
pub mod spec_int; // use i128s for kani ints, since num_bigint has an unbounded heap

#[doc(hidden)]
pub use spec_int as __vcheck_int;
pub mod spec_real; // BigInt real support

#[doc(hidden)]
pub use spec_real as __vcheck_real;

pub mod concretize; // support for running vcheck over types with uninterpreted views
pub use concretize::VcheckConcretize;

/// Re-export the runtime math-integer type so `VcheckConcretize` impls can name
/// `vcheck_realize`'s return type as `verus_spec_check::SpecInt`.
pub use spec_int::SpecInt;

/// Re-export the runtime real type (the `real` analogue of [`SpecInt`]).
pub use spec_real::SpecReal;

/// VcheckStrategy is a core bridging trait between the verus-spec-check harness,
/// and the proptesting engine itself. For every parameter type
/// appearing in a contract, the macro emits a `vcheck_strategy::<T>()`
/// and asks the proptester to produce values of `T`.
///
/// If the user does not label their cross-file self-defined type with
/// `#[vcheck_provide]`, the engine will not be able to automatically generate
/// a VcheckStrategy for it. So, we surface this error.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not set up for property-based testing",
    label = "no `VcheckStrategy` for `{Self}`",
    note = "add `#[vcheck_provide]` to the definition of `{Self}` (and its spec fns) so \
            verus_spec_check can try to generate a proptest strategy and exec companion for it",
    note = "if `{Self}` is defined in this same `verus!` block as the `#[vcheck]` function, \
            this is generated automatically; across files/modules each type must be \
            marked `#[vcheck_provide]` at its own definition site"
)]
pub trait VcheckStrategy: Sized {
    type Strategy: Strategy<Value = Self>;
    // implementations should return a strategy that produces values
    // respecting the structure of the type, similar to the `Arbitrary` crate
    fn vcheck_strategy() -> Self::Strategy;
}

// Convenience function used by the macro-generated harnesses.
pub fn vcheck_strategy<T: VcheckStrategy>() -> T::Strategy {
    T::vcheck_strategy()
}

// Converts a sampled value of a user's spec-side type into the engine's
// `Exec*` model, such that the harness can feed it to the generated `exec_*`
// spec companions. This is generated at the type's `#[vcheck_provide]` site,
// and resolved by trait lookup across files. This idea is core to the cross-
// file attribution of verus-spec-check.
#[diagnostic::on_unimplemented(
    message = "`{Self}` has no exec model for property-based testing",
    label = "no `ToExecModel` for `{Self}`",
    note = "add `#[vcheck_provide]` to the definition of `{Self}` so verus_spec_check can generate \
            its exec-model conversion"
)]
pub trait ToExecModel {
    type Exec;
    // Convert `&self` into its `Exec*` model.
    fn to_exec_model(&self) -> Self::Exec;
}

// Marker that a user type's spec fns have runnable companions available.
// The harness rewrites a spec call `x.foo_spec()` into a call through this
// trait; if the type was never `#[vcheck_provide]`'d, the missing impl produces
// a tailored error rather than a raw "method not found".
//
// The actual companions are inherent `*_exec` methods generated at the
// `#[vcheck_provide]` site; this trait exists so a missing provider is reported
// as a clear trait-bound error. The harness emits a
// `let _: () = <T as VcheckSpecCompanion>::ASSERT_PROVIDED;`-style touch when it
// calls a spec companion, so the diagnostic fires.
#[diagnostic::on_unimplemented(
    message = "the spec fns of `{Self}` have no runnable companions for property-based testing",
    label = "no `VcheckSpecCompanion` for `{Self}`",
    note = "add `#[vcheck_provide]` to the definition of `{Self}` (and its spec fns) so \
            verus_spec_check can generate runnable companions used to evaluate contracts"
)]
pub trait VcheckSpecCompanion {
    const PROVIDED: () = ();
}

// ---------------------------------------------------------------------------
// Edge-biased integer strategies.
//
// Proptest's default `any::<T>()` for primitive integers is a uniform
// random distribution. That's fine for most cases, but really we
// also want to make sure we hit edge inputs such as `T::MIN`, `T::MAX`,
// `0`, `-1`, `1`.
//
// This simple strategy tries to pick some edge cases, and falls
// back to the uniform random distribution ofr the rest. The approach
// for this uses proptest::prop_oneof, which allows you to weight choices
//
// See: https://docs.rs/proptest/latest/proptest/macro.prop_oneof.html
macro_rules! impl_int_with_edges {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckStrategy for $t {
                type Strategy = BoxedStrategy<$t>;
                fn vcheck_strategy() -> Self::Strategy {
                    use proptest::prelude::Just;
                    use proptest::prop_oneof;
                    prop_oneof![
                        2 => Just(<$t>::MIN),
                        2 => Just(<$t>::MAX),
                        2 => Just(0 as $t),
                        2 => Just(1 as $t),
                        2 => Just(<$t>::MAX.saturating_sub(1)),
                        14 => any::<$t>(), // uniform fallback
                    ].boxed()
                }
            }
        )*
    };
}

// Signed versions also include `-1`
macro_rules! impl_signed_with_edges {
    ($($t:ty),* $(,)?) => {
        $(
            impl VcheckStrategy for $t {
                type Strategy = BoxedStrategy<$t>;
                fn vcheck_strategy() -> Self::Strategy {
                    use proptest::prelude::Just;
                    use proptest::prop_oneof;
                    prop_oneof![
                        4 => Just(<$t>::MIN),
                        2 => Just(<$t>::MAX),
                        2 => Just(0 as $t),
                        2 => Just(1 as $t),
                        4 => Just(-1 as $t),
                        2 => Just(<$t>::MAX.saturating_sub(1)),
                        2 => Just(<$t>::MIN.saturating_add(1)),
                        12 => any::<$t>(),
                    ].boxed()
                }
            }
        )*
    };
}

impl_int_with_edges!(u8, u16, u32, u64, u128, usize);
impl_signed_with_edges!(i8, i16, i32, i64, i128, isize);

// `bool` and `char` keep their plain `any::<T>()` strategy
impl VcheckStrategy for bool {
    type Strategy = BoxedStrategy<bool>;
    fn vcheck_strategy() -> Self::Strategy {
        any::<bool>().boxed()
    }
}

impl VcheckStrategy for char {
    type Strategy = BoxedStrategy<char>;
    fn vcheck_strategy() -> Self::Strategy {
        any::<char>().boxed()
    }
}

// Float strategies. proptest's default `any::<f32>()` / `any::<f64>()`
// includes NaN / +inf / -inf / subnormals, which is exactly what users
// want when they're testing IEEE-aware contracts. We don't add extra
// edge biasing because `any::<f*>()` already covers the IEEE special
// values that drive most float bugs.
impl VcheckStrategy for f32 {
    type Strategy = BoxedStrategy<f32>;
    fn vcheck_strategy() -> Self::Strategy {
        any::<f32>().boxed()
    }
}
impl VcheckStrategy for f64 {
    type Strategy = BoxedStrategy<f64>;
    fn vcheck_strategy() -> Self::Strategy {
        any::<f64>().boxed()
    }
}

/// The unit type: one value, no bytes. Needed so container specs can be
/// instantiated at a zero-sized element type (`#[vcheck(T = ())]`), where
/// maximum-length containers are constructible in O(1) memory — the only
/// practical way to reach length-arithmetic boundaries like
/// `usize::MAX` in `Vec::append` / `VecDeque::append`.
impl VcheckStrategy for () {
    type Strategy = BoxedStrategy<()>;
    fn vcheck_strategy() -> Self::Strategy {
        use proptest::prelude::Just;
        Just(()).boxed()
    }
}

/// Counterexample-printing guard for sequence-shaped harness params.
///
/// proptest reports a failing case by `Debug`-formatting the sampled
/// value. `Vec`'s `Debug` walks every element, so a length-boundary ZST
/// vec (up to `usize::MAX` elements, from the ZST boundary strategy arm)
/// would print forever. Harness emission binds sequence-shaped params
/// through this wrapper — `VcheckSeqSample(v) in <strategy>.prop_map(VcheckSeqSample)`
/// — so the reported value's `Debug` is this one: for zero-sized element
/// types it prints `[<zst>; <len>]` (fully informative — ZST elements
/// carry no data, the length IS the value); for everything else it
/// delegates to the container's own `Debug`, keeping existing failure
/// output byte-identical.
pub struct VcheckSeqSample<C>(pub C);

/// The containers `VcheckSeqSample` knows how to bound-print.
pub trait VcheckSeqSampleFmt {
    fn fmt_bounded(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

impl<T: Debug> VcheckSeqSampleFmt for Vec<T> {
    fn fmt_bounded(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if std::mem::size_of::<T>() == 0 {
            return write!(f, "[<zst>; {}]", self.len());
        }
        Debug::fmt(self, f)
    }
}

impl<T: Debug> VcheckSeqSampleFmt for std::collections::VecDeque<T> {
    fn fmt_bounded(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if std::mem::size_of::<T>() == 0 {
            return write!(f, "[<zst>; {}]", self.len());
        }
        Debug::fmt(self, f)
    }
}

impl<C: VcheckSeqSampleFmt> Debug for VcheckSeqSample<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_bounded(f)
    }
}

/// Length-boundary lengths for zero-sized element types. A ZST `Vec`
/// stores only a length counter (`Vec::new()` already has capacity
/// `usize::MAX`), so these lengths cost no memory. Chosen so a PAIR of
/// independently drawn boundary lengths crosses `usize::MAX` — the
/// overflow class in `append`-style growth specs whose ensures have no
/// combined-length `requires`. Random sampling can never coordinate
/// these values; they must be seeded, like the scalar MIN/-1 seeds.
const ZST_BOUNDARY_LENS: [usize; 4] = [
    usize::MAX,
    usize::MAX - 1,
    usize::MAX / 2 + 1,
    DEFAULT_COLLECTION_MAX + 1,
];

/// True when `T` is a zero-sized, drop-free type — the class for which
/// length-boundary containers are O(1) memory and all values are
/// bit-identical. Shared gate for the boundary strategies and the
/// ZST-aware O(1) fast paths in the seq helpers below (`clone`, `==`,
/// and view materialization on a `usize::MAX`-length container would
/// otherwise loop 2^64 times in a debug build).
#[inline]
fn is_zst_no_drop<T>() -> bool {
    std::mem::size_of::<T>() == 0 && !std::mem::needs_drop::<T>()
}

/// Materialize a length-`len` ZST vec from a witness value.
///
/// Safety: only called when `is_zst_no_drop::<T>()`. For a zero-sized
/// `T`, `Vec::new()` has capacity `usize::MAX` and elements occupy no
/// storage, so `set_len(len)` exposes `len` copies of the
/// (bit-identical, drop-free) witness the strategy already produced.
fn zst_vec_with_len<T>(_witness: T, len: usize) -> Vec<T> {
    debug_assert!(is_zst_no_drop::<T>());
    let mut out = Vec::new();
    unsafe { out.set_len(len) };
    out
}

// Strategies for vec
impl<T: VcheckStrategy + Debug + 'static> VcheckStrategy for Vec<T>
where
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Vec<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        let small = vec(T::vcheck_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed();
        // Zero-sized, drop-free element types additionally sample
        // length-boundary vecs (see ZST_BOUNDARY_LENS). Weighted toward
        // the boundary: a pair of drawn containers should frequently
        // have a combined length crossing usize::MAX.
        if std::mem::size_of::<T>() == 0 && !std::mem::needs_drop::<T>() {
            let boundary = (T::vcheck_strategy(), proptest::sample::select(&ZST_BOUNDARY_LENS[..]))
                .prop_map(|(witness, len)| zst_vec_with_len(witness, len))
                .boxed();
            return proptest::prop_oneof![1 => small, 1 => boundary].boxed();
        }
        small
    }
}

impl<T: VcheckStrategy + Debug + 'static> VcheckStrategy for std::collections::VecDeque<T>
where
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<std::collections::VecDeque<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        // Generate a `Vec<T>` (bounded like the `Vec` strategy, including
        // the ZST length-boundary arm) and convert; `VecDeque::from(vec)`
        // preserves front-to-back order, reuses the buffer (O(1) for
        // ZSTs), and yields the empty deque for the empty vec.
        <Vec<T> as VcheckStrategy>::vcheck_strategy()
            .prop_map(std::collections::VecDeque::from)
            .boxed()
    }
}

impl<T: VcheckStrategy + Debug + 'static> VcheckStrategy for Option<T>
where
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Option<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        proptest::option::of(T::vcheck_strategy()).boxed()
    }
}

// `Result<T, E>` strategy: pick `Ok(t)` or `Err(e)` with equal weight.
// This mirrors `proptest::option::of` but proptest doesn't ship a
// `result::of` so we build it manually with `prop_oneof!`.
impl<T, E> VcheckStrategy for Result<T, E>
where
    T: VcheckStrategy + Debug + 'static,
    E: VcheckStrategy + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
    <E as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Result<T, E>>;
    fn vcheck_strategy() -> Self::Strategy {
        proptest::prop_oneof![
            T::vcheck_strategy().prop_map(Ok),
            E::vcheck_strategy().prop_map(Err),
        ]
        .boxed()
    }
}

impl<K, V> VcheckStrategy for HashMap<K, V>
where
    K: VcheckStrategy + Eq + Hash + Debug + 'static,
    V: VcheckStrategy + Debug + 'static,
    <K as VcheckStrategy>::Strategy: 'static,
    <V as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<HashMap<K, V>>;
    fn vcheck_strategy() -> Self::Strategy {
        // just recursively generate strategies for generics K and V
        hash_map(
            K::vcheck_strategy(),
            V::vcheck_strategy(),
            0..=DEFAULT_COLLECTION_MAX,
        )
        .boxed()
    }
}

impl<T> VcheckStrategy for HashSet<T>
where
    T: VcheckStrategy + Eq + Hash + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<HashSet<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        // just recursively generate strategy for generics T
        hash_set(T::vcheck_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed()
    }
}

impl<K, V> VcheckStrategy for std::collections::BTreeMap<K, V>
where
    K: VcheckStrategy + Ord + Debug + 'static,
    V: VcheckStrategy + Debug + 'static,
    <K as VcheckStrategy>::Strategy: 'static,
    <V as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<std::collections::BTreeMap<K, V>>;
    fn vcheck_strategy() -> Self::Strategy {
        // recurse
        proptest::collection::btree_map(
            K::vcheck_strategy(),
            V::vcheck_strategy(),
            0..=DEFAULT_COLLECTION_MAX,
        )
        .boxed()
    }
}

impl<T> VcheckStrategy for std::collections::BTreeSet<T>
where
    T: VcheckStrategy + Ord + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<std::collections::BTreeSet<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        // recurse
        proptest::collection::btree_set(T::vcheck_strategy(), 0..=DEFAULT_COLLECTION_MAX).boxed()
    }
}

/// `Box<T>`: sample the payload, box it. Primarily used by the
/// tracked-resource harnesses to drive permission
/// value types. i.e. these proptests might get touched by Miri
impl<T> VcheckStrategy for Box<T>
where
    T: VcheckStrategy + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<Box<T>>;

    fn vcheck_strategy() -> Self::Strategy {
        T::vcheck_strategy().prop_map(Box::new).boxed()
    }
}

impl VcheckStrategy for String {
    type Strategy = BoxedStrategy<String>;
    fn vcheck_strategy() -> Self::Strategy {
        any::<String>().boxed()
    }
}

// ---------------------------------------------------------------------------
// vstd::contrib::exec_spec::ExecMultiset<T> strategy
//
// Since this one lives in vstd, we need a helper module that consumers
// can opt into. The macro emits a manual `VcheckStrategy` impl for `ExecMultiset<T>`
// whenever a contract uses `Multiset<T>`. The helper here just exposes a strategy builder.

/// Our approach to creating a strategy is kind of funny, as we use
/// HashMap as a bootstrap for ExecMultiset such that we don't have to know
/// about the `vstd` types at runtime.
pub fn multiset_inner_strategy<T>(count_max: u32) -> BoxedStrategy<HashMap<T, usize>>
where
    T: VcheckStrategy + Eq + Hash + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    hash_map(
        T::vcheck_strategy(),
        0usize..=count_max as usize,
        0..=DEFAULT_COLLECTION_MAX,
    )
    .boxed()
}

// In general, we also provide exec helpers for spec-level functions such as
// `Seq::update`. In general, keeping these as free functions, rather than inlining
// them into blocks, makes the rewritten contract call _flat_. This is nicer for
// creating proptest blocks.

// Sequence-update helper used by the harness contract rewriter for
// `Seq::update` lowering.
#[doc(hidden)]
pub fn __vcheck_seq_update<T>(mut v: Vec<T>, i: usize, x: T) -> Vec<T> {
    v[i] = x;
    v
}

// String-to-Vec<char> bridge used by the harness contract rewriter for
// `&str` / `String` deep_view.
#[doc(hidden)]
pub fn __vcheck_str_chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

// String-to-bytes bridge. Verus's `str`-side specs call
// `s.spec_bytes()`, an uninterp spec fn returning `Seq<u8>`. At
// runtime that's just the UTF-8 byte slice. The engine lowers
// `s.spec_bytes()` to `__vcheck_str_bytes(&s).as_slice()` (a `Seq<u8>`-
// shaped value in the slice path), so contracts like
// `len == s.spec_bytes().len()` evaluate correctly.
#[doc(hidden)]
pub fn __vcheck_str_bytes(s: &str) -> &[u8] {
    s.as_bytes()
}

// Slice-concat helper used by the harness contract rewriter for the
// `seq + seq` Verus form (which lowers to `Vec<T>` concatenation in the
// runtime form). Cloning is required because the underlying values flow
// from `&[T]` slice projections.
//
// Accepts anything sliceable (`AsRef<[T]>`) on both sides so it works for
// slice operands (the `seq + seq` form, where both are `&[T]` projections)
// AND for a by-value `Vec` operand produced by a `seq![x]` literal in
// `+` position (the `seq![value] + old@` front-insertion form used by
// `VecDeque::push_front`). `&[T]`, `Vec<T>`, and `&Vec<T>` all implement
// `AsRef<[T]>`, so every existing call site keeps compiling.
#[doc(hidden)]
pub fn __vcheck_seq_concat<T: Clone>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> Vec<T> {
    let (a, b) = (a.as_ref(), b.as_ref());
    // ZST fast path. Also necessary for correctness, not just speed:
    // with length-boundary ZST vecs in play (see ZST_BOUNDARY_LENS) the
    // combined spec-level length can exceed usize::MAX, which
    // `Vec::with_capacity(a.len() + b.len())` can't represent (debug:
    // add overflow panic). A saturated-length vec keeps the eq check
    // meaningful: the true concat length > usize::MAX can never equal
    // any real container's length, and `__vcheck_seq_eq` compares lengths
    // first.
    if is_zst_no_drop::<T>() {
        if let Some(w) = a.first().or_else(|| b.first()) {
            return zst_vec_with_len(w.clone(), a.len().saturating_add(b.len()));
        }
        return Vec::new();
    }
    let mut out = Vec::with_capacity(a.len() + b.len());
    out.extend_from_slice(a);
    out.extend_from_slice(b);
    out
}

// Sequence equality used by the harness contract rewriter for `==`/`!=`
// between sequence views (`final(v)@ == old(v)@ + old(other)@`). Plain
// slice `PartialEq` walks every element; for zero-sized element types the
// boundary strategies produce lengths near `usize::MAX` and the walk
// never terminates in a debug build. All values of a drop-free ZST are
// bit-identical, so comparing one representative pair after the length
// check is exhaustive (an impure `PartialEq` on a ZST is out of scope).
#[doc(hidden)]
pub fn __vcheck_seq_eq<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    let (a, b) = (a.as_ref(), b.as_ref());
    if a.len() != b.len() {
        return false;
    }
    if std::mem::size_of::<T>() == 0 {
        return match (a.first(), b.first()) {
            (Some(x), Some(y)) => x == y,
            _ => true, // both empty
        };
    }
    a == b
}

// Contiguous-`Vec` materialization of a `VecDeque`'s logical front-to-back
// order. `VecDeque` has no `as_slice()` (ring buffer), so the harness
// contract rewriter routes every `<deque>@` view through this helper and
// then `.as_slice()`s the result — mirroring how `__vcheck_str_chars` bridges
// `&str`/`String` to a `Vec<char>`.
#[doc(hidden)]
pub fn __vcheck_vecdeque_slice<T: Clone>(v: &std::collections::VecDeque<T>) -> Vec<T> {
    // ZST fast path: `iter().cloned().collect()` walks every element,
    // which never terminates for the length-boundary deques the ZST
    // strategies produce. Bit-identical drop-free elements replicate in
    // O(1) instead.
    if is_zst_no_drop::<T>() {
        return match v.front() {
            Some(w) => zst_vec_with_len(w.clone(), v.len()),
            None => Vec::new(),
        };
    }
    v.iter().cloned().collect()
}

// O(1)-for-ZST snapshot of a `&mut VecDeque` param's pre-call state.
// `VecDeque::clone` walks elements one by one (no `Copy` memcpy
// specialization like `Vec`'s), so cloning a length-boundary ZST deque
// hangs. Routed here by the harness's pre-state snapshot emission.
#[doc(hidden)]
pub fn __vcheck_vecdeque_snapshot<T: Clone>(
    v: &std::collections::VecDeque<T>,
) -> std::collections::VecDeque<T> {
    if is_zst_no_drop::<T>() {
        return match v.front() {
            Some(w) => std::collections::VecDeque::from(zst_vec_with_len(w.clone(), v.len())),
            None => std::collections::VecDeque::new(),
        };
    }
    v.clone()
}

// Sequence-push helper used by the harness contract rewriter for the
// `Seq::push` method form.
#[doc(hidden)]
pub fn __vcheck_seq_push<T>(mut v: Vec<T>, x: T) -> Vec<T> {
    v.push(x);
    v
}

// Sequence element accessors / structural ops used by the harness contract
// rewriter for `Seq::last`, `Seq::first`, and `Seq::drop_last`.
//
// `Seq::last` / `Seq::first` return the ELEMENT (`T`), matching Verus's spec
// signatures — not `Option<&T>` like the inherent slice methods. The contract
// context guarantees non-emptiness (these only appear where the spec's
// requires established `len > 0`), so an out-of-bounds access here surfaces
// as a clear failure rather than passing vacuously.
#[doc(hidden)]
pub fn __vcheck_seq_last<T>(mut v: Vec<T>) -> T {
    v.pop().expect("verus_spec_check: Seq::last on empty sequence")
}

#[doc(hidden)]
pub fn __vcheck_seq_first<T>(v: Vec<T>) -> T {
    v.into_iter()
        .next()
        .expect("verus_spec_check: Seq::first on empty sequence")
}

#[doc(hidden)]
pub fn __vcheck_seq_drop_last<T>(mut v: Vec<T>) -> Vec<T> {
    v.pop();
    v
}

// `Seq::insert(i, x)` (shift-right insertion) and `Seq::remove(i)`
// (shift-left removal).
// A future Set/Map harness that used `insert`/`remove` on a viewed collection
// would need receiver-shape-aware routing; collection specs are not currently
// harnessed, so there is no live collision.
#[doc(hidden)]
pub fn __vcheck_seq_insert<T>(mut v: Vec<T>, i: usize, x: T) -> Vec<T> {
    v.insert(i, x);
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_remove<T>(mut v: Vec<T>, i: usize) -> Vec<T> {
    v.remove(i);
    v
}

// `Seq::contains(x)` — membership, element taken BY VALUE (Verus's spec
// signature), unlike the inherent slice `.contains(&T)`. Without this arm the
// rewriter used to leak a raw `.contains(x)` method call onto the lowered
// slice, where std's `&T`-taking method won and the harness failed to
// typecheck (`expected &T, found T`). Same name-shadowing class as
// `last`/`first` above. Accepts `AsRef<[T]>` so both slice projections and
// owned `Vec` operands work.
#[doc(hidden)]
pub fn __vcheck_seq_contains<T: PartialEq>(v: impl AsRef<[T]>, x: T) -> bool {
    v.as_ref().iter().any(|e| *e == x)
}

// `Seq::to_set()` — materialize distinct sequence elements as a runtime
// `HashSet`, matching the finite extensional semantics of vstd's `Set`.
#[doc(hidden)]
pub fn __vcheck_seq_to_set<T>(v: impl AsRef<[T]>) -> HashSet<T>
where
    T: Clone + Eq + Hash,
{
    v.as_ref().iter().cloned().collect()
}

// `Set::map(f)` — apply a value-taking spec closure to every finite-set
// element and collect the image. Cloning bridges HashSet iteration (`&T`) to
// Verus's value-taking `Set::map` closure.
#[doc(hidden)]
pub fn __vcheck_set_map<T, U, F>(set: &HashSet<T>, f: F) -> HashSet<U>
where
    T: Clone + Eq + Hash,
    U: Eq + Hash,
    F: Fn(T) -> U,
{
    set.iter().cloned().map(f).collect()
}

// Current-vstd `IteratorSpec::remaining().unref()` — return the suffix of the
// sampled iteration order beginning at the sampled pre-call cursor.
#[doc(hidden)]
pub fn __vcheck_iter_remaining<'a, T>(state: (i64, &'a [T])) -> &'a [T] {
    &state.1[state.0 as usize..]
}

// `Seq::reverse()` — returns the reversed sequence (a NEW value, matching
// Verus's spec signature), unlike the inherent `[T]::reverse` / `Vec::reverse`
// which mutate in place and return `()`.
#[doc(hidden)]
pub fn __vcheck_seq_reverse<T>(mut v: Vec<T>) -> Vec<T> {
    v.reverse();
    v
}

// `Seq::is_prefix_of` / `Seq::is_suffix_of` — `a.is_prefix_of(b)` holds when
// `b` begins with `a`. No inherent slice method shadows these; they simply had
// no exec lowering before (E0599 in generated harnesses).
#[doc(hidden)]
pub fn __vcheck_seq_is_prefix_of<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    b.as_ref().starts_with(a.as_ref())
}

#[doc(hidden)]
pub fn __vcheck_seq_is_suffix_of<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    b.as_ref().ends_with(a.as_ref())
}

// ---------------------------------------------------------------------------
// BTreeMap / BTreeSet exec companions.
//
// `BTreeMap<K,V>` / `BTreeSet<K>` share the exact `Map`/`Set` view surface as
// their Hash counterparts, so the contract rewriter routes their view-ops to
// the same `exec_get` / `exec_insert` / `exec_remove` method names. We can't
// reuse the `verus_spec_check_vstd_ext` `ExecSpec*` companions for BTree, though:
// those require a `vstd::DeepView` supertrait, and vstd only provides
// `DeepView for BTreeMap`/`BTreeSet` inside its ghost-gated `std_specs`
// module (absent under plain `cargo test`), whereas `DeepView for HashMap`
// lives in the always-compiled `vstd::view`. Orphan rules block us from
// filling that gap in `verus_spec_check_vstd_ext`.
//
// Instead we provide dedicated extension traits here (no vstd dependency,
// mirroring the `__vcheck_vecdeque_slice` escape hatch). Method resolution is
// unambiguous because these impls are for `&BTreeMap` / `&BTreeSet`, disjoint
// from the vstd_ext impls on `&HashMap` / `&HashSet`. Both trait families are
// in scope in the generated harness (`use super::*` + `use
// ::verus_spec_check_vstd_ext::*`), and only one applies to any given receiver.
//
// Each functional op clones the receiver and applies the real std mutation,
// returning an owned collection; the rewriter wraps mutation results in `&`
// so `<map>@ == <op>` compares `&BTreeMap == &BTreeMap` via BTree's
// (order-independent) `PartialEq`.

/// Owned-value normalizer for `Map::index` results. The two map
/// carriers disagree on what their `exec_index` returns, the vstd_ext
/// `HashMap` companion yields `&V`, the `VcheckBTreeMapExec` companion
/// yields owned `V`, so the contract rewriter routes `m@[k]` through
/// this trait to land on an owned `V` either way. The two impls don't
/// overlap: `(Self = &T, Target = T)` and `(Self = X, Target = X)`
/// would coincide only at the infinite type `T = &T`.
pub trait VcheckMapIndexOwned<T> {
    fn vcheck_owned(self) -> T;
}

impl<T: Clone> VcheckMapIndexOwned<T> for T {
    #[inline(always)]
    fn vcheck_owned(self) -> T {
        self
    }
}

impl<T: Clone> VcheckMapIndexOwned<T> for &T {
    #[inline(always)]
    fn vcheck_owned(self) -> T {
        self.clone()
    }
}

/// `exec_*` companions for `Map`-viewed `BTreeMap`.
pub trait VcheckBTreeMapExec<K, V> {
    /// Functional `Map::insert`.
    fn exec_insert(self, key: K, value: V) -> std::collections::BTreeMap<K, V>;
    /// Functional `Map::remove`.
    fn exec_remove(self, key: K) -> std::collections::BTreeMap<K, V>;
    /// `Map::get` -> owned `Option<V>`.
    fn exec_get(self, key: K) -> Option<V>;
    /// `Map::index` -> owned `V`. Panics on an absent key — the contract
    /// context precludes it (`contains_key` guards), so a panic here is a
    /// genuine spec-evaluation failure signal.
    fn exec_index(self, key: K) -> V;
}

impl<K: Ord + Clone, V: Clone> VcheckBTreeMapExec<K, V> for &std::collections::BTreeMap<K, V> {
    #[inline(always)]
    fn exec_insert(self, key: K, value: V) -> std::collections::BTreeMap<K, V> {
        let mut m = self.clone();
        let _ = m.insert(key, value);
        m
    }

    #[inline(always)]
    fn exec_remove(self, key: K) -> std::collections::BTreeMap<K, V> {
        let mut m = self.clone();
        let _ = m.remove(&key);
        m
    }

    #[inline(always)]
    fn exec_get(self, key: K) -> Option<V> {
        self.get(&key).cloned()
    }

    #[inline(always)]
    fn exec_index(self, key: K) -> V {
        self.get(&key)
            .cloned()
            .expect("verus_spec_check: Map::index on an absent key (contract evaluation)")
    }
}

/// `exec_*` companions for `Set`-viewed `BTreeSet`.
pub trait VcheckBTreeSetExec<K> {
    /// Functional `Set::insert`.
    fn exec_insert(self, elem: K) -> std::collections::BTreeSet<K>;
    /// Functional `Set::remove`.
    fn exec_remove(self, elem: K) -> std::collections::BTreeSet<K>;
}

impl<K: Ord + Clone> VcheckBTreeSetExec<K> for &std::collections::BTreeSet<K> {
    #[inline(always)]
    fn exec_insert(self, elem: K) -> std::collections::BTreeSet<K> {
        let mut s = self.clone();
        let _ = s.insert(elem);
        s
    }

    #[inline(always)]
    fn exec_remove(self, elem: K) -> std::collections::BTreeSet<K> {
        let mut s = self.clone();
        let _ = s.remove(&elem);
        s
    }
}

#[cfg(test)]
mod zst_strategy_tests {
    use super::*;
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

    fn sample_lens<T: VcheckStrategy + Debug + 'static>(n: usize) -> Vec<usize>
    where
        <T as VcheckStrategy>::Strategy: 'static,
        T: Clone,
    {
        let mut runner = TestRunner::deterministic();
        let strategy = <Vec<T> as VcheckStrategy>::vcheck_strategy();
        (0..n)
            .map(|_| strategy.new_tree(&mut runner).unwrap().current().len())
            .collect()
    }

    /// ZST element vecs must sample BOTH small lengths and the
    /// usize::MAX-class boundary lengths; a drawn pair must be able to
    /// cross usize::MAX combined length (the append-overflow class).
    #[test]
    fn zst_vec_strategy_reaches_length_boundaries() {
        let lens = sample_lens::<()>(64);
        assert!(
            lens.iter().any(|&l| l <= DEFAULT_COLLECTION_MAX),
            "no small lengths sampled: {lens:?}"
        );
        assert!(
            lens.iter().any(|&l| l == usize::MAX),
            "usize::MAX never sampled: {lens:?}"
        );
        assert!(
            lens.iter().any(|&l| l == usize::MAX / 2 + 1),
            "half-max never sampled (pairs must cross usize::MAX): {lens:?}"
        );
    }

    /// Sized element types must be completely unaffected by the ZST arm.
    #[test]
    fn sized_vec_strategy_stays_bounded() {
        let lens = sample_lens::<u32>(64);
        assert!(
            lens.iter().all(|&l| l <= DEFAULT_COLLECTION_MAX),
            "sized element type sampled an out-of-bound length: {lens:?}"
        );
    }

    /// The boundary lengths flow through the VecDeque strategy (From<Vec>
    /// reuses the buffer, so this stays O(1) for ZSTs).
    #[test]
    fn zst_vecdeque_strategy_reaches_length_boundaries() {
        let mut runner = TestRunner::deterministic();
        let strategy = <std::collections::VecDeque<()> as VcheckStrategy>::vcheck_strategy();
        let lens: Vec<usize> = (0..64)
            .map(|_| strategy.new_tree(&mut runner).unwrap().current().len())
            .collect();
        assert!(lens.iter().any(|&l| l == usize::MAX), "MAX missing: {lens:?}");
        assert!(lens.iter().any(|&l| l <= DEFAULT_COLLECTION_MAX));
    }

    /// The concrete finding this feature exists for: a sampled ZST pair
    /// whose combined length exceeds usize::MAX makes real
    /// `Vec::append` panic ("capacity overflow") while the trusted vstd
    /// ensures describes the impossible sum. Checked directly here so
    /// the engine-level capability is pinned even before vstd carries a
    /// `#[vcheck(T = ())]` annotation.
    #[test]
    fn zst_append_boundary_pair_panics() {
        let mut a = zst_vec_with_len((), usize::MAX);
        let mut b = zst_vec_with_len((), 1);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            a.append(&mut b);
        }));
        assert!(
            outcome.is_err(),
            "Vec::append at combined length usize::MAX + 1 must panic"
        );
    }

    /// Every helper the label-generated harness touches on the huge-ZST
    /// path must be O(1): view materialization, pre-state snapshot,
    /// concat, equality, and counterexample printing. Each of these
    /// walks elements in its generic form and would loop 2^64 times.
    #[test]
    fn zst_boundary_helpers_terminate() {
        let half = usize::MAX / 2 + 1;
        let a = zst_vec_with_len((), half);
        let b = zst_vec_with_len((), 17);

        // seq equality: lengths first, then one representative pair.
        assert!(__vcheck_seq_eq(&a, &zst_vec_with_len((), half)));
        assert!(!__vcheck_seq_eq(&a, &b));

        // concat: saturated ZST replication, no element walk.
        let c = __vcheck_seq_concat(&a, &b);
        assert_eq!(c.len(), half + 17);
        let sat = __vcheck_seq_concat(&zst_vec_with_len((), usize::MAX), &b);
        assert_eq!(sat.len(), usize::MAX, "combined length saturates");

        // VecDeque view + snapshot.
        let d: std::collections::VecDeque<()> = std::collections::VecDeque::from(a);
        assert_eq!(__vcheck_vecdeque_slice(&d).len(), half);
        assert_eq!(__vcheck_vecdeque_snapshot(&d).len(), half);

        // Counterexample printing: bounded and informative.
        let printed = format!("{:?}", VcheckSeqSample(zst_vec_with_len((), usize::MAX)));
        assert_eq!(printed, format!("[<zst>; {}]", usize::MAX));
        let printed = format!("{:?}", __vcheck_vecdeque_snapshot(&d).len());
        assert!(!printed.is_empty());
        // Non-ZST output stays byte-identical to Vec's own Debug.
        assert_eq!(format!("{:?}", VcheckSeqSample(vec![1u8, 2, 3])), "[1, 2, 3]");
    }
}
