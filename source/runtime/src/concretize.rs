//! `VcheckConcretize` — the developer-supplied bridge that lets `#[vcheck]`
//! property-test specifications written over an **abstract/opaque type** with
//! an **uninterpreted view**.
//!
//! ## The problem
//!
//! Specs like alerus's `extern_spec.rs` state their contracts over a ghost
//! view of an opaque foreign type:
//!
//! ```ignore
//! pub uninterp spec fn ubig_view(n: &UBig) -> nat;
//!
//! pub assume_specification[ random::ubig_add ](a: &UBig, b: &UBig) -> (ret: UBig)
//!     ensures ubig_view(&ret) == ubig_view(a) + ubig_view(b);
//! ```
//!
//! The engine can't run this directly: `UBig` is opaque (no way to sample a
//! value) and `ubig_view` is `uninterp` (no executable meaning). Neither is
//! recoverable from the spec text — it's irreducible semantic knowledge the
//! developer holds.
//!
//! ## The bridge
//!
//! The developer supplies that knowledge exactly once per opaque type via
//! this trait:
//!
//! ```ignore
//! impl VcheckConcretize for UBig {
//!     type Sample = u32;
//!     fn vcheck_inject(s: u32) -> UBig { random::ubig_from_u64(s as u64) }
//!     fn vcheck_realize(&self) -> SpecInt { /* UBig -> BigInt */ }
//! }
//! ```
//!
//! and marks the view fn with `#[vcheck_view]`. The `#[vcheck]` engine then, for
//! *every* operation over `UBig`, auto-generates a harness that:
//!
//! 1. samples a `Sample` value (which has a generator),
//! 2. injects it to an owned `UBig` via [`VcheckConcretize::vcheck_inject`],
//! 3. calls the real operation, and
//! 4. rewrites each `ubig_view(x)` in the contract to
//!    [`VcheckConcretize::vcheck_realize`]`(x)`, evaluating the (now executable)
//!    contract in the unbounded [`SpecInt`] domain.
//!
//! No per-operation wrapper is ever hand-written.

use crate::spec_int::SpecInt;

/// The bridge from a sampleable primitive domain into an opaque type, plus an
/// executable realization of that type's abstract view.
///
/// Implement once per opaque type whose specs you want to property-test. The
/// associated `Sample` type is what the harness actually samples; it must have
/// a generator for the active backend (`VcheckGen` for bolero, `VcheckStrategy` for
/// proptest). The engine emits the generator call using the fully-associated
/// path `<Self::Sample as ...>::...`, so it never needs to name the concrete
/// `Sample` type.
pub trait VcheckConcretize: Sized {
    /// The primitive (or otherwise directly-sampleable) domain the harness
    /// samples from. Bounded by `Clone + Debug` so the harness can hold and
    /// report sampled values; the per-backend generator bound is enforced at
    /// the emitted call site, not here (keeping this trait backend-agnostic).
    type Sample: Clone + core::fmt::Debug;

    /// Map a sampled value into an owned instance of the opaque type.
    fn vcheck_inject(sample: Self::Sample) -> Self;

    /// Realize the type's abstract view as an executable, unbounded
    /// mathematical integer. This is the concrete meaning of the `#[vcheck_view]`
    /// spec fn (e.g. `ubig_view`). Because it returns a [`SpecInt`], contract
    /// arithmetic (`+`/`-`/`*`) composes losslessly with no overflow bounds.
    fn vcheck_realize(&self) -> SpecInt;
}
