//! `verus-spec-check-external-provide`: parsing and companion synthesis for
//! `external_vcheck_provide!` blocks (trusted exec twins of spec fns
//! defined outside the current `verus!{}` block).
//!
//! This is an internal crate of the verus-spec-check family; it makes no
//! stability guarantees. Use the `verus_spec_check` umbrella crate instead.

mod external_vcheck_provide;
pub use external_vcheck_provide::*;
