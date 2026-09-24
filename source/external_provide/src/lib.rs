//! `verus-spec-check-external-provide`: parsing and companion synthesis for
//! `external_vcheck_provide!` blocks (trusted exec twins of spec fns
//! defined outside the current `verus!{}` block).
//!
//! This is an internal crate of the verus-spec-check family; it makes no
//! stability guarantees. Use the `verus_spec_check` umbrella crate instead.

// Alias so the module body's original `crate::exec_spec::*` paths keep
// resolving after the split out of `verus_spec_check_engine`.
use verus_spec_check_exec_spec as exec_spec;

mod external_vcheck_provide;
pub use external_vcheck_provide::*;
