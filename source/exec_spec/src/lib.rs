//! `verus-spec-check-exec-spec`: the spec-to-exec lowering pass
//! (`exec_spec_unverified!` / `exec_spec_verified!`) split out of the
//! engine so `verus_spec_check_attr` / `verus_spec_check_expand` / the
//! `verus_builtin_macros` overlay can share one implementation.
//!
//! This is an internal crate of the verus-spec-check family; it makes no
//! stability guarantees. Use the `verus_spec_check` umbrella crate instead.

// Alias so the module body's original `crate::syntax::*` paths keep
// resolving after the split out of `verus_spec_check_engine`.
use verus_spec_check_syntax::syntax;

mod exec_spec;
pub use exec_spec::*;

#[cfg(test)]
mod tests;
