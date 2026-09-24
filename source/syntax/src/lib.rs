//! `verus-spec-check-syntax`: two short helpers forked from upstream Verus
//! internals, shared by the verus-spec-check engine crates:
//!
//! - [`syntax::Vstd`] -- emits the right `vstd::*` path qualifier.
//! - [`vstd_kind::vstd_kind`] -- detects the build mode (env-var driven).
//! - [`quote_vstd!`] -- `quote!{}` wrapper that binds `#vstd` to the
//!   resolved qualifier.

pub mod syntax;
pub mod vstd_kind;
