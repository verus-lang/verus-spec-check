#![cfg(all(feature = "alloc", feature = "std"))]

// `verus!` macros need this in scope to expand. We do not re-export.
extern crate vstd;

pub mod exec_spec;
pub mod resource;

// Flat re-export of every `pub` item under `exec_spec` so the engine's
// `::verus_spec_check_vstd_ext::ExecSpecType` paths resolve.
pub use exec_spec::*;
