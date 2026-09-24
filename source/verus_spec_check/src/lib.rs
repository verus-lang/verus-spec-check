//! `verus_spec_check`: property-based testing for Verus.
//!
//! This is the user-facing umbrella crate that bundles everything
//! needed to run vcheck against a stock verus distribution. This includes:
//!
//! - Proc macros: (`verus_spec_check_unverified!`, `verus_spec_check_verified!`,
//!   `external_vcheck_provide!`, `#[vcheck]`, `#[vcheck_provide]`,
//!   `#[vcheck_cov_mutate]`, `#[vcheck_cov_fuzz]`) -- re-exported from
//!   `verus_spec_check_macros`.
//! - vcheck Runtime (`VcheckStrategy`, `vcheck_strategy`, `ToExecModel`,
//!   `cov_mutate::*`, `cov_fuzz::*`, the `proptest` re-export) --
//!   re-exported from `verus_spec_check_runtime`.
//! - vstd-side exec_spec types (`ExecSpecType`, `ToRef`, `ToOwned`,
//!   `DeepViewClone`, `ExecSpecEq`, `ExecSpecIndex`, `ExecSpecLen`,
//!   plus the `ExecMultiset` / Set / Map / Option helpers) -- defined in
//!   `verus_spec_check_vstd_ext` and used by the engine's emitted harness code.
//!
//! If you do not want to use the umbrella, you can just do:
//!
//! ```ignore
//! use verus_spec_check_macros::*;
//! use verus_spec_check_runtime::*;
//! ```
//! We re-export the vstd-side exec_spec types so source code that
//! uses verus_spec_check::* gets them for free. `::verus_spec_check_vstd_ext` is emitted,
//! so the user requires vstd_ext as a top-level dependency.

pub use verus_spec_check_macros::*;
pub use verus_spec_check_runtime::*;
pub use verus_spec_check_vstd_ext;
