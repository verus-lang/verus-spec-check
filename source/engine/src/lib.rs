//! `verus-spec-check-engine`: the stable facade over the vcheck engine crates,
//! exposed as plain library functions so Verus's contrib pipeline
//! (which can't depend on a proc-macro crate from a non-proc-macro
//! position) can drive the folding pass.
//!
//! The implementation lives in dedicated crates:
//!
//! - `verus_spec_check_attr`: `#[vcheck]` / `#[vcheck_provide]` preprocessing.
//! - `verus_spec_check_expand`: `verus_spec_check_unverified!` / `_verified!` expansion.
//! - `verus_spec_check_exec_spec`: spec-to-exec lowering.
//! - `verus_spec_check_external_provide`: `external_vcheck_provide!` companions.
//! - `verus_spec_check_assert`: inline `#[vcheck] assert(...)` handling.
//! - `verus_spec_check_mutator`: `#[vcheck_cov_mutate]` mutation sites.
//! - `verus_spec_check_instrument`: `#[vcheck_cov_fuzz]` branch instrumentation.
//! - `verus_spec_check_syntax`: forked Verus helpers (`Vstd`, `vstd_kind`).
//!
//! This crate keeps the public surface (and the `path = "../engine"`
//! location that downstream `[patch.crates-io]` users pin) stable:
//!
//! - [`vcheck_provide_preprocess`]: whole-block folding pass invoked
//!   from Verus's `contrib_preprocess_items`.
//! - [`expand_verus_spec_check`]: expand a `verus_spec_check_unverified!` /
//!   `verus_spec_check_verified!` invocation. Called from the proc-macro
//!   wrapper in `verus-spec-check-macros`.
//! - [`expand_exec_spec`]: expand an `exec_spec_unverified!` /
//!   `exec_spec_verified!` invocation (used by the
//!   `verus_builtin_macros` overlay).
//! - [`compile_error_external_vcheck_provide`]: produce the diagnostic
//!   for `external_vcheck_provide!` outside `verus!{}`.

use proc_macro2::TokenStream;

// Re-exported for consumers that use `verus_spec_check_engine::*`
pub use verus_spec_check_expand::pretty_tokens;
pub use verus_spec_check_syntax::vstd_kind;

/// The top-level whole-block folding pass for verus-spec-check attributes;
/// passes created blocks into `verus_spec_check_unverified!`
pub fn vcheck_provide_preprocess(items: &mut Vec<verus_syn::Item>) {
    verus_spec_check_attr::vcheck_provide_preprocess(items);
}

/// Expand a `verus_spec_check_unverified!` / `verus_spec_check_verified!`
/// invocation. The `verified` flag picks the engine flavor.
///
/// Both input and output are `proc_macro2::TokenStream`. The proc-macro
/// wrapper in `verus-spec-check-macros` converts to/from
/// `proc_macro::TokenStream` at the entry point.
pub fn expand_verus_spec_check(input: TokenStream, verified: bool) -> TokenStream {
    verus_spec_check_expand::expand(input, verified)
}

/// Expand an `exec_spec_unverified!` / `exec_spec_verified!`
/// invocation. The `unverified` flag picks the engine flavor.
pub fn expand_exec_spec(input: TokenStream, unverified: bool) -> TokenStream {
    verus_spec_check_exec_spec::exec_spec(input, unverified)
}

/// Produce the `compile_error!` diagnostic for `external_vcheck_provide!`
/// when expanded outside a `verus!{}` block
pub fn compile_error_external_vcheck_provide() -> TokenStream {
    let msg = "external_vcheck_provide! must be used inside a `verus! { ... }` block, \
               alongside the `#[vcheck]` function whose contract references the provided \
               spec fn(s); it is consumed by the #[vcheck] preprocessing pass and has no \
               effect on its own";
    quote::quote! { compile_error!(#msg); }
}
