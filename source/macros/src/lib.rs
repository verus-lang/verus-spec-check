//! `verus-spec-check-macros`: thin proc-macro wrapper around the engine
//! defined in the sibling `engine` crate.
//!
//! Why split: a `proc-macro = true` crate cannot export `pub fn` items
//! that aren't proc macros. Verus's contrib pipeline needs to call
//! `vcheck_provide_preprocess` as a regular function, so the engine logic
//! must live in a non-proc-macro crate. This crate is the proc-macro
//! face of the engine.
//!
//! ## Public surface
//!
//! - `verus_spec_check_unverified!` / `verus_spec_check_verified!`: proc macros
//!   that emit a proptest harness alongside the user's items.
//! - `external_vcheck_provide!`: create trusted exec stubs for specs
//! - `#[vcheck]`, `#[vcheck_provide]`, `#[vcheck_cov_mutate]`, `#[vcheck_cov_fuzz]`:
//!    pass-through attribute markers (the actual processing happens in
//!   `verus_spec_check_engine::vcheck_provide_preprocess`, called from Verus's
//!   `contrib_preprocess_items` pipeline).

use proc_macro::TokenStream;

#[proc_macro]
pub fn verus_spec_check_unverified(input: TokenStream) -> TokenStream {
    verus_spec_check_engine::expand_verus_spec_check(input.into(), /*verified=*/ false).into()
}

#[proc_macro]
pub fn verus_spec_check_verified(input: TokenStream) -> TokenStream {
    verus_spec_check_engine::expand_verus_spec_check(input.into(), /*verified=*/ true).into()
}

#[proc_macro]
pub fn external_vcheck_provide(_input: TokenStream) -> TokenStream {
    verus_spec_check_engine::compile_error_external_vcheck_provide().into()
}

#[proc_macro_attribute]
pub fn vcheck(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}

#[proc_macro_attribute]
pub fn vcheck_provide(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}

/// `#[vcheck_view]` marks an `uninterp spec fn view(x: &T) -> nat/int` as the
/// executable view of an opaque type `T` that implements `VcheckConcretize`.
/// The actual handling happens in `verus_spec_check_engine::vcheck_provide_preprocess`;
/// this is a pass-through marker (like `#[vcheck]`).
#[proc_macro_attribute]
pub fn vcheck_view(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}

#[proc_macro_attribute]
pub fn vcheck_cov_mutate(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}

#[proc_macro_attribute]
pub fn vcheck_cov_fuzz(_args: TokenStream, input: TokenStream) -> TokenStream {
    input
}
