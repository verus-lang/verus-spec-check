//! Forked from `verus-lang/verus/source/builtin_macros/src/syntax.rs`
//! (just the `Vstd` resolver -- about line 5624 in the snapshot at
//! migration time).
//!
//! ## What this provides
//!
//! `Vstd(span)` is a `ToTokens` impl that emits the right path prefix
//! to reach `vstd::*` from whatever crate the macro is expanding into.
//! The path varies based on `vstd_kind()`:
//!
//! - `IsVstd`         -> `crate`           (current crate IS vstd)
//! - `NoVstd`         -> `::vstd`          (error case; emitted anyway)
//! - `Imported`       -> `::vstd`          (normal case)
//! - `IsCore`         -> `crate::vstd`     (verifying core)
//! - `ImportedViaCore` -> `::core::vstd`
//!
//! vcheck-internal callers use it like
//! `let vstd = crate::syntax::Vstd(span); quote! { #vstd::contrib::... }`.

use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote_spanned;
use quote::ToTokens;

use crate::vstd_kind::{vstd_kind, VstdKind};

/// Token-level placeholder that resolves to `vstd`'s path prefix.
pub struct Vstd(pub Span);

impl ToTokens for Vstd {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // If this is called for NoVstd, it is of course an error, but we just emit the
        // vstd identifier and let Rust complain about it later.
        let toks = match vstd_kind() {
            VstdKind::IsVstd => quote_spanned! { self.0 => crate },
            VstdKind::NoVstd => quote_spanned! { self.0 => ::vstd },
            VstdKind::Imported => quote_spanned! { self.0 => ::vstd },
            VstdKind::IsCore => quote_spanned! { self.0 => crate::vstd },
            VstdKind::ImportedViaCore => quote_spanned! { self.0 => ::core::vstd },
        };
        tokens.extend(toks);
    }
}

/// Convenience macro forked from
/// `verus/source/builtin_macros/src/syntax.rs` (around line 243).
/// Wraps a `quote!{}` block so the inner template can reference
/// `#vstd` and have it resolve to the right `vstd::*` qualifier.
///
/// Usage:
/// ```ignore
/// let ts = quote_vstd! { vstd =>
///     #vstd::prelude::verus! { ... }
/// };
/// ```
#[macro_export]
macro_rules! quote_vstd {
    ($b:ident => $($tt:tt)*) => {
        {
            let sp = ::proc_macro2::Span::call_site();
            let $b = $crate::syntax::Vstd(sp);
            ::quote::quote!{ $($tt)* }
        }
    }
}
