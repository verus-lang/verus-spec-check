//! Forked from `verus-lang/verus/source/builtin_macros/src/lib.rs` (the
//! `VstdKind` enum and `vstd_kind()` function).
//!
//! ## What this provides
//!
//! Build-mode detection for the vcheck engine. vcheck short-circuits expansion
//! in special build modes (e.g. when verifying `core` itself, or when
//! `vstd` is unavailable). The original Verus code reads env vars and
//! cfg flags at static-init time, and this fork reproduces the env-var
//! reads.
//!
//! ## Differences from upstream
//!
//! - `pub` instead of `pub(crate)` so the engine modules and the proc-
//!   macro wrapper can use it.
//! - The original Verus code has fallback paths using
//!   `proc_macro::TokenStream::expand_expr()` to read `cfg(verus_verify_core)`
//!   and `cfg(verus_no_vstd)`. Those paths require the unstable
//!   `proc_macro::TokenStream::expand_expr()`, which is only available
//!   in proc-macro crates. This crate is a regular library, not a
//!   proc-macro, so we drop those fallbacks. Typically every Verus
//!   build that needs a non-default `VstdKind` sets the `VSTD_KIND`
//!   env var directly via vargo, so the env-var path covers the
//!   real-world surface.

use std::sync::OnceLock;

/// Mirrors Verus's `VstdKind`. Each variant tells the vcheck engine where to
/// resolve `vstd::*` paths from.
#[derive(Clone, Copy, Debug)]
pub enum VstdKind {
    /// The current crate is vstd.
    IsVstd,
    /// There is no vstd (only verus_builtin). Really only used for testing.
    NoVstd,
    /// Imports the vstd crate like usual.
    Imported,
    /// Embed vstd and verus_builtin as modules, necessary for verifying the `core` library.
    IsCore,
    /// For other crates in stdlib verification that import core.
    ImportedViaCore,
}

/// Determine the build mode by reading env vars. Reads:
/// - `VSTD_KIND` env var (set by vargo). Highest priority.
/// - `CARGO_PKG_NAME == "vstd"` heuristic (when the env var isn't set).
///
/// Defaults to `Imported` (the normal case) when none of the signals fire.
pub fn vstd_kind() -> VstdKind {
    static VSTD_KIND: OnceLock<VstdKind> = OnceLock::new();
    *VSTD_KIND.get_or_init(|| {
        if let Ok(s) = std::env::var("VSTD_KIND") {
            if &s == "IsVstd" {
                return VstdKind::IsVstd;
            } else if &s == "NoVstd" {
                return VstdKind::NoVstd;
            } else if &s == "Imported" {
                return VstdKind::Imported;
            } else if &s == "IsCore" {
                return VstdKind::IsCore;
            } else if &s == "ImportedViaCore" {
                return VstdKind::ImportedViaCore;
            } else {
                panic!(
                    "The environment variable VSTD_KIND was set but its value ('{:}') is invalid. \
                     Allowed values are 'IsVstd', 'NoVstd', 'Imported', 'IsCore', and 'ImportedViaCore'",
                    s
                );
            }
        }

        // When building vstd normally through cargo, we won't get a
        // VSTD_KIND env var, but we can use CARGO_PKG_NAME instead
        let is_vstd = std::env::var("CARGO_PKG_NAME").map_or(false, |s| s == "vstd");
        if is_vstd {
            return VstdKind::IsVstd;
        }

        // If none of the above, just assume a normal build
        VstdKind::Imported
    })
}
