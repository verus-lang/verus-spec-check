//! `#[vcheck_provide]` and `#[vcheck]` attribute preprocessing.
//!
//! These run as a whole-`Vec<Item>` pass during `contrib_preprocess_items`,
//! which gives them sibling visibility within a single `verus! { ... }` block
//! (the per-item hook used by `auto_spec` cannot see siblings).
//!
//! ## `#[vcheck_provide]`
//!
//! Marks a `struct`/`enum`/spec-fn as a source of property-based-testing
//! infrastructure. The marked item (and, for a type, its inherent impls) is
//! folded into a single `verus_spec_check_unverified! { ... }` block, so the backend
//! emits the engine `Exec*` companions, `exec_*` spec fns, and the
//! `VcheckStrategy` / `ToExecModel` / `VcheckSpecCompanion` trait impls (which
//! resolve by trait lookup across files).
//!
//! ## `#[vcheck]`
//!
//! Marks a contract-bearing exec fn (free or method) to be property-tested.
//! The pass computes the transitive closure of spec fns + user types its
//! `requires`/`ensures` (and their bodies/fields) reach **among siblings in
//! the same `verus!` block**, and folds the exec fn + that closure into one
//! engine block. The backend then generates both the engine companions and
//! the `proptest!` harness. The user adds only `#[vcheck]` — no separate macro
//! block, no `#[vcheck_provide]` for in-block dependencies.
//!
//! Items the closure cannot resolve in-block (defined in another file) are
//! left out; the harness references them by trait, and a missing
//! `#[vcheck_provide]` at their definition site surfaces as the
//! `on_unimplemented` diagnostic on `VcheckStrategy`/`ToExecModel`.

use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::spanned::Spanned;
use verus_syn::visit::Visit;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{
    Attribute, Expr, ExprPath, FnMode, GenericArgument, GenericParam, Generics, Ident, ImplItem,
    Item, ItemFn, Meta, PathArguments, Type, UseTree,
};

// Crate aliases so the module bodies' original `crate::<name>::*`
// paths resolve
use verus_spec_check_assert as vcheck_assert;
use verus_spec_check_exec_spec as exec_spec;
use verus_spec_check_external_provide as external_vcheck_provide;
use verus_spec_check_syntax::vstd_kind;

mod attr_helpers;
mod closure;
mod config;
mod impl_lift;
mod index;
mod pass;
mod refs;
mod subst;
mod wrapper_synth;

pub use attr_helpers::*;
pub use closure::*;
pub use config::*;
pub use impl_lift::*;
pub use index::*;
pub use pass::*;
pub use refs::*;
pub use subst::*;
pub use wrapper_synth::*;
