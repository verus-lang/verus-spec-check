//! Implementation of `verus_spec_check_unverified!` and `verus_spec_check_verified!`.
//!
//! These macros sit alongside `exec_spec_unverified!` / `exec_spec_verified!`
//! in the contrib tree. Given a body of items containing `spec` functions,
//! user-defined `struct` / `enum`s, and exec functions with `requires` /
//! `ensures` clauses, they emit:
//!
//! 1. A `verus! { ... }` block holding the user's items unchanged so Verus
//!    still verifies the spec layer.
//! 2. An engine block (`exec_spec_unverified!` or `exec_spec_verified!`)
//!    compiling every spec fn and user type reachable from a contract into
//!    its `Exec*` counterpart. This block also includes any synthetic spec
//!    fns the macro lifts inline `forall`/`exists` into.
//! 3. A `VcheckStrategy` impl per user-defined struct/enum so the harness can
//!    sample values of `Exec*` types directly.
//! 4. A `#[cfg(test)] mod __verus_spec_check_<id>` containing one `proptest!`
//!    harness per contract-bearing exec fn. The harness asks the runtime
//!    crate (`::verus_spec_check_runtime`) for a strategy per parameter,
//!    `prop_assume!`s the requires, calls the real exec fn, and
//!    `prop_assert!`s the ensures.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use proc_macro2::{Span, TokenStream as TokenStream2};
type TokenStream = proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::visit::Visit;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{
    Error, Expr, ExprCall, ExprMethodCall, ExprPath, ExprUnary, Fields, FnArgKind, FnMode,
    GenericArgument, Ident, Item, ItemEnum, ItemFn, ItemImpl, ItemStruct, Pat, PatType,
    PathArguments, ReturnType, Type, UnOp,
};

// Crate aliases so the module bodies' original `crate::<name>::*`
// paths keep resolving after the split out of `verus_spec_check_engine`.
use verus_spec_check_assert as vcheck_assert;
use verus_spec_check_attr as vcheck_attr;
use verus_spec_check_exec_spec as exec_spec;
use verus_spec_check_external_provide as external_vcheck_provide;
use verus_spec_check_instrument as vcheck_instrument;
use verus_spec_check_mutator as vcheck_mutator;
use verus_spec_check_syntax::syntax;

mod audit;
mod bolero_emit;
mod classify;
mod concretize;
mod contract_rewriter;
mod cov_fuzz_emit;
mod cov_mutate_emit;
mod expand;
mod expr_utils;
mod harness_emit;
mod inline_assert_emit;
mod inline_quant;
mod param_shape;
mod render;
mod resource;
mod strategy_emit;

pub use audit::*;
pub use bolero_emit::*;
pub use classify::*;
pub use concretize::*;
pub use contract_rewriter::*;
pub use cov_fuzz_emit::*;
pub use cov_mutate_emit::*;
pub use expand::*;
pub use expr_utils::*;
pub use harness_emit::*;
pub use inline_assert_emit::*;
pub use inline_quant::*;
pub use param_shape::*;
pub use render::*;
pub use resource::*;
pub use strategy_emit::*;
