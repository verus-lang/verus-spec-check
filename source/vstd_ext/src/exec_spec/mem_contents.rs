//! This module contains the exec mirror of [`vstd::raw_ptr::MemContents`],
//! the abstract memory-state view of the `PointsTo` permission family
//! (`raw_ptr::PointsTo`, `simple_pptr::PointsTo`, `cell::PointsTo`).
//!
//! `MemContents<T>` is the *sample-able bottom layer* of a permission:
//! the permission itself is a runtime ZST with no
//! exec side, but its view - "this memory is `Uninit` or `Init(v)`" - is
//! ordinary spec data that contracts project via `perm.is_init()` /
//! `perm.value()`. The harness samples an `ExecMemContents<T>` as the
//! shadow model, materializes real memory to match, and evaluates the
//! rewritten contract against the model.
//!
//! Unlike `Option<T>` (whose exec mirror is itself), `MemContents` needs a
//! distinct exec type: it is a `ghost enum`, so its constructors don't
//! exist in exec code under `cargo verus verify`.

use crate::exec_spec::*;
use vstd::prelude::*;
use vstd::raw_ptr::MemContents;

verus! {

/// `MemContents<T>` is compiled to `ExecMemContents<T>`
#[derive(Eq, PartialEq, Debug)]
pub enum ExecMemContents<T> {
    /// Mirror of [`MemContents::Uninit`]
    Uninit,
    /// Mirror of [`MemContents::Init`]
    Init(T),
}

/// Implementations for shared traits
impl<T: DeepView> DeepView for ExecMemContents<T> {
    type V = MemContents<<T as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ExecMemContents::Uninit => MemContents::Uninit,
            ExecMemContents::Init(t) => MemContents::Init(t.deep_view()),
        }
    }
}

impl<'a, T: DeepView> ToRef<&'a ExecMemContents<T>> for &'a ExecMemContents<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a ExecMemContents<T> {
        self
    }
}

impl<'a, T: DeepView + DeepViewClone> ToOwned<ExecMemContents<T>> for &'a ExecMemContents<T> {
    #[inline(always)]
    fn get_owned(self) -> ExecMemContents<T> {
        self.deep_clone()
    }
}

impl<T: DeepViewClone> DeepViewClone for ExecMemContents<T> {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        match self {
            ExecMemContents::Uninit => ExecMemContents::Uninit,
            ExecMemContents::Init(t) => ExecMemContents::Init(t.deep_clone()),
        }
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a ExecMemContents<T> where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Other = &'a ExecMemContents<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (ExecMemContents::Init(t1), ExecMemContents::Init(t2)) => <&'a T>::exec_eq(t1, t2),
            (ExecMemContents::Uninit, ExecMemContents::Uninit) => true,
            _ => false,
        }
    }
}

/// Traits for MemContents methods
/// Spec for executable versions of [`MemContents::is_init`],
/// [`MemContents::is_uninit`], and [`MemContents::value`].
pub trait ExecSpecMemContents<'a>: Sized + DeepView {
    type Elem: DeepView + DeepViewClone;

    spec fn is_init_spec(&self) -> bool;

    fn exec_is_init(self) -> bool;

    fn exec_is_uninit(self) -> bool;

    fn exec_value(self) -> Self::Elem
        requires
            self.is_init_spec(),
    ;
}

/// Impls for MemContents methods
impl<'a, T> ExecSpecMemContents<'a> for &'a ExecMemContents<T> where T: DeepView + DeepViewClone {
    type Elem = T;

    open spec fn is_init_spec(&self) -> bool {
        self.deep_view() is Init
    }

    #[inline(always)]
    fn exec_is_init(self) -> (res: bool)
        ensures
            res == self.deep_view().is_init(),
    {
        match self {
            ExecMemContents::Init(_) => true,
            ExecMemContents::Uninit => false,
        }
    }

    #[inline(always)]
    fn exec_is_uninit(self) -> (res: bool)
        ensures
            res == self.deep_view().is_uninit(),
    {
        match self {
            ExecMemContents::Uninit => true,
            ExecMemContents::Init(_) => false,
        }
    }

    #[inline(always)]
    fn exec_value(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view()->0,
    {
        match self {
            ExecMemContents::Init(t) => t.deep_clone(),
            ExecMemContents::Uninit => {
                // Unreachable under the `is_init_spec` requires. Keep a
                // runtime panic (not UB) as the erased-build behavior so a
                // harness bug surfaces as a clean failure.
                vstd::pervasive::unreached()
            },
        }
    }
}

/// Harness-side constructor: build the shadow model from a sampled
/// `Option<T>` (`None` -> `Uninit`, `Some(v)` -> `Init(v)`). Sampling an
/// `Option` and wrapping at the call site follows the `ExecMultiset`
/// precedent (sample a `HashMap`, wrap into the exec mirror), so no
/// backend-specific strategy impl is needed for this type.
#[inline(always)]
pub fn exec_mem_contents_from_option<T: DeepView>(o: Option<T>) -> (res: ExecMemContents<T>)
    ensures
        res.deep_view() == match o.deep_view() {
            Some(v) => MemContents::Init(v),
            None => MemContents::Uninit,
        },
{
    match o {
        Some(t) => ExecMemContents::Init(t),
        None => ExecMemContents::Uninit,
    }
}

} // verus!
