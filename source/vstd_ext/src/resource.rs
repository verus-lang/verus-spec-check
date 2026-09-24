//! `VcheckResource`: a samplable materialization of linear permissions for
//! vcheck harnesses
//!
//! A `#[vcheck]` fn that takes `Tracked<PointsTo<V>>` (or `Tracked<&PointsTo>` /
//! `Tracked<&mut PointsTo>`) cannot have its permission sampled, because a tracked
//! permission entirely exists to be seen by the borrow checker, then erased
//! by the Verus HIR -> VIR back-end passes. That is, (`Tracked::get`
//! / `::borrow` / `::view` don't exist under `cargo test`). What CAN be
//! sampled is the permission's view, i.e. an [`ExecMemContents`] model. This
//! module turns a sampled model into real, coupled runtime state by
//! replaying the resource's certified constructor (`PPtr::new` / `empty`),
//! whose `ensures` is the only sound tie between a permission and memory.
//!
//! ## Design
//!
//! At a high level, tracked permissions are shadowed by a `VcheckResourceGuard`
//! in the style of RAII, see: https://en.cppreference.com/cpp/language/raii.
//! The `VcheckResourceGuard` is generic over something implementing the `VcheckResource`
//! trait, which names the value and handle types, provides the materialization,
//! moves, and teardowns as static operations. Specifically, the materialization
//! attaches a state and a permission for every piece of memory that's sampled,
//! corresponding to the state of the tracked permission. This can be done because
//! `VcheckPermState` shadows the `MemContents` of the permission via
//! `exec_spec::ExecMemcontents`, which is in-effect the only sampleable part of
//! the permission.
//!
//! The `VcheckResource` is implemented for `vstd::PPtr`, providing a materialization
//! for this datatype that cases on the state of `ExecMemContents`. Every guard over a
//! `VcheckResource` (e.g. the one for `vstd::PPtr`) gets a `read_back`, which triggers
//! `take` (e.g. `vstd::PPtr::take`), minting a permission with `assume_new`.
//!
//! The lifetime of a vcheck sample is:
//! 1. sample `ExecMemContents`
//! 2. materialize it with `vcheck_materialize` to get your sample and your state
//! 3. call it under test
//! 4. apply the transition the contract dictates, e.g. `init`/`uninit`/`consumed`
//! 5. read it back and move it out if there are final-value ensures to check, then drop it
//!
//! Also note, these additons happen during macro processing-time; after these additions,
//! Verus proceeds with the tracked permission erasure procedure that erases ghost types.
//!
//! ## Toolchain notes (why this file is NOT inside `verus! {}`)
//!
//! Everything here is harness-only infrastructure, reached exclusively from
//! the generated `#[cfg(test)]` harness modules, which the verifier never
//! sees. Under `cargo verus verify` this crate is compiled (not verified) as
//! a dependency; under `cargo test` it's plain Rust.
//!
//! The `Tracked<..>` arguments of the fns we call are runtime `PhantomData`
//! ZSTs; they are minted with `Tracked::assume_new()` exactly as vstd's own
//! external-body constructors do internally.
//!
//! ## Panic safety
//!
//! A failing property panics mid-harness (that IS the failure signal), and
//! harnesses run under Miri with leak checking (`tools/run_miri.sh`).
//! [`VcheckResourceGuard`] therefore frees the materialized memory in `Drop`,
//! keyed on the shadow-model state, so every unwind path deallocates and
//! drops the payload exactly once.

use crate::exec_spec::ExecMemContents;
use vstd::prelude::Tracked;
use vstd::simple_pptr::{PPtr, PointsTo};

/// The guard's shadow of the permission's `MemContents` state tag.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VcheckPermState {
    /// Model says the memory is uninitialized, i.e. teardown frees raw memory
    /// without dropping a payload.
    Uninit,
    /// Model says the memory holds a live `V`, i.e. teardown must
    /// drop the before freeing.
    Init,
    /// The fn under test consumed the permission, e.g. `vstd::PPtr::free`.
    /// This indicates a no-op, as the callee already released the permission.
    Consumed,
}

/// VcheckResource is designed to represent a materializable resource kind,
/// such as `vstd::PPtr` and `vstd::PCell`. These types carry a public
/// exec constructor returning `(handle, Tracked<perm>: Tracked<PointsTo<V>>)`
/// whose postcondition pins the permission view to the constructor input.
///
/// Generally, these implementations are trusted.
pub trait VcheckResource {
    /// The payload type that the permission manages. The `T` in `MemContents<T>`
    /// is what the harness actually samples from.
    type Value;
    /// The exec-side handle type coupled to the permission, e.g. `PPtr<V>`.
    type Handle: Copy;
    /// Replay the certified constructor for the sampled model. Real memory
    /// comes into existence together with the (ZST) permission.
    fn vcheck_materialize(model: ExecMemContents<Self::Value>) -> (Self::Handle, VcheckPermState);

    /// Move the payload out of initialized memory, leaving it uninitialized
    /// (`vstd::PPtr::take` shape). Used by `read_back` to recover post-state
    /// values for `final(perm).value()` ensures clauses.
    fn vcheck_take(handle: Self::Handle) -> Self::Value;

    /// Tear down memory the model says is initialized (drop payload + free).
    fn vcheck_teardown_init(handle: Self::Handle);

    /// Tear down memory the model says is uninitialized (free only).
    fn vcheck_teardown_uninit(handle: Self::Handle);
}

/// An RAII-style guard that pairs a materialized resource handle with its
/// shadow-model state. https://en.cppreference.com/cpp/language/raii
///
/// The harness:
/// 1. Samples an `ExecMemContents<V> model`
/// 2. `materialize`s a guard, which will do a real alloc/write
/// 3. passes `guard.handle()` and a freshly minded `Tracked::assume_new()`
///    to the fn under test
/// 4. applies the contract's ghost transition, i.e. `mark_init` /
///    `mark_uninit` / `defuse`
/// 5. evaluates the deferred-observable ensures via `read_back()`,
/// 6. lets `Drop` release whatever is left on success AND panic
pub struct VcheckResourceGuard<R: VcheckResource> {
    handle: R::Handle,
    state: VcheckPermState,
}

impl<R: VcheckResource> VcheckResourceGuard<R> {
    /// Materialize real state for a sampled shadow model.
    pub fn materialize(model: ExecMemContents<R::Value>) -> Self {
        let (handle, state) = R::vcheck_materialize(model);
        VcheckResourceGuard { handle, state }
    }

    /// The exec handle to pass to the fn under test.
    pub fn handle(&self) -> R::Handle {
        self.handle
    }

    /// Current shadow-model state tag.
    pub fn state(&self) -> VcheckPermState {
        self.state
    }

    /// Apply the contract-classified post-call transition: memory is now
    /// initialized (e.g. after a `put`/`write`-shaped call).
    pub fn mark_init(&mut self) {
        self.state = VcheckPermState::Init;
    }

    /// Post-call transition: memory is now uninitialized (e.g. after
    /// `core::ptr::read` call where `T` is NOT of type Copy).
    /// https://doc.rust-lang.org/std/ptr/fn.read.html
    pub fn mark_uninit(&mut self) {
        self.state = VcheckPermState::Uninit;
    }

    /// The fn under test consumed the permission, i.e. an `Tracked<Perm>`
    /// param, went through a `free`/`into_inner`-shaped call.
    pub fn defuse(&mut self) {
        self.state = VcheckPermState::Consumed;
    }

    /// Recover the post-call memory contents through the certified read
    /// API, for evaluating `final(perm).value()`-style ensures. Moves the
    /// payload out (model transitions to `Uninit`), so call it once, after
    /// the fn under test.
    pub fn read_back(&mut self) -> ExecMemContents<R::Value> {
        match self.state {
            VcheckPermState::Init => {
                let v = R::vcheck_take(self.handle);
                self.state = VcheckPermState::Uninit;
                ExecMemContents::Init(v)
            }
            VcheckPermState::Uninit => ExecMemContents::Uninit,
            VcheckPermState::Consumed => {
                // A harness asking for post-state of a consumed permission,
                // which is UB and should be caught by the borrow checker.
                panic!(
                    "verus_spec_check: read_back() on a consumed permission: the fn under test \
                     took the Tracked<Perm> by value, so there is no post-state to observe"
                );
            }
        }
    }
}

impl<R: VcheckResource> Drop for VcheckResourceGuard<R> {
    fn drop(&mut self) {
        match self.state {
            VcheckPermState::Init => R::vcheck_teardown_init(self.handle),
            VcheckPermState::Uninit => R::vcheck_teardown_uninit(self.handle),
            VcheckPermState::Consumed => {}
        }
    }
}

/// Crate-identity-agnostic variant of [`VcheckResourceGuard`], and the form
/// the harness emitter will actually use.
///
/// Why not the trait?
///
/// When the harness expands _inside vstd itself_ (the in-place instrumentation
/// of `simple_pptr.rs`), the handle type is `crate::simple_pptr::PPtr<V>`
/// - a _different type_ from the upstream `vstd::simple_pptr::PPtr<V>`
/// this crate's `VcheckResource` impl is written
/// against, so the trait bound can't be satisfied. This guard instead takes
/// the constructor/teardown operations as fn pointers, emitted at the
/// expansion site (via the engine's `Vstd` path resolver), so they
/// monomorphize against whichever vstd is `crate` there. Same
/// state-keyed, panic-safe `Drop` contract as the trait-based guard.
pub struct VcheckDynResourceGuard<H: Copy> {
    handle: H,
    state: VcheckPermState,
    teardown_init: fn(H),
    teardown_uninit: fn(H),
}

impl<H: Copy> VcheckDynResourceGuard<H> {
    /// Materialize real state for a sampled shadow model by replaying the
    /// resource's certified constructor for the sampled state tag.
    pub fn materialize<V>(
        model: ExecMemContents<V>,
        init_ctor: fn(V) -> H,
        uninit_ctor: fn() -> H,
        teardown_init: fn(H),
        teardown_uninit: fn(H),
    ) -> Self {
        let (handle, state) = match model {
            ExecMemContents::Init(v) => (init_ctor(v), VcheckPermState::Init),
            ExecMemContents::Uninit => (uninit_ctor(), VcheckPermState::Uninit),
        };
        VcheckDynResourceGuard {
            handle,
            state,
            teardown_init,
            teardown_uninit,
        }
    }

    /// The exec handle to pass to the fn under test.
    pub fn handle(&self) -> H {
        self.handle
    }

    /// Current shadow-model state tag.
    pub fn state(&self) -> VcheckPermState {
        self.state
    }

    /// Post-call transition: memory is now initialized.
    pub fn mark_init(&mut self) {
        self.state = VcheckPermState::Init;
    }

    /// Post-call transition: memory is now uninitialized.
    pub fn mark_uninit(&mut self) {
        self.state = VcheckPermState::Uninit;
    }

    /// The fn under test consumed the permission: teardown becomes a no-op.
    pub fn defuse(&mut self) {
        self.state = VcheckPermState::Consumed;
    }

    /// Recover the post-call memory contents through a certified move-out
    /// operation (`PPtr::take` / `raw_ptr::ptr_mut_read` shaped), for
    /// evaluating `final(perm).value()` ensures clauses on `&mut`
    /// permissions.
    ///
    /// Call AFTER applying the contract's post-state transition
    /// (`mark_init` / `mark_uninit`). The current state tag decides whether
    /// a payload can be moved out at all. The move leaves the memory
    /// uninitialized (state -> `Uninit`), so teardown afterwards frees raw
    /// bytes only and the payload drops exactly once. This is what keeps
    /// read-back sound for `Drop` types (a _copying_ read would duplicate
    /// ownership and double-free).
    ///
    /// Epistemic note: the state tag comes from the *contract under test*
    /// (its `final(perm).is_init()`-style clauses direct the observation
    /// protocol). A wrong tag claim is not silently trusted: it
    /// manifests as failing value assertions or, for heap-owning payloads,
    /// as a Miri-visible leak / invalid read in the harness itself.
    pub fn read_back<V>(&mut self, take_op: fn(H) -> V) -> ExecMemContents<V> {
        match self.state {
            VcheckPermState::Init => {
                let v = take_op(self.handle);
                self.state = VcheckPermState::Uninit;
                ExecMemContents::Init(v)
            }
            VcheckPermState::Uninit => ExecMemContents::Uninit,
            VcheckPermState::Consumed => {
                panic!(
                    "verus_spec_check: read_back() on a consumed permission: the fn under test \
                     took the Tracked<Perm> by value, so there is no post-state to observe"
                );
            }
        }
    }
}

impl<H: Copy> Drop for VcheckDynResourceGuard<H> {
    fn drop(&mut self) {
        match self.state {
            VcheckPermState::Init => (self.teardown_init)(self.handle),
            VcheckPermState::Uninit => (self.teardown_uninit)(self.handle),
            VcheckPermState::Consumed => {}
        }
    }
}

/// Impl for [`vstd::simple_pptr::PPtr`].
///
/// Provides certified constructors for `PPtr::new` (view pinned to `Init(v)`)
/// and `PPtr::empty` (view pinned to `Uninit`), and teardown via
/// `into_inner` / `free`. All four are real
/// allocator traffic at runtime, which should be caught by Miri.
impl<V> VcheckResource for PPtr<V> {
    type Value = V;
    type Handle = PPtr<V>;

    fn vcheck_materialize(model: ExecMemContents<V>) -> (PPtr<V>, VcheckPermState) {
        match model {
            ExecMemContents::Init(v) => {
                let (ptr, _perm) = PPtr::new(v);
                (ptr, VcheckPermState::Init)
            }
            ExecMemContents::Uninit => {
                let (ptr, _perm) = PPtr::<V>::empty();
                (ptr, VcheckPermState::Uninit)
            }
        }
    }

    fn vcheck_take(handle: PPtr<V>) -> V {
        handle.take(mint_tracked_mut())
    }

    fn vcheck_teardown_init(handle: PPtr<V>) {
        // `into_inner` moves the payload out (dropping it here) and frees.
        let _v = handle.into_inner(Tracked::assume_new());
    }

    fn vcheck_teardown_uninit(handle: PPtr<V>) {
        handle.free(Tracked::assume_new());
    }
}

/// Mint a `Tracked<&mut P>` argument. At runtime `Tracked<_>` is a
/// `PhantomData` ZST, so this fabricates only ghost-erased state; the
/// coupling to real memory is the caller's (guard's) responsibility.
fn mint_tracked_mut<'a, P>() -> Tracked<&'a mut P> {
    Tracked::assume_new()
}

#[cfg(test)]
mod tests {
    //! Guard semantics tests. These run real allocator traffic (PPtr::new /
    //! empty / take / into_inner / free), so they double as the first
    //! Miri-checkable surface for the tracked-support work

    use super::*;

    type R = PPtr<u32>;

    /// Init model: materialize writes the sampled payload; read_back
    /// recovers it and transitions the model to Uninit; Drop then frees
    /// raw memory only.
    #[test]
    fn init_materialize_read_back() {
        let mut g = VcheckResourceGuard::<R>::materialize(ExecMemContents::Init(42));
        assert_eq!(g.state(), VcheckPermState::Init);
        assert_eq!(g.read_back(), ExecMemContents::Init(42));
        assert_eq!(g.state(), VcheckPermState::Uninit);
        // Drop frees the (now uninitialized) allocation.
    }

    /// Uninit model: materialize allocates without writing; read_back
    /// observes Uninit; Drop frees.
    #[test]
    fn uninit_materialize_read_back() {
        let mut g = VcheckResourceGuard::<R>::materialize(ExecMemContents::Uninit);
        assert_eq!(g.state(), VcheckPermState::Uninit);
        assert_eq!(g.read_back(), ExecMemContents::Uninit);
    }

    /// Init model dropped WITHOUT read_back: Drop must move the payload out
    /// (dropping it) before freeing. With a heap-owning payload this is the
    /// leak-or-not case Miri adjudicates.
    #[test]
    fn init_drop_without_read_back_drops_payload() {
        let g = VcheckResourceGuard::<PPtr<Box<u32>>>::materialize(ExecMemContents::Init(Box::new(7)));
        assert_eq!(g.state(), VcheckPermState::Init);
        drop(g);
    }

    #[test]
    fn call_through_with_transition() {
        let mut g = VcheckResourceGuard::<R>::materialize(ExecMemContents::Init(5));
        // "fn under test": take() moves the value out; its contract says
        // final(perm).is_uninit().
        let got = g.handle().take(Tracked::assume_new());
        assert_eq!(got, 5);
        g.mark_uninit(); // classified ghost transition from the ensures
        assert_eq!(g.read_back(), ExecMemContents::Uninit);
    }

    /// Consumed permission: the callee freed the memory; Drop must be a
    /// no-op (a double free here is exactly what Miri would catch).
    #[test]
    fn consumed_defuses_teardown() {
        let mut g = VcheckResourceGuard::<R>::materialize(ExecMemContents::Init(9));
        // "fn under test": into_inner consumes the permission and frees.
        let got = g.handle().into_inner(Tracked::assume_new());
        assert_eq!(got, 9);
        g.defuse();
    }

    /// Panic safety: unwinding out of a "failing property" still tears down
    /// the materialized allocation (asserted by Miri's leak check when this
    /// suite runs under `tools/run_miri.sh`).
    #[test]
    fn teardown_on_unwind() {
        let result = std::panic::catch_unwind(|| {
            let _g =
                VcheckResourceGuard::<PPtr<Box<u32>>>::materialize(ExecMemContents::Init(Box::new(1)));
            panic!("property failed");
        });
        assert!(result.is_err());
    }
}
