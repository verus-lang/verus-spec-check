//! Sampled predicate values for higher-order contracts.
//!
//! Verus specs on higher-order fns (`fn all_(v, pred: impl Fn(&T) -> bool)`)
//! quantify over the closure's contract via `call_requires` /
//! `call_ensures`. A property-test harness cannot sample "an arbitrary
//! closure with an arbitrary contract", but it CAN sample from a *family*
//! of predicates whose contracts are known by construction. [`VcheckPred`] is
//! that family:
//!
//! - **Pure** kinds (membership / threshold tables): deterministic, with the
//!   tight implicit contract `ret == eval(x)`. For these,
//!   `call_ensures(pred, (x,), r)` faithfully lowers to `r == pred.eval(x)`.
//!
//! - **Stateful** kinds (call-count budgets): legal under `Fn` via interior
//!   mutability. For these there is no per-call functional contract; the
//!   faithful runtime meaning of `call_ensures(pred, (x,), r)` is *trace
//!   membership* — "some actual call on `x` returned `r`" — because in Verus
//!   positive `call_ensures` facts arise only from actual calls. Every
//!   `call()` is recorded in [`VcheckPred::trace`] for exactly this purpose.
//!
//! The engine lowers `call_ensures(pred, (x,), r)` to `pred.models(&x, r)`,
//! which dispatches on the sampled kind. Stateful kinds are what expose
//! specs that over-assume determinism (e.g. a biconditional
//! `res <==> forall ... call_ensures(pred, _, true)`).

use std::cell::RefCell;
use std::fmt::Debug;
use std::hash::Hash;

use proptest::collection::hash_set;
use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use crate::{VcheckStrategy, DEFAULT_COLLECTION_MAX};

/// The decision procedure backing a sampled predicate.
#[derive(Clone, Debug)]
pub enum PredKind<T> {
    /// `x ∈ set`, XOR'd with `polarity`. Pure and deterministic; the
    /// implicit contract is tight: `ret == eval(x)`.
    Membership {
        set: std::collections::HashSet<T>,
        /// `false` -> "in set"; `true` -> "NOT in set".
        negate: bool,
    },
    /// Returns `true` for the first `budget` calls, `false` afterwards.
    /// Stateful (interior mutability) but still `Fn`-callable — the family
    /// member that exposes contracts assuming predicate determinism.
    Budget { budget: usize },
}

/// A sampled predicate over `&T`, with a recorded call trace.
#[derive(Debug)]
pub struct VcheckPred<T> {
    kind: PredKind<T>,
    calls: RefCell<usize>,
    trace: RefCell<Vec<(T, bool)>>,
}

impl<T: Clone> Clone for VcheckPred<T> {
    fn clone(&self) -> Self {
        // Fresh state: cloning a pred resets its call counter and trace.
        // (Harnesses clone the sampled value once, before any calls.)
        VcheckPred {
            kind: self.kind.clone(),
            calls: RefCell::new(0),
            trace: RefCell::new(Vec::new()),
        }
    }
}

impl<T: Eq + Hash + Clone> VcheckPred<T> {
    pub fn new(kind: PredKind<T>) -> Self {
        VcheckPred {
            kind,
            calls: RefCell::new(0),
            trace: RefCell::new(Vec::new()),
        }
    }

    /// Whether this predicate is pure (deterministic per input).
    pub fn is_pure(&self) -> bool {
        matches!(self.kind, PredKind::Membership { .. })
    }

    /// The *pure* decision, without advancing state or recording. Only
    /// meaningful for pure kinds; for stateful kinds returns the decision
    /// the NEXT call would make (do not use for contract evaluation —
    /// use [`Self::models`]).
    pub fn eval(&self, x: &T) -> bool {
        match &self.kind {
            PredKind::Membership { set, negate } => set.contains(x) ^ negate,
            PredKind::Budget { budget } => *self.calls.borrow() < *budget,
        }
    }

    /// An actual predicate invocation: advances state and records the
    /// (input, output) pair in the trace. This is what the harness passes
    /// to the fn under test (wrapped in a closure).
    pub fn call(&self, x: &T) -> bool {
        let r = match &self.kind {
            PredKind::Membership { set, negate } => set.contains(x) ^ negate,
            PredKind::Budget { budget } => {
                let mut c = self.calls.borrow_mut();
                *c += 1;
                *c <= *budget
            }
        };
        self.trace.borrow_mut().push((x.clone(), r));
        r
    }

    /// Runtime meaning of `call_ensures(pred, (x,), ret)`:
    /// - pure kind: `ret == eval(x)` (the family's contract is tight);
    /// - stateful kind: trace membership — a positive `call_ensures` fact
    ///   in Verus can only come from an actual call.
    pub fn models(&self, x: &T, ret: bool) -> bool {
        match &self.kind {
            PredKind::Membership { .. } => ret == self.eval(x),
            PredKind::Budget { .. } => self
                .trace
                .borrow()
                .iter()
                .any(|(tx, tr)| tx == x && *tr == ret),
        }
    }

    /// Runtime meaning of `call_requires(pred, (x,))`. The sampled family
    /// is total: always `true`.
    pub fn requires(&self, _x: &T) -> bool {
        true
    }
}

impl<T> VcheckPred<T>
where
    T: VcheckStrategy + Eq + Hash + Clone + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    fn kind_strategy() -> BoxedStrategy<PredKind<T>> {
        prop_oneof![
            // Pure membership tables (both polarities).
            3 => (
                hash_set(T::vcheck_strategy(), 0..DEFAULT_COLLECTION_MAX),
                any::<bool>()
            )
                .prop_map(|(set, negate)| PredKind::Membership { set, negate }),
            // Stateful budgets. Small budgets bias toward the interesting
            // regime (state flips mid-iteration).
            2 => (0usize..8).prop_map(|budget| PredKind::Budget { budget }),
        ]
        .boxed()
    }
}

impl<T> VcheckStrategy for VcheckPred<T>
where
    T: VcheckStrategy + Eq + Hash + Clone + Debug + 'static,
    <T as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<VcheckPred<T>>;
    fn vcheck_strategy() -> Self::Strategy {
        Self::kind_strategy().prop_map(VcheckPred::new).boxed()
    }
}

/// Pair strategy: used by iterator-state params, which sample
/// `(collection, cursor)`. Proptest composes tuple strategies natively;
/// this impl just routes both components through their `VcheckStrategy`.
impl<A, B> VcheckStrategy for (A, B)
where
    A: VcheckStrategy + Debug + 'static,
    B: VcheckStrategy + Debug + 'static,
    <A as VcheckStrategy>::Strategy: 'static,
    <B as VcheckStrategy>::Strategy: 'static,
{
    type Strategy = BoxedStrategy<(A, B)>;
    fn vcheck_strategy() -> Self::Strategy {
        (A::vcheck_strategy(), B::vcheck_strategy()).boxed()
    }
}
