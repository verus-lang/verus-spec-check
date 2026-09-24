mod common;
use common::*;

// SOUND: predicate params and single application.
test_vcheck_one_file! {
    #[test] sound_pred_application vcheck_code! {
        // Smoke: predicate params are sampleable; contract ignores pred.
        #[vcheck]
        #[verifier::external_body]
        pub fn pred_smoke(x: u32, pred: impl Fn(&u32) -> bool) -> (r: bool)
            ensures
                r == true || r == false,
        {
            pred(&x)
        }

        // `call_ensures` on the actual result: true for the whole sampled
        // family (pure preds give a tight contract; stateful ones have
        // the call recorded in the trace)
        #[vcheck]
        #[verifier::external_body]
        pub fn pred_apply(x: u32, pred: impl Fn(&u32) -> bool) -> (r: bool)
            ensures
                call_ensures(pred, (&x,), r),
        {
            pred(&x)
        }

        // Method-form spelling of the same contract.
        #[vcheck]
        #[verifier::external_body]
        pub fn pred_apply_method_form(x: u32, pred: impl Fn(&u32) -> bool) -> (r: bool)
            requires
                call_requires(pred, (&x,)),
            ensures
                pred.ensures((&x,), r),
        {
            pred(&x)
        }
    } => HarnessOutcome::Pass { harnesses: 3 }
}

// SOUND `Vec::all_`: one-directional implications. `res == true` claims a
// pred-true fact for every element (all were actually called);
// `res == false` claims a pred-false fact for the one failing call.
// Neither direction over-assumes determinism.
test_vcheck_one_file! {
    #[test] sound_vec_all vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub fn vec_all_sound(v: Vec<u32>, pred: impl Fn(&u32) -> bool) -> (res: bool)
            requires
                forall|elem: u32| v@.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res ==> forall|elem: u32|
                    v@.contains(elem) ==> call_ensures(pred, (&elem,), true),
                !res ==> exists|elem: u32|
                    v@.contains(elem) && call_ensures(pred, (&elem,), false),
        {
            v.iter().all(pred)
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// UNSOUND counterpart: The `<==` direction over-assumes
// predicate determinism. For a stateful
// (interior-mutability) predicate a caller can witness
// call_ensures(pred, (&e,), true) from a direct call while a later
// all_() observes false. The harness samples such predicates (VcheckPred's
// Budget kind), primes them once per element, and refutes the
// equivalence.
test_vcheck_one_file! {
    #[test] unsound_vec_all_biconditional vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub fn vec_all_biconditional(v: Vec<u32>, pred: impl Fn(&u32) -> bool) -> (res: bool)
            requires
                forall|elem: u32| v@.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res <==> (forall|elem: u32|
                    v@.contains(elem) ==> call_ensures(pred, (&elem,), true)),
        {
            v.iter().all(pred)
        }
    } => HarnessOutcome::FailsHarness
}

// ---------------------------------------------------------------------------
// Iterator mid-states. These need `vcheck_code_raw!`: the trait + impl live
// outside `verus!`, and the `assume_specification` sits in a nested
// module.
// ---------------------------------------------------------------------------

// SOUND: quantifies over the REMAINING elements
// (`old(s)@.1.skip(old(s)@.0)`) — what the executable all() actually
// visits. Passes at every sampled cursor position.
test_vcheck_one_file! {
    #[test] sound_iter_all_remaining vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;

        pub trait AdditionalIterFns {
            type Item;
            fn all_(&mut self, pred: impl Fn(&Self::Item) -> bool) -> bool;
        }

        impl<'a, T: 'a> AdditionalIterFns for std::slice::Iter<'a, T> {
            type Item = T;
            #[inline]
            fn all_(&mut self, pred: impl Fn(&T) -> bool) -> bool {
                self.all(pred)
            }
        }

        verus! {

        #[vcheck]
        pub assume_specification<'a>[ <std::slice::Iter<'a, u32> as AdditionalIterFns>::all_ ](
            s: &mut std::slice::Iter<'a, u32>,
            pred: impl Fn(&u32) -> bool,
        ) -> (res: bool)
            requires
                forall|elem: u32| old(s)@.1.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res ==> old(s)@.1.skip(old(s)@.0).all(
                    |elem: u32| call_ensures(pred, (&elem,), true)),
                !res ==> old(s)@.1.skip(old(s)@.0).any(
                    |elem: u32| call_ensures(pred, (&elem,), false)),
        ;

        } // verus!
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// UNSOUND counterpart: quantifies over the FULL sequence. vstd models
// slice iterators as (index, full_seq) with `next` leaving the seq
// unchanged, so `old(s)@.1` includes elements the executable all()
// (which visits only the remainder) never saw. Any sampled cursor > 0
// over a non-trivial collection, with a pred false on a consumed
// element, refutes the `res ==> ...` clause.
test_vcheck_one_file! {
    #[test] unsound_iter_all_full_seq vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;

        pub trait AdditionalIterFns {
            type Item;
            fn all_(&mut self, pred: impl Fn(&Self::Item) -> bool) -> bool;
        }

        impl<'a, T: 'a> AdditionalIterFns for std::slice::Iter<'a, T> {
            type Item = T;
            #[inline]
            fn all_(&mut self, pred: impl Fn(&T) -> bool) -> bool {
                self.all(pred)
            }
        }

        verus! {

        #[vcheck]
        pub assume_specification<'a>[ <std::slice::Iter<'a, u32> as AdditionalIterFns>::all_ ](
            s: &mut std::slice::Iter<'a, u32>,
            pred: impl Fn(&u32) -> bool,
        ) -> (res: bool)
            requires
                forall|elem: u32| old(s)@.1.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res ==> old(s)@.1.all(|elem: u32| call_ensures(pred, (&elem,), true)),
                !res ==> old(s)@.1.any(|elem: u32| call_ensures(pred, (&elem,), false)),
        ;

        } // verus!
    } => HarnessOutcome::FailsHarness
}

// SOUND Keys::any_ — remaining-keys form.
test_vcheck_one_file! {
    #[test] sound_keys_any_remaining vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;
        use std::collections::hash_map::Keys;

        pub trait AdditionalIterFns {
            type Item;
            fn any_(&mut self, pred: impl Fn(&Self::Item) -> bool) -> bool;
        }

        impl<'a, K, V> AdditionalIterFns for Keys<'a, K, V> {
            type Item = K;
            #[inline]
            fn any_(&mut self, pred: impl Fn(&K) -> bool) -> bool {
                self.any(pred)
            }
        }

        verus! {

        #[vcheck]
        pub assume_specification<'a>[ <Keys<'a, u32, u32> as AdditionalIterFns>::any_ ](
            s: &mut Keys<'a, u32, u32>,
            pred: impl Fn(&u32) -> bool,
        ) -> (res: bool)
            requires
                forall|elem: u32| old(s)@.1.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res ==> (exists|elem: u32| old(s)@.1.skip(old(s)@.0).contains(elem)
                            && call_ensures(pred, (&elem,), true)),
                !res ==> old(s)@.1.skip(old(s)@.0).all(
                    |elem: u32| call_ensures(pred, (&elem,), false)),
        ;

        } // verus!
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// UNSOUND counterpart: same full-sequence over-claim on the `!res`
// branch. After a next(), a pred TRUE on the consumed key and false on
// the remaining ones makes any_() return false while
// `!res ==> all(... false)` claims a pred-false fact about the consumed
// key.
test_vcheck_one_file! {
    #[test] unsound_keys_any_full_seq vcheck_code_raw! {
        #![allow(unused_imports)]
        use verus_spec_check::*;
        use verus_spec_check_vstd_ext::*;
        use vstd::prelude::*;
        use std::collections::hash_map::Keys;

        pub trait AdditionalIterFns {
            type Item;
            fn any_(&mut self, pred: impl Fn(&Self::Item) -> bool) -> bool;
        }

        impl<'a, K, V> AdditionalIterFns for Keys<'a, K, V> {
            type Item = K;
            #[inline]
            fn any_(&mut self, pred: impl Fn(&K) -> bool) -> bool {
                self.any(pred)
            }
        }

        verus! {

        #[vcheck]
        pub assume_specification<'a>[ <Keys<'a, u32, u32> as AdditionalIterFns>::any_ ](
            s: &mut Keys<'a, u32, u32>,
            pred: impl Fn(&u32) -> bool,
        ) -> (res: bool)
            requires
                forall|elem: u32| old(s)@.1.contains(elem) ==> call_requires(pred, (&elem,)),
            ensures
                res ==> (exists|elem: u32| old(s)@.1.contains(elem)
                            && call_ensures(pred, (&elem,), true)),
                !res ==> old(s)@.1.all(|elem: u32| call_ensures(pred, (&elem,), false)),
        ;

        } // verus!
    } => HarnessOutcome::FailsHarness
}
