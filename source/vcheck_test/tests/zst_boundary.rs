mod common;
use common::*;

// The finding itself, from a single `#[vcheck(T = ())]` label on a generic
// growth fn: the harness must discover a boundary pair, observe the
// "capacity overflow" panic, and report it (with the bounded `[<zst>; N]`
// counterexample printing — an unbounded printer would hang, not fail).
test_vcheck_one_file! {
    #[test] zst_vec_append_label_finds_overflow vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vec_append<T>(v: &mut Vec<T>, other: &mut Vec<T>)
            ensures
                final(v)@ == old(v)@ + old(other)@,
                final(other)@ == Seq::<T>::empty(),
        {
            v.append(other);
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// Same class through VecDeque, which additionally exercises the O(1)
// ZST paths in `__vcheck_vecdeque_snapshot` (VecDeque::clone walks
// elements) and `__vcheck_vecdeque_slice` (view materialization).
test_vcheck_one_file! {
    #[test] zst_vecdeque_append_label_finds_overflow vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vecdeque_append<T>(
            v: &mut std::collections::VecDeque<T>,
            other: &mut std::collections::VecDeque<T>,
        )
            ensures
                final(v)@ == old(v)@ + old(other)@,
                final(other)@ == Seq::<T>::empty(),
        {
            v.append(other);
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// Multi-instantiation: ONE assume_specification carrying TWO `#[vcheck]`
// markers. The primary `T = u32` instantiation checks ordinary behavior
// (bounded vecs — append can't overflow) and must pass; the secondary
// `T = ()` instantiation reaches the boundary and must fail. Two
// wrappers -> two harnesses; the run fails overall with the overflow.
test_vcheck_one_file! {
    #[test] zst_second_instantiation_on_assume_spec vcheck_code! {
        #[vcheck(T = u32)]
        #[vcheck(T = ())]
        pub assume_specification<T>[ Vec::<T>::append ](
            v: &mut Vec<T>,
            other: &mut Vec<T>,
        )
            ensures
                final(v)@ == old(v)@ + old(other)@,
                final(other)@ == Seq::<T>::empty(),
        ;
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// Single-container growth: `push` at len == usize::MAX panics "capacity
// overflow" (len == cap forces a grow even for ZSTs). The spec claims
// the appended view (`old@.push(x)`) with no length bound — same finding
// class as `append`, reachable from ONE boundary sample instead of a
// pair. Exercises the `__vcheck_seq_push(..).as_slice()` eq-operand path:
// on the non-panicking boundary samples (e.g. len usize::MAX/2 + 1) the
// ensures comparison must route through the ZST-aware `__vcheck_seq_eq`,
// or it walks 2^63 elements.
test_vcheck_one_file! {
    #[test] zst_vec_push_label_finds_overflow vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vec_push_zst<T>(v: &mut Vec<T>, x: T)
            ensures
                final(v)@ == old(v)@.push(x),
        {
            v.push(x);
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// Same through VecDeque::push_front, whose spec is the front-insertion
// concat form `seq![x] + old(v)@` (the `__vcheck_seq_concat` path).
test_vcheck_one_file! {
    #[test] zst_vecdeque_push_front_label_finds_overflow vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vecdeque_push_front_zst<T>(
            v: &mut std::collections::VecDeque<T>,
            x: T,
        )
            ensures
                final(v)@ == seq![x] + old(v)@,
        {
            v.push_front(x);
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// And `insert`: the `i <= len` requires does NOT exclude len ==
// usize::MAX, so the growth overflow is still reachable. Exercises the
// `__vcheck_seq_insert(..).as_slice()` eq-operand path.
test_vcheck_one_file! {
    #[test] zst_vec_insert_label_finds_overflow vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vec_insert_zst<T>(v: &mut Vec<T>, i: usize, x: T)
            requires
                i <= old(v)@.len(),
            ensures
                final(v)@ == old(v)@.insert(i as int, x),
        {
            v.insert(i, x);
        }
    } => HarnessOutcome::FailsHarnessWith { needle: "capacity overflow" }
}

// Control: the same growth contract at a sized element type stays
// bounded and passes — the boundary arm must not leak into sized
// instantiations, and the wrapped counterexample printing must be
// invisible for them.
test_vcheck_one_file! {
    #[test] sized_vec_append_still_passes vcheck_code! {
        #[vcheck(T = u32)]
        #[verifier::external_body]
        pub exec fn vec_append_sized<T>(v: &mut Vec<T>, other: &mut Vec<T>)
            ensures
                final(v)@ == old(v)@ + old(other)@,
                final(other)@ == Seq::<T>::empty(),
        {
            v.append(other);
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}
