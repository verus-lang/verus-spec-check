mod common;
use common::*;

// Shared snippet: harness gate + verify gate at the bottom of this file.
fn vec_push_snippet() -> String {
    vcheck_code! {
        #[vcheck(T = u32)]
        #[verifier::external_body]
        pub exec fn vec_push<T>(v: &mut Vec<T>, x: T)
            ensures
                final(v)@ == old(v)@.push(x),
        {
            v.push(x);
        }
    }
}

test_vcheck_one_file! {
    #[test] vec_push vec_push_snippet() => HarnessOutcome::Pass { harnesses: 1 }
}

test_verify_one_file! {
    #[test] verify_vec_push vec_push_snippet() => VerifyOutcome::Verifies
}

test_vcheck_one_file! {
    #[test] vec_set_at_index vcheck_code! {
        #[vcheck(T = u32)]
        #[verifier::external_body]
        pub exec fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
            requires
                i < old(v)@.len(),
            ensures
                final(v)@ == old(v)@.update(i as int, x),
        {
            v[i] = x;
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] string_append vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn string_append(s: &mut String, t: &str)
            ensures
                final(s)@ == old(s)@ + t@,
        {
            s.push_str(t);
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] vec_clear vcheck_code! {
        #[vcheck(T = u32)]
        #[verifier::external_body]
        pub exec fn vec_clear<T>(v: &mut Vec<T>)
            ensures
                final(v)@.len() == 0,
        {
            v.clear();
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// A wrong `final`/`old` contract must be caught: this claims the pushed
// element lands at the FRONT. False for any sampled non-empty v.
test_vcheck_one_file! {
    #[test] wrong_mut_contract_is_caught vcheck_code! {
        #[vcheck(T = u32)]
        #[verifier::external_body]
        pub exec fn vec_push_wrong_contract<T>(v: &mut Vec<T>, x: T)
            ensures
                final(v)@ == seq![x] + old(v)@,
        {
            v.push(x);
        }
    } => HarnessOutcome::FailsHarness
}

// Mutable slice returns are copied into owned observations immediately after
// the call. This ends the borrow before final(v) is evaluated and lets
// cov_fuzz run non-failing length-preservation probes.
test_vcheck_one_file! {
    #[test] mutable_slice_return_is_observable vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        fn whole_mut_slice(v: &mut Vec<u8>) -> (r: &mut [u8])
            ensures
                r@ == old(v)@,
                final(r)@ == final(v)@,
        {
            v.as_mut_slice()
        }
    } => HarnessOutcome::PassWithCovFuzzReportContaining {
        harnesses: 1,
        needles: &[
            "strengthening candidate",
            "final(v).len() == old(v).len()",
        ],
    }
}

// Range-style mutable indexing returns a subslice. Its existing functional
// clause identifies the old subrange but does not syntactically claim that
// the base collection keeps its length, so the new return observation should
// surface the previously identified Range<usize>::index_mut candidate.
test_vcheck_one_file! {
    #[test] mutable_subrange_confirms_base_length_candidate vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        fn mutable_subrange(
            v: &mut Vec<u8>,
            start: usize,
            end: usize,
        ) -> (r: &mut [u8])
            requires
                start <= end,
                end <= v.len(),
            ensures
                r@ == old(v)@.subrange(start as int, end as int),
        {
            &mut v[start..end]
        }
    } => HarnessOutcome::PassWithCovFuzzReportContaining {
        harnesses: 1,
        needles: &["final(v).len() == old(v).len()"],
    }
}

// The tuple form exercises split_at_mut's two returned borrows. Both halves
// are snapshotted, after which the base Vec can be observed and the advisory
// left-boundary / total-length probes can run.
test_vcheck_one_file! {
    #[test] mutable_slice_pair_return_is_observable vcheck_code! {
        #[vcheck]
        #[vcheck_cov_fuzz]
        fn split_mut_slice(v: &mut Vec<u8>, mid: usize) -> (ret: (&mut [u8], &mut [u8]))
            requires
                mid <= v.len(),
            ensures
                ret.0@ == old(v)@.subrange(0, mid as int),
                ret.1@ == old(v)@.subrange(mid as int, old(v)@.len() as int),
                final(v)@ == final(ret.0)@ + final(ret.1)@,
        {
            v.as_mut_slice().split_at_mut(mid)
        }
    } => HarnessOutcome::PassWithCovFuzzReportContaining {
        harnesses: 1,
        needles: &[
            "final(v).len() == old(v).len()",
            "final(ret.0).len() == mid",
            "final(ret.0).len() + final(ret.1).len() == old(v).len()",
        ],
    }
}
