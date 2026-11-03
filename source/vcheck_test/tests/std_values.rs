mod common;
use common::*;

test_vcheck_one_file! {
    #[test] range_contains_passes vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn range_contains(r: core::ops::Range<usize>, i: usize) -> (b: bool)
            ensures
                b == (r.start <= i && i < r.end),
        {
            r.contains(&i)
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] range_next_mut_passes vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn range_next(r: &mut core::ops::Range<u8>) -> (ret: Option<u8>)
            ensures
                old(r).start < old(r).end ==> ret == Some(old(r).start)
                    && final(r).start as int == old(r).start as int + 1
                    && final(r).end == old(r).end,
                old(r).start >= old(r).end ==> ret is None && final(r).start == old(r).start,
        {
            r.next()
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] slice_get_range_passes vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn slice_get_range(s: &[u8], r: core::ops::Range<usize>) -> (out: Option<usize>)
            ensures
                out is Some <==> (r.start <= r.end && r.end <= s@.len()),
                out is Some ==> out->Some_0 as int == r.end as int - r.start as int,
        {
            s.get(r).map(|x| x.len())
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] slice_index_generic_instantiation_passes vcheck_code! {
        #[vcheck(I = core::ops::RangeTo<usize>)]
        #[verifier::external_body]
        pub exec fn slice_get_prefix<I: core::slice::SliceIndex<[u8], Output = [u8]>>(
            s: &[u8],
            i: I,
        ) -> (out: Option<usize>)
            ensures
                out is Some ==> out->Some_0 <= s@.len(),
        {
            s.get(i).map(|x| x.len())
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] str_get_range_ignoring_char_boundaries_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn str_get_range(s: &str, r: core::ops::Range<usize>) -> (out: Option<String>)
            ensures
                out is Some <==> (r.start <= r.end && r.end <= s.len()),
        {
            s.get(r).map(|x| x.to_string())
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] range_inclusive_is_empty_matches_vstd_spec vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn range_inclusive_is_empty(r: &core::ops::RangeInclusive<u8>) -> (res: bool)
            ensures
                res == (!(r@.start <= r@.end) || r@.exhausted),
        {
            r.is_empty()
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] range_inclusive_is_empty_forgetting_exhaustion_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn range_inclusive_is_empty_wrong(r: &core::ops::RangeInclusive<u8>) -> (res: bool)
            ensures
                res == (r@.start > r@.end),
        {
            r.is_empty()
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] range_inclusive_new_view_passes vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn range_inclusive_new(start: u16, end: u16) -> (ret: core::ops::RangeInclusive<u16>)
            ensures
                ret@.start == start,
                ret@.end == end,
                !ret@.exhausted,
        {
            core::ops::RangeInclusive::new(start, end)
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// vstd's `in_bounds` normalizes an exhausted `e..=e` to `e..e`, std to `(e+1)..(e+1)`
test_vcheck_one_file! {
    #[test] vstd_exhausted_range_inclusive_in_bounds_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn slice_get_inclusive_vstd(s: &[u8], r: core::ops::RangeInclusive<usize>) -> (out: Option<usize>)
            requires
                r@.exhausted,
                s@.len() == 0,
            ensures
                out is Some <==> (r@.start <= r@.end && r@.end <= s@.len()),
        {
            s.get(r).map(|x| x.len())
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] ordering_reverse_and_then_pass vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn ordering_reverse(o: core::cmp::Ordering) -> (r: core::cmp::Ordering)
            ensures
                o == core::cmp::Ordering::Less ==> r == core::cmp::Ordering::Greater,
                o == core::cmp::Ordering::Equal ==> r == core::cmp::Ordering::Equal,
                o == core::cmp::Ordering::Greater ==> r == core::cmp::Ordering::Less,
        {
            o.reverse()
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn ordering_then(a: core::cmp::Ordering, b: core::cmp::Ordering) -> (r: core::cmp::Ordering)
            ensures
                a != core::cmp::Ordering::Equal ==> r == a,
                a == core::cmp::Ordering::Equal ==> r == b,
        {
            a.then(b)
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] nonzero_new_and_get_pass vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn nonzero_new_u32(n: u32) -> (ret: Option<core::num::NonZero<u32>>)
            ensures
                ret is Some <==> n != 0,
                ret is Some ==> ret->Some_0.get() == n,
        {
            core::num::NonZero::new(n)
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn nonzero_get(n: core::num::NonZero<u8>) -> (r: u8)
            ensures
                r == n@,
                r != 0,
        {
            n.get()
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] nonzero_signed_abs_at_min_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn nonzero_checked_abs(n: core::num::NonZero<i32>) -> (r: Option<core::num::NonZero<i32>>)
            ensures
                r is Some ==> r->Some_0@ > 0,
                r is Some,
        {
            n.checked_abs()
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] char_len_utf8_off_by_one_boundaries_are_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn char_len_utf8_wrong(c: char) -> (n: usize)
            ensures
                (c as u32) <= 0x80 ==> n == 1,
                0x80 < (c as u32) && (c as u32) <= 0x800 ==> n == 2,
                0x800 < (c as u32) && (c as u32) <= 0x10000 ==> n == 3,
                0x10000 < (c as u32) ==> n == 4,
        {
            c.len_utf8()
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] char_ascii_only_whitespace_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn char_is_whitespace_wrong(c: char) -> (r: bool)
            ensures
                r == (c == ' ' || c == '\t' || c == '\n' || c == '\u{b}' || c == '\u{c}' || c == '\r'),
        {
            c.is_whitespace()
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] string_interior_nul_is_caught vcheck_code! {
        #[vcheck]
        #[verifier::external_body]
        pub exec fn c_string_len(s: &str) -> (r: Option<usize>)
            ensures
                r is Some,
        {
            std::ffi::CString::new(s).ok().map(|c| c.as_bytes().len())
        }
    } => HarnessOutcome::FailsHarness
}

test_vcheck_one_file! {
    #[test] zst_append_exact_max_sum_passes vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vec_append_guarded<T>(v: &mut Vec<T>, other: &mut Vec<T>)
            requires
                old(v)@.len() + old(other)@.len() <= usize::MAX,
            ensures
                final(v)@ == old(v)@ + old(other)@,
                final(other)@ == Seq::<T>::empty(),
        {
            v.append(other);
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

test_vcheck_one_file! {
    #[test] zst_u32_truncation_guard_off_by_one_is_caught vcheck_code! {
        #[vcheck(T = ())]
        #[verifier::external_body]
        pub exec fn vec_len_u32<T>(v: Vec<T>) -> (n: u32)
            requires
                v@.len() <= 0x1_0000_0000,
            ensures
                n as int == v@.len(),
        {
            v.len() as u32
        }
    } => HarnessOutcome::FailsHarness
}

test_bolero_one_file! {
    #[test] bolero_std_values_pass vcheck_code! {
        #[vcheck(mode = "fuzz")]
        #[verifier::external_body]
        pub exec fn fuzz_slice_get(s: &[u8], r: core::ops::Range<usize>) -> (out: Option<usize>)
            ensures
                out is Some <==> (r.start <= r.end && r.end <= s@.len()),
        {
            s.get(r).map(|x| x.len())
        }

        #[vcheck(mode = "fuzz")]
        #[verifier::external_body]
        pub exec fn fuzz_is_empty(r: &core::ops::RangeInclusive<u8>) -> (res: bool)
            ensures
                res == (!(r@.start <= r@.end) || r@.exhausted),
        {
            r.is_empty()
        }

        #[vcheck(mode = "fuzz")]
        #[verifier::external_body]
        pub exec fn fuzz_nonzero_get(n: core::num::NonZero<u16>, o: core::cmp::Ordering) -> (r: u16)
            ensures
                r == n@,
        {
            n.get()
        }
    } => HarnessOutcome::Pass { harnesses: 3 }
}

test_bolero_one_file! {
    #[test] bolero_exhausted_range_is_caught vcheck_code! {
        #[vcheck(mode = "fuzz")]
        #[verifier::external_body]
        pub exec fn fuzz_is_empty_wrong(r: &core::ops::RangeInclusive<u8>) -> (res: bool)
            ensures
                res == (r@.start > r@.end),
        {
            r.is_empty()
        }
    } => HarnessOutcome::FailsHarness
}
