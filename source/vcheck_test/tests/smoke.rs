mod common;
use common::*;

test_vcheck_one_file! {
    #[test] primitives_and_vec vcheck_code! {
        verus_spec_check_unverified! {
            spec fn small_enough(s: Seq<i64>) -> bool {
                s.len() <= 16
            }

            spec fn appended(a: Seq<i64>, b: Seq<i64>, r: Seq<i64>) -> bool {
                r.len() == a.len() + b.len()
            }

            fn append_vec(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
                requires
                    small_enough(a.deep_view()),
                    small_enough(b.deep_view()),
                ensures
                    appended(a.deep_view(), b.deep_view(), r.deep_view()),
            {
                let mut r: Vec<i64> = Vec::new();
                let mut i: usize = 0;
                while i < a.len()
                    invariant
                        i <= a.len(),
                        r.len() == i,
                    decreases a.len() - i,
                {
                    r.push(a[i]);
                    i += 1;
                }
                let mut j: usize = 0;
                while j < b.len()
                    invariant
                        j <= b.len(),
                        r.len() == a.len() + j,
                    decreases b.len() - j,
                {
                    r.push(b[j]);
                    j += 1;
                }
                r
            }

            // inline `forall` lifted to a synthetic spec fn
            fn make_zeros(n: u8) -> (r: Vec<i64>)
                ensures
                    r.len() == n as usize,
                    forall |i: usize| 0 <= i < r.len() ==> r[i as int] == 0,
            {
                let mut v: Vec<i64> = Vec::new();
                let mut i: u8 = 0;
                while i < n
                    invariant
                        i <= n,
                        v.len() == i as usize,
                        forall |k: usize| 0 <= k < v.len() ==> v[k as int] == 0,
                    decreases n - i,
                {
                    v.push(0);
                    i += 1;
                }
                v
            }
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] struct_and_enum vcheck_code! {
        verus_spec_check_unverified! {
            pub struct Pair {
                pub a: u8,
                pub b: u8,
            }

            pub enum Choice {
                Left,
                Right(u32),
                Both { x: i32, y: i32 },
            }

            spec fn pair_eq(p: Pair, x: u8, y: u8) -> bool {
                p.a == x && p.b == y
            }

            fn echo_pair(p: &Pair) -> (r: bool)
                ensures pair_eq(*p, p.a, p.b) == r,
            {
                true
            }

            spec fn choice_picks_zero(c: Choice) -> bool {
                match c {
                    Choice::Left => true,
                    Choice::Right(n) => n == 0u32,
                    Choice::Both { x, y } => x == 0 && y == 0,
                }
            }

            fn always_pass(c: &Choice) -> (r: bool)
                ensures r == true,
            {
                let _ = c;
                true
            }
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] verified_first vcheck_code! {
        verus_spec_check_verified! {
            spec fn nonempty(s: Seq<i64>) -> bool {
                s.len() > 0
            }

            fn first(s: &[i64]) -> (r: i64)
                requires nonempty(s.deep_view()),
                ensures r == s.deep_view()[0],
            {
                s[0]
            }
        }
    } => HarnessOutcome::Pass { harnesses: 1 }
}

// Exercises the FailsHarness outcome (the machinery that replaces the
// EXPECTED_FAIL list in run_examples.sh). Same spec shapes as
// `primitives_and_vec`, but the impl drops `b` entirely, violating the
// length ensures.
test_vcheck_one_file! {
    #[test] broken_append_is_caught vcheck_code! {
        verus_spec_check_unverified! {
            spec fn small_enough(s: Seq<i64>) -> bool {
                s.len() <= 16
            }

            spec fn appended(a: Seq<i64>, b: Seq<i64>, r: Seq<i64>) -> bool {
                r.len() == a.len() + b.len()
            }

            fn append_wrong(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
                requires
                    small_enough(a.deep_view()),
                    small_enough(b.deep_view()),
                ensures
                    appended(a.deep_view(), b.deep_view(), r.deep_view()),
            {
                let _ = b; // BUG: b is never appended
                let mut r: Vec<i64> = Vec::new();
                let mut i: usize = 0;
                while i < a.len()
                    invariant
                        i <= a.len(),
                        r.len() == i,
                    decreases a.len() - i,
                {
                    r.push(a[i]);
                    i += 1;
                }
                r
            }
        }
    } => HarnessOutcome::FailsHarness
}

// Verify sweep coverage.
test_verify_one_file! {
    #[test] verify_first vcheck_code! {
        verus_spec_check_verified! {
            spec fn nonempty(s: Seq<i64>) -> bool {
                s.len() > 0
            }

            fn first(s: &[i64]) -> (r: i64)
                requires nonempty(s.deep_view()),
                ensures r == s.deep_view()[0],
            {
                s[0]
            }
        }
    } => VerifyOutcome::Verifies
}
