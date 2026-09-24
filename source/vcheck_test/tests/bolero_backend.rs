mod common;
use common::*;

// Mode dispatch: the new `mode = "fuzz"` spelling, `mode = "kani"`, and
// the legacy `backend = "bolero"` spelling, all in one case so a
// regression in any one shows up together
test_bolero_one_file! {
    #[test] mode_spellings vcheck_code! {
        // New `mode = "fuzz"` spelling, primitive contract with a
        // precondition.
        #[vcheck(mode = "fuzz")]
        fn safe_double(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x + x
        }

        // Multi-param, no precondition.
        #[vcheck(mode = "fuzz")]
        fn triple_sum(a: u8, b: u8, c: u8) -> (r: u32)
            ensures r == a as u32 + b as u32 + c as u32,
        {
            a as u32 + b as u32 + c as u32
        }

        // `mode = "kani"`: same emitted harness as `mode = "fuzz"`,
        // intended for `cargo bolero test ... --engine kani`. Under plain
        // `cargo test` it runs as a random smoke test.
        #[vcheck(mode = "kani")]
        fn safe_add_kani(a: u16, b: u16) -> (r: u32)
            ensures r == a as u32 + b as u32,
        {
            a as u32 + b as u32
        }

        // Legacy spelling, and a zero-param fn: exercises the bolero
        // zero-parameter generator path (`with_generator(constant(()))`
        // plus a `|()|` closure).
        #[vcheck(backend = "bolero")]
        fn always_seven() -> (r: u32)
            ensures r == 7,
        {
            7
        }
    } => HarnessOutcome::Pass { harnesses: 4 }
}

// Relational precondition (requires-as-skip path) and collection
// generators.
test_bolero_one_file! {
    #[test] precondition_and_collections vcheck_code! {
        #[vcheck(backend = "bolero")]
        fn midpoint(a: u32, b: u32) -> (m: u32)
            requires a <= b,
            ensures a <= m, m <= b,
        {
            a + (b - a) / 2
        }

        #[vcheck(backend = "bolero")]
        fn append_vec(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
            ensures r.len() == a.len() + b.len(),
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
    } => HarnessOutcome::Pass { harnesses: 2 }
}

// `real` / float bridging on the bolero backend:
//   - integer -> real exact conversion and multiplication in the real
//     domain;
//   - float <-> real, where NaN / +-inf inputs are unspecified in Verus so
//     the harness skips them via the `reset_defined()` / `is_defined()`
//     guard rather than failing;
//   - real division plus `floor` bridging back to `int`, feeding an
//     integer-domain comparison.
test_bolero_one_file! {
    #[test] real_and_float_bridging vcheck_code! {
        #[vcheck(mode = "fuzz")]
        fn double_via_real(x: u32) -> (r: u64)
            ensures (r as real) == (x as real) * 2real,
        {
            x as u64 * 2
        }

        #[vcheck]
        fn float_identity(x: f64) -> (r: f64)
            ensures (r as real) == (x as real),
        {
            x
        }

        #[vcheck]
        fn half_floor(x: u32) -> (r: u32)
            ensures r as int == ((x as real) / 2real).floor(),
        {
            x / 2
        }
    } => HarnessOutcome::Pass { harnesses: 3 }
}

// A broken contract must be caught on the bolero backend too — otherwise
// the passing cases above can't distinguish "harness runs" from "harness
// is a no-op".
test_bolero_one_file! {
    #[test] broken_contract_is_caught vcheck_code! {
        #[vcheck(mode = "fuzz")]
        fn double_wrong(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x // BUG: not doubled
        }
    } => HarnessOutcome::FailsHarness
}
