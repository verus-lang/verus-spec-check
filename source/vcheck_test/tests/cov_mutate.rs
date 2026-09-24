mod common;
use common::*;

// Strong vs. loose ensures on the same `x + x` body. Shared snippet:
// harness gate + verify gate at the bottom of this file.
fn double_pair_snippet() -> String {
    vcheck_code! {
        #[vcheck]
        #[vcheck_cov_mutate]
        fn strong_double(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            ensures r == x * 2,
        {
            x + x
        }

        #[vcheck]
        #[vcheck_cov_mutate]
        fn weak_double(x: u32) -> (r: u32)
            requires x <= u32::MAX / 2,
            // Looser ensures: mutations that still satisfy it survive.
            ensures r >= x,
        {
            x + x
        }
    }
}

test_vcheck_one_file! {
    #[test] strong_vs_weak_double double_pair_snippet()
        => HarnessOutcome::PassWithMutationReport { harnesses: 2 }
}

test_verify_one_file! {
    #[test] verify_strong_vs_weak_double double_pair_snippet()
        => VerifyOutcome::Verifies
}

// Multi-arg shape, strong vs. bound-only ensures.
test_vcheck_one_file! {
    #[test] strong_vs_weak_triple_sum vcheck_code! {
        #[vcheck]
        #[vcheck_cov_mutate]
        fn triple_sum_strong(a: u8, b: u8, c: u8) -> (r: u32)
            ensures r == a as u32 + b as u32 + c as u32,
        {
            a as u32 + b as u32 + c as u32
        }

        #[vcheck]
        #[vcheck_cov_mutate]
        fn triple_sum_weak(a: u8, b: u8, c: u8) -> (r: u32)
            // Loose ensures — sum bound only.
            ensures r <= 3 * 255u32,
        {
            a as u32 + b as u32 + c as u32
        }
    } => HarnessOutcome::PassWithMutationReport { harnesses: 2 }
}

// Mixed widths and a signed shape.
test_vcheck_one_file! {
    #[test] pack_and_signed vcheck_code! {
        #[vcheck]
        #[vcheck_cov_mutate]
        fn pack_u16(hi: u8, lo: u8) -> (r: u16)
            ensures r == ((hi as u16) * 256u16 + (lo as u16)) as u16,
        {
            (hi as u16) * 256 + (lo as u16)
        }

        #[vcheck]
        #[vcheck_cov_mutate]
        fn signed_double(x: i32) -> (r: i32)
            requires
                x >= -(i32::MAX / 2),
                x <= i32::MAX / 2,
            ensures r == x * 2,
        {
            x + x
        }
    } => HarnessOutcome::PassWithMutationReport { harnesses: 2 }
}
