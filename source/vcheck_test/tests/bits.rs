//! Validates that the trusted implementations behind
//! `<uXX>::{trailing,leading}_{zeros,ones}` match the recursive Verus
//! spec definitions in `vstd::std_specs::bits`. Verus *axiomatizes* that
//! equivalence via `assume_specification`.

mod common;
use common::*;

// Shared snippet, driven by BOTH the harness gate and the verify gate at
// the bottom of this file, so the two can't drift apart.
fn u8_snippet() -> String {
    vcheck_code! {
        #[vcheck_provide]
        pub closed spec fn u8_tz(i: u8) -> u32
            decreases i,
        {
            if i == 0 { 8 }
            else if (i & 1) != 0 { 0 }
            else { (1 + u8_tz(i / 2)) as u32 }
        }

        #[vcheck_provide]
        pub closed spec fn u8_lz(i: u8) -> u32
            decreases i,
        {
            if i == 0 { 8 } else { (u8_lz(i / 2) - 1) as u32 }
        }

        #[vcheck_provide]
        pub open spec fn u8_to(i: u8) -> u32 { u8_tz(!i) }

        #[vcheck_provide]
        pub open spec fn u8_lo(i: u8) -> u32 { u8_lz(!i) }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u8_tz(i: u8) -> (r: u32) ensures r == u8_tz(i), { i.trailing_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u8_lz(i: u8) -> (r: u32) ensures r == u8_lz(i), { i.leading_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u8_to(i: u8) -> (r: u32) ensures r == u8_to(i), { i.trailing_ones() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u8_lo(i: u8) -> (r: u32) ensures r == u8_lo(i), { i.leading_ones() }
    }
}

test_vcheck_one_file! {
    #[test] u8_bit_counts u8_snippet() => HarnessOutcome::Pass { harnesses: 4 }
}

test_verify_one_file! {
    #[test] verify_u8_bit_counts u8_snippet() => VerifyOutcome::Verifies
}

test_vcheck_one_file! {
    #[test] u16_bit_counts vcheck_code! {
        #[vcheck_provide]
        pub closed spec fn u16_tz(i: u16) -> u32
            decreases i,
        {
            if i == 0 { 16 }
            else if (i & 1) != 0 { 0 }
            else { (1 + u16_tz(i / 2)) as u32 }
        }

        #[vcheck_provide]
        pub closed spec fn u16_lz(i: u16) -> u32
            decreases i,
        {
            if i == 0 { 16 } else { (u16_lz(i / 2) - 1) as u32 }
        }

        #[vcheck_provide]
        pub open spec fn u16_to(i: u16) -> u32 { u16_tz(!i) }

        #[vcheck_provide]
        pub open spec fn u16_lo(i: u16) -> u32 { u16_lz(!i) }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u16_tz(i: u16) -> (r: u32) ensures r == u16_tz(i), { i.trailing_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u16_lz(i: u16) -> (r: u32) ensures r == u16_lz(i), { i.leading_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u16_to(i: u16) -> (r: u32) ensures r == u16_to(i), { i.trailing_ones() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u16_lo(i: u16) -> (r: u32) ensures r == u16_lo(i), { i.leading_ones() }
    } => HarnessOutcome::Pass { harnesses: 4 }
}

test_vcheck_one_file! {
    #[test] u32_bit_counts vcheck_code! {
        #[vcheck_provide]
        pub closed spec fn u32_tz(i: u32) -> u32
            decreases i,
        {
            if i == 0 { 32 }
            else if (i & 1) != 0 { 0 }
            else { (1 + u32_tz(i / 2)) as u32 }
        }

        #[vcheck_provide]
        pub closed spec fn u32_lz(i: u32) -> u32
            decreases i,
        {
            if i == 0 { 32 } else { (u32_lz(i / 2) - 1) as u32 }
        }

        #[vcheck_provide]
        pub open spec fn u32_to(i: u32) -> u32 { u32_tz(!i) }

        #[vcheck_provide]
        pub open spec fn u32_lo(i: u32) -> u32 { u32_lz(!i) }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u32_tz(i: u32) -> (r: u32) ensures r == u32_tz(i), { i.trailing_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u32_lz(i: u32) -> (r: u32) ensures r == u32_lz(i), { i.leading_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u32_to(i: u32) -> (r: u32) ensures r == u32_to(i), { i.trailing_ones() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u32_lo(i: u32) -> (r: u32) ensures r == u32_lo(i), { i.leading_ones() }
    } => HarnessOutcome::Pass { harnesses: 4 }
}

test_vcheck_one_file! {
    #[test] u64_bit_counts vcheck_code! {
        #[vcheck_provide]
        pub closed spec fn u64_tz(i: u64) -> u32
            decreases i,
        {
            if i == 0 { 64 }
            else if (i & 1) != 0 { 0 }
            else { (1 + u64_tz(i / 2)) as u32 }
        }

        #[vcheck_provide]
        pub closed spec fn u64_lz(i: u64) -> u32
            decreases i,
        {
            if i == 0 { 64 } else { (u64_lz(i / 2) - 1) as u32 }
        }

        #[vcheck_provide]
        pub open spec fn u64_to(i: u64) -> u32 { u64_tz(!i) }

        #[vcheck_provide]
        pub open spec fn u64_lo(i: u64) -> u32 { u64_lz(!i) }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u64_tz(i: u64) -> (r: u32) ensures r == u64_tz(i), { i.trailing_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u64_lz(i: u64) -> (r: u32) ensures r == u64_lz(i), { i.leading_zeros() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u64_to(i: u64) -> (r: u32) ensures r == u64_to(i), { i.trailing_ones() }

        #[vcheck]
        #[verifier::external_body]
        pub fn vcheck_u64_lo(i: u64) -> (r: u32) ensures r == u64_lo(i), { i.leading_ones() }
    } => HarnessOutcome::Pass { harnesses: 4 }
}
