mod common;
use common::*;

// Shared snippet: harness gate + verify gate at the bottom of this file.
fn u16_snippet() -> String {
    vcheck_code! {
        #[vcheck_provide]
        pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
            recommends s.len() == 2,
        {
            (s[0] as u16) | (s[1] as u16) << 8
        }

        #[vcheck_provide]
        pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8> {
            seq![
                (x & 0xff) as u8,
                ((x >> 8) & 0xff) as u8,
            ]
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u16_from_le_bytes(s: &[u8]) -> (x: u16)
            requires s@.len() == 2,
            ensures x == spec_u16_from_le_bytes(s@),
        {
            use core::convert::TryInto;
            u16::from_le_bytes(s.try_into().unwrap())
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u16_to_le_bytes(x: u16) -> (r: Vec<u8>)
            ensures
                r@ == spec_u16_to_le_bytes(x),
                r@.len() == 2,
        {
            x.to_le_bytes().to_vec()
        }
    }
}

test_vcheck_one_file! {
    #[test] u16_le_roundtrip u16_snippet() => HarnessOutcome::Pass { harnesses: 2 }
}

test_verify_one_file! {
    #[test] verify_u16_le_roundtrip u16_snippet() => VerifyOutcome::Verifies
}

test_vcheck_one_file! {
    #[test] u32_le_roundtrip vcheck_code! {
        pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
            recommends s.len() == 4,
        {
            (s[0] as u32) | (s[1] as u32) << 8 | (s[2] as u32) << 16 | (s[3] as u32) << 24
        }

        pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8> {
            seq![
                (x & 0xff) as u8,
                ((x >> 8) & 0xff) as u8,
                ((x >> 16) & 0xff) as u8,
                ((x >> 24) & 0xff) as u8,
            ]
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u32_from_le_bytes(s: &[u8]) -> (x: u32)
            requires s@.len() == 4,
            ensures x == spec_u32_from_le_bytes(s@),
        {
            use core::convert::TryInto;
            u32::from_le_bytes(s.try_into().unwrap())
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u32_to_le_bytes(x: u32) -> (r: Vec<u8>)
            ensures
                r@ == spec_u32_to_le_bytes(x),
                r@.len() == 4,
        {
            x.to_le_bytes().to_vec()
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] u64_le_roundtrip vcheck_code! {
        pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
            recommends s.len() == 8,
        {
            (s[0] as u64) | (s[1] as u64) << 8 | (s[2] as u64) << 16 | (s[3] as u64) << 24
                | (s[4] as u64) << 32 | (s[5] as u64) << 40 | (s[6] as u64) << 48
                | (s[7] as u64) << 56
        }

        pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8> {
            seq![
                (x & 0xff) as u8,
                ((x >> 8) & 0xff) as u8,
                ((x >> 16) & 0xff) as u8,
                ((x >> 24) & 0xff) as u8,
                ((x >> 32) & 0xff) as u8,
                ((x >> 40) & 0xff) as u8,
                ((x >> 48) & 0xff) as u8,
                ((x >> 56) & 0xff) as u8,
            ]
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u64_from_le_bytes(s: &[u8]) -> (x: u64)
            requires s@.len() == 8,
            ensures x == spec_u64_from_le_bytes(s@),
        {
            use core::convert::TryInto;
            u64::from_le_bytes(s.try_into().unwrap())
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u64_to_le_bytes(x: u64) -> (r: Vec<u8>)
            ensures
                r@ == spec_u64_to_le_bytes(x),
                r@.len() == 8,
        {
            x.to_le_bytes().to_vec()
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] u128_le_roundtrip vcheck_code! {
        pub closed spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
            recommends s.len() == 16,
        {
            (s[0] as u128) | (s[1] as u128) << 8 | (s[2] as u128) << 16 | (s[3] as u128) << 24
                | (s[4] as u128) << 32 | (s[5] as u128) << 40 | (s[6] as u128) << 48
                | (s[7] as u128) << 56 | (s[8] as u128) << 64 | (s[9] as u128) << 72
                | (s[10] as u128) << 80 | (s[11] as u128) << 88 | (s[12] as u128) << 96
                | (s[13] as u128) << 104 | (s[14] as u128) << 112 | (s[15] as u128) << 120
        }

        pub closed spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8> {
            seq![
                (x & 0xff) as u8,
                ((x >> 8) & 0xff) as u8,
                ((x >> 16) & 0xff) as u8,
                ((x >> 24) & 0xff) as u8,
                ((x >> 32) & 0xff) as u8,
                ((x >> 40) & 0xff) as u8,
                ((x >> 48) & 0xff) as u8,
                ((x >> 56) & 0xff) as u8,
                ((x >> 64) & 0xff) as u8,
                ((x >> 72) & 0xff) as u8,
                ((x >> 80) & 0xff) as u8,
                ((x >> 88) & 0xff) as u8,
                ((x >> 96) & 0xff) as u8,
                ((x >> 104) & 0xff) as u8,
                ((x >> 112) & 0xff) as u8,
                ((x >> 120) & 0xff) as u8,
            ]
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u128_from_le_bytes(s: &[u8]) -> (x: u128)
            requires s@.len() == 16,
            ensures x == spec_u128_from_le_bytes(s@),
        {
            use core::convert::TryInto;
            u128::from_le_bytes(s.try_into().unwrap())
        }

        #[vcheck]
        #[verifier::external_body]
        pub exec fn u128_to_le_bytes(x: u128) -> (r: Vec<u8>)
            ensures
                r@ == spec_u128_to_le_bytes(x),
                r@.len() == 16,
        {
            x.to_le_bytes().to_vec()
        }
    } => HarnessOutcome::Pass { harnesses: 2 }
}
