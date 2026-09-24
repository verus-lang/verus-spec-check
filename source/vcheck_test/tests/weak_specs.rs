mod common;
use common::*;

test_vcheck_one_file! {
    #[test] contract_strength_ladder vcheck_code! {
        #[vcheck_cov_mutate]
        #[vcheck]
        pub exec fn double_strong(r: u32) -> (out: u32)
            requires r <= u32::MAX / 2,
            ensures out == r * 2,
        {
            r * 2
        }

        // Predicate-only: "the result is even" — the vstd Result::map
        // style where the contract is a predicate the closure satisfies
        // rather than an exact value match.
        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn double_parity(r: u32) -> (out: u32)
            requires r <= u32::MAX / 2,
            ensures out % 2 == 0,
        {
            r * 2
        }

        // Tautological: mirrors `Result::map` when the closure has no
        // ensures at all — any value of the right type is permitted.
        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn double_vacuous(r: u32) -> (out: u32)
            requires r <= u32::MAX / 2,
            ensures out >= 0, // vacuous on u32
        {
            r * 2
        }
    } => HarnessOutcome::PassWithMutationReport { harnesses: 3 }
}

fn partial_eq_snippet() -> String {
    vcheck_code! {
        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn eq_vacuous(x: u32, y: u32) -> (b: bool)
            ensures b || !b, // tautology
        {
            x == y
        }

        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn eq_tight(x: u32, y: u32) -> (b: bool)
            ensures b == (x == y),
        {
            x == y
        }
    }
}

test_vcheck_one_file! {
    #[test] partial_eq_vacuous_vs_tight partial_eq_snippet()
        => HarnessOutcome::PassWithMutationReport { harnesses: 2 }
}

test_vcheck_one_file! {
    #[test] vec_index_loose_vs_tight vcheck_code! {
        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn vec_first_loose(vec: Vec<u32>) -> (out: u32)
            requires
                vec.len() >= 1,
            ensures
                // LOOSE: vacuous on u32, but mirrors the structural fact
                // that an existential without index-pinning doesn't
                // constrain the specific value returned.
                out >= 0,
        {
            vec[0]
        }

        #[vcheck_cov_mutate]
        #[vcheck]
        #[verifier::external_body]
        pub exec fn vec_first_tight(vec: Vec<u32>) -> (out: u32)
            requires
                vec.len() >= 1,
            ensures
                out == vec[0 as int],
        {
            vec[0]
        }
    } => HarnessOutcome::PassWithMutationReport { harnesses: 2 }
}

// Verify gate (what `tools/verify_examples.sh` covered for
// `examples/weak_specs/`).
test_verify_one_file! {
    #[test] verify_partial_eq_vacuous_vs_tight partial_eq_snippet()
        => VerifyOutcome::Verifies
}
