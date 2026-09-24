mod common;
use common::*;

// Shared snippet: harness gate + verify gate at the bottom of this file.
fn user_snippet() -> String {
    vcheck_code! {
        pub enum Permission {
            Read,
            Write,
            Admin,
            Revoked,
        }

        pub struct User {
            pub name_len: usize,
            pub perm: Permission,
            pub quota: u64,
        }

        impl Permission {
            pub open spec fn grants_write(&self) -> bool {
                match self {
                    Permission::Write => true,
                    Permission::Admin => true,
                    _ => false,
                }
            }

            pub open spec fn is_revoked(&self) -> bool {
                match self {
                    Permission::Revoked => true,
                    _ => false,
                }
            }
        }

        impl User {
            pub open spec fn is_valid_spec(&self) -> bool {
                &&& self.name_len > 0
                &&& !self.perm.is_revoked()
                &&& (self.perm.grants_write() ==> self.quota > 0)
            }

            #[vcheck]
            #[verifier::external_body]
            pub fn is_valid(&self) -> (b: bool)
                ensures b == self.is_valid_spec(),
            {
                self.name_len > 0
                    && !matches!(self.perm, Permission::Revoked)
                    && (!matches!(self.perm, Permission::Write | Permission::Admin)
                        || self.quota > 0)
            }
        }
    }
}

test_vcheck_one_file! {
    #[test] impl_method_closure user_snippet() => HarnessOutcome::Pass { harnesses: 1 }
}

// the spec-fn closure the preprocessing pass
// folds in must still verify.
test_verify_one_file! {
    #[test] verify_impl_method_closure user_snippet() => VerifyOutcome::Verifies
}

// checks only `name_len`, ignoring the revoked and quota clauses of
// the spec. Caught as soon as a Revoked (or write-without-quota) User is
// sampled.
test_vcheck_one_file! {
    #[test] buggy_validator_is_caught vcheck_code! {
        pub enum Permission {
            Read,
            Write,
            Admin,
            Revoked,
        }

        pub struct User {
            pub name_len: usize,
            pub perm: Permission,
            pub quota: u64,
        }

        impl Permission {
            pub open spec fn grants_write(&self) -> bool {
                match self {
                    Permission::Write => true,
                    Permission::Admin => true,
                    _ => false,
                }
            }

            pub open spec fn is_revoked(&self) -> bool {
                match self {
                    Permission::Revoked => true,
                    _ => false,
                }
            }
        }

        impl User {
            pub open spec fn is_valid_spec(&self) -> bool {
                &&& self.name_len > 0
                &&& !self.perm.is_revoked()
                &&& (self.perm.grants_write() ==> self.quota > 0)
            }

            #[vcheck]
            #[verifier::external_body]
            pub fn is_valid_buggy(&self) -> (b: bool)
                ensures b == self.is_valid_spec(),
            {
                self.name_len > 0 // BUG: drops the perm/quota clauses
            }
        }
    } => HarnessOutcome::FailsHarness
}
