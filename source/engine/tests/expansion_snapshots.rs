//! Golden-file expansion snapshots for the vcheck engine.
//!
//! These tests pin the exact token output of the three public engine
//! entry points (`vcheck_provide_preprocess`, `expand_verus_spec_check`,
//! `expand_exec_spec`) for a set of representative inputs drawn from
//! the `examples/` crates. They exist to make refactors of the engine
//! internals provably behavior-preserving: any change to emitted
//! tokens shows up as a snapshot diff.
//!
//! ## Updating snapshots
//!
//! ```bash
//! UPDATE_VCHECK_SNAPSHOTS=1 cargo test -p verus_spec_check_engine --test expansion_snapshots
//! ```
//!
//! Review the diff of `tests/snapshots/` before accepting.
//!
//! ## Determinism notes
//!
//! - The engine's `expand` entry point draws module ids from a
//!   process-global counter, so all cases run inside ONE `#[test]`
//!   in a fixed order, and `__verus_spec_check_<n>` ids are normalized to
//!   `__verus_spec_check_ID` in the stored snapshots anyway (belt and
//!   suspenders).
//! - Snapshots are stored pretty-printed (brace-indented token text)
//!   so mismatches produce reviewable diffs.

use proc_macro2::TokenStream;

// ---------------------------------------------------------------------------
// Input parsing
// ---------------------------------------------------------------------------

/// Parse a source string into the `Vec<verus_syn::Item>` shape that
/// `vcheck_provide_preprocess` consumes (i.e. the items inside `verus!{}`).
fn parse_items(src: &str) -> Vec<verus_syn::Item> {
    use verus_syn::parse::Parser;
    let ts: TokenStream = src
        .parse()
        .unwrap_or_else(|e| panic!("tokenize failed: {e}"));
    let parser = |input: verus_syn::parse::ParseStream| {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse::<verus_syn::Item>()?);
        }
        Ok(items)
    };
    parser
        .parse2(ts)
        .unwrap_or_else(|e| panic!("parse items failed: {e}"))
}

// ---------------------------------------------------------------------------
// Snapshot rendering
// ---------------------------------------------------------------------------

/// Render a token stream as brace-indented text so snapshot diffs are
/// reviewable. Purely syntactic: no token is added, dropped, or
/// reordered. Shared with the `VERUS_SPEC_CHECK_EXPAND_DIR` dump hook behind
/// `cargo vcheck expand` — one renderer, so snapshots and dumps agree.
fn pretty(ts: &TokenStream) -> String {
    verus_spec_check_engine::pretty_tokens(ts)
}

/// Normalize counter-derived harness-module ids (`__verus_spec_check_<n>`)
/// so snapshots don't depend on how many expansions ran before.
fn normalize(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    const NEEDLE: &str = "__verus_spec_check_";
    while let Some(pos) = rest.find(NEEDLE) {
        let after = pos + NEEDLE.len();
        let tail = &rest[after..];
        let digits = tail.chars().take_while(|c| c.is_ascii_digit()).count();
        if digits > 0 {
            out.push_str(&rest[..after]);
            out.push_str("ID");
            rest = &tail[digits..];
        } else {
            out.push_str(&rest[..after]);
            rest = tail;
        }
    }
    out.push_str(rest);
    out
}

// ---------------------------------------------------------------------------
// Golden-file plumbing
// ---------------------------------------------------------------------------

fn snapshot_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("snapshots")
}

/// Compare `actual` against the stored golden file, or (re)write it when
/// `UPDATE_VCHECK_SNAPSHOTS` is set. Returns an error message on mismatch.
fn check_snapshot(name: &str, actual: &str) -> Result<(), String> {
    let path = snapshot_dir().join(format!("{name}.snap"));
    if std::env::var("UPDATE_VCHECK_SNAPSHOTS").is_ok() {
        std::fs::create_dir_all(snapshot_dir()).expect("create snapshot dir");
        std::fs::write(&path, actual).expect("write snapshot");
        return Ok(());
    }
    let expected = std::fs::read_to_string(&path).map_err(|_| {
        format!(
            "snapshot `{name}` missing at {}; run with UPDATE_VCHECK_SNAPSHOTS=1 to create it",
            path.display()
        )
    })?;
    if expected == actual {
        return Ok(());
    }
    // Locate the first differing line for a focused failure message.
    let mut line_no = 1usize;
    let mut exp_lines = expected.lines();
    let mut act_lines = actual.lines();
    loop {
        match (exp_lines.next(), act_lines.next()) {
            (Some(e), Some(a)) if e == a => line_no += 1,
            (e, a) => {
                return Err(format!(
                    "snapshot `{name}` mismatch at line {line_no}:\n  expected: {}\n  actual:   {}\n\
                     (full golden file: {})",
                    e.unwrap_or("<eof>"),
                    a.unwrap_or("<eof>"),
                    path.display()
                ));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Cases
// ---------------------------------------------------------------------------

struct Case {
    name: &'static str,
    src: &'static str,
    /// Also run `expand_verus_spec_check` on the folded engine block(s) found
    /// in the preprocessed output.
    expand: bool,
}

const CASES: &[Case] = &[
    // Free fn + Vec/slice params + spec fns.
    Case {
        name: "smoke_free_fn_vec",
        expand: true,
        src: r#"
            spec fn small_enough(s: Seq<i64>) -> bool {
                s.len() <= 16
            }

            spec fn appended(a: Seq<i64>, b: Seq<i64>, r: Seq<i64>) -> bool {
                r.len() == a.len() + b.len()
            }

            #[vcheck]
            fn append_vec(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
                requires
                    small_enough(a.deep_view()),
                    small_enough(b.deep_view()),
                ensures
                    appended(a.deep_view(), b.deep_view(), r.deep_view()),
            {
                let mut r: Vec<i64> = Vec::new();
                r
            }
        "#,
    },
    // Inline forall in ensures, lifted to a synthetic spec fn.
    Case {
        name: "inline_forall_lift",
        expand: true,
        src: r#"
            #[vcheck]
            fn make_zeros(n: u8) -> (r: Vec<i64>)
                ensures
                    r.len() == n as usize,
                    forall |i: usize| 0 <= i < r.len() ==> r[i as int] == 0,
            {
                Vec::new()
            }
        "#,
    },
    // User struct + enum + spec impls + #[vcheck] method.
    Case {
        name: "user_struct_enum_closure",
        expand: true,
        src: r#"
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
                    true
                }
            }
        "#,
    },
    // Generic fn with a #[vcheck(T = u32)] instantiation; mirrors examples/mut.
    Case {
        name: "generic_subst_mut_param",
        expand: true,
        src: r#"
            #[vcheck(T = u32)]
            fn overwrite<T: Copy>(x: &mut T, v: T)
                ensures *x == v,
            {
                *x = v;
            }
        "#,
    },
    // &mut param with old(); exercises the old/final rewrite path.
    Case {
        name: "mut_param_old",
        expand: true,
        src: r#"
            #[vcheck]
            fn bump(x: &mut u32)
                requires *old(x) < 1000,
                ensures *x == *old(x) + 1,
            {
                *x = *x + 1;
            }
        "#,
    },
    // external_vcheck_provide!: trusted exec twin for an external spec fn.
    Case {
        name: "external_vcheck_provide",
        expand: true,
        src: r#"
            external_vcheck_provide! {
                fn is_sorted(s: Seq<i64>) -> bool {
                    let mut i = 0;
                    while i + 1 < s.len() {
                        if s[i] > s[i + 1] {
                            return false;
                        }
                        i += 1;
                    }
                    true
                }
            }

            #[vcheck]
            #[verifier::external_body]
            pub fn is_input_sorted(s: &[i64]) -> (b: bool)
                ensures b == is_sorted(s.deep_view()),
            {
                true
            }
        "#,
    },
    // Unresolved external spec fn: pins the tier-aware diagnostic text.
    Case {
        name: "diag_unresolved_spec_fn",
        expand: false,
        src: r#"
            #[vcheck]
            fn sort_it(v: &mut Vec<i64>)
                ensures is_sorted(v.deep_view()),
            {
            }
        "#,
    },
    // `#[vcheck]` on a fn with NO contract clauses must be a hard compile
    // error, not a silent no-harness expansion: during spec ablation
    // (commenting out ensures), the fn used to drop out of the pipeline
    // entirely — no `vcheck_<fn>` harness, dead-code warning on the fn,
    // green run. The sentinel-based check in classify pins the failure.
    Case {
        name: "diag_vcheck_no_contract",
        expand: true,
        src: r#"
            #[vcheck]
            fn forgot_contract(a: u8, b: u8) -> (r: u8)
            {
                if a >= b { a - b } else { b - a }
            }
        "#,
    },
    // Method shape of the same diagnostic (scoped to the method's own
    // marker, so unmarked helper methods in a folded impl stay exempt).
    Case {
        name: "diag_vcheck_no_contract_method",
        expand: true,
        src: r#"
            pub struct Counter { pub v: u8 }

            impl Counter {
                #[vcheck]
                pub fn get(&self) -> u8 {
                    self.v
                }
            }
        "#,
    },
    // Bolero backend selection via mode = "fuzz".
    Case {
        name: "bolero_mode_fuzz",
        expand: true,
        src: r#"
            #[vcheck(mode = "fuzz")]
            fn safe_double(x: u16) -> (r: u32)
                ensures r == 2 * x as u32,
            {
                2 * x as u32
            }
        "#,
    },
    // mode = "kani": pins the plain bolero harness (kani::proof attr,
    // kani::assume lowering) PLUS the `__vcheck_kani_report` orchestration
    // test that makes plain `cargo test` drive `cargo kani --tests`.
    Case {
        name: "bolero_mode_kani",
        expand: true,
        src: r#"
            #[vcheck(mode = "kani")]
            fn safe_add(a: u16, b: u16) -> (r: u32)
                requires a <= 1000,
                ensures r == a as u32 + b as u32,
            {
                a as u32 + b as u32
            }
        "#,
    },
    // mode = "fuzz" with a precondition and a branching body: pins the
    // guided-loop half of the cfg-split harness — instrumented twin +
    // hit bits (branch feedback), requires -> guidance-bit lowering,
    // ensures -> `ContractExec::Failed` with the original clause text.
    Case {
        name: "bolero_mode_fuzz_guided",
        expand: true,
        src: r#"
            #[vcheck(mode = "fuzz")]
            fn bounded_abs_diff(a: u8, b: u8) -> (r: u8)
                requires a <= 200,
                ensures
                    a >= b ==> r == a - b,
                    a < b ==> r == b - a,
            {
                if a >= b {
                    a - b
                } else {
                    b - a
                }
            }
        "#,
    },
    // #[vcheck] + #[vcheck_cov_mutate] mutation-testing harness.
    Case {
        name: "cov_mutate",
        expand: true,
        src: r#"
            #[vcheck]
            #[vcheck_cov_mutate]
            fn strong_double(x: u32) -> (r: u32)
                requires x <= u32::MAX / 2,
                ensures r == x * 2,
            {
                x + x
            }
        "#,
    },
    // #[vcheck] + #[vcheck_cov_fuzz] branch-coverage harness: instrumented
    // twin + coverage-guided runner + report test. The body exercises
    // if/else and `&&` short-circuit sites; the requires clause becomes
    // a guidance-bit lowering in the runner.
    Case {
        name: "cov_fuzz",
        expand: true,
        src: r#"
            #[vcheck]
            #[vcheck_cov_fuzz]
            fn clamp_sum(a: u8, b: u8) -> (r: u16)
                requires a as u16 + b as u16 <= 400,
                ensures r == a as u16 + b as u16,
            {
                if a > 10 && b > 10 {
                    a as u16 + b as u16
                } else {
                    a as u16 + b as u16
                }
            }
        "#,
    },
    // #[vcheck_cov_fuzz] on an assume_specification: the synthesized
    // wrapper carries the target-path sentinel, so the cov_fuzz target
    // is classified as EXTERNAL — no instrumented twin / marker /
    // guided runner is emitted, just the stub + a target decl whose
    // `external` field carries the wrapped path for the side-profile
    // measurement.
    Case {
        name: "cov_fuzz_assume_spec_external",
        expand: true,
        src: r#"
            #[vcheck]
            #[vcheck_cov_fuzz]
            pub assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
                ensures
                    r.is_some() ==> r.unwrap() == x + y,
                    r.is_none() ==> x + y > u32::MAX,
            ;
        "#,
    },
    // assume_specification wrapper synthesis (concrete instantiation).
    Case {
        name: "assume_spec_wrapper",
        expand: true,
        src: r#"
            #[vcheck(T = u32)]
            pub assume_specification<T> [Vec::<T>::clear] (v: &mut Vec<T>)
                ensures v.deep_view().len() == 0;
        "#,
    },
    // Generic assume_specification with no instantiation: pins the
    // "needs concrete types" diagnostic.
    Case {
        name: "diag_generic_no_instantiation",
        expand: false,
        src: r#"
            #[vcheck]
            pub assume_specification<T> [Vec::<T>::clear] (v: &mut Vec<T>)
                ensures v.deep_view().len() == 0;
        "#,
    },
    // Inline #[vcheck] assert inside a fn body.
    Case {
        name: "inline_assert",
        expand: true,
        src: r#"
            fn checked_add(a: u16, b: u16) -> (r: u32)
                ensures r == a as u32 + b as u32,
            {
                let r = a as u32 + b as u32;
                #[vcheck]
                assert(r >= a as u32);
                r
            }
        "#,
    },
];

/// exec_spec lowering cases fed straight to `expand_exec_spec`.
const EXEC_SPEC_CASES: &[Case] = &[
    Case {
        name: "exec_spec_seq_ops",
        expand: false,
        src: r#"
            spec fn total(s: Seq<u32>) -> int
                decreases s.len(),
            {
                if s.len() == 0 { 0 } else { s[0] + total(s.skip(1)) }
            }
        "#,
    },
    Case {
        name: "exec_spec_quantifier",
        expand: false,
        src: r#"
            spec fn all_small(s: Seq<u32>) -> bool {
                forall |i: int| 0 <= i < s.len() ==> s[i] < 100
            }
        "#,
    },
];

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

/// Extract the token bodies of every folded `verus_spec_check_unverified!` /
/// `verus_spec_check_verified!` invocation in the preprocessed items.
fn folded_engine_blocks(items: &[verus_syn::Item]) -> Vec<TokenStream> {
    use quote::ToTokens;
    let mut blocks = Vec::new();
    for item in items {
        if let verus_syn::Item::Macro(m) = item {
            let last = m.mac.path.segments.last().map(|s| s.ident.to_string());
            if matches!(
                last.as_deref(),
                Some("verus_spec_check_unverified" | "verus_spec_check_verified")
            ) {
                blocks.push(m.mac.tokens.clone());
            }
        } else {
            // Folded blocks can also appear nested inside modules; the
            // current pass emits them at top level, so a miss here just
            // means the case exercises no engine block.
            let _ = item.to_token_stream();
        }
    }
    blocks
}

/// All cases run inside one #[test] in declaration order: the engine's
/// harness-module counter is process-global, so a fixed sequence keeps
/// ids stable (they're normalized too, but stability makes goldens
/// easier to read).
#[test]
fn expansion_snapshots() {
    let mut failures: Vec<String> = Vec::new();

    for case in CASES {
        let mut items = parse_items(case.src);
        verus_spec_check_engine::vcheck_provide_preprocess(&mut items);

        use quote::ToTokens;
        let mut folded = TokenStream::new();
        for item in &items {
            item.to_tokens(&mut folded);
        }
        let rendered = normalize(&pretty(&folded));
        if let Err(e) = check_snapshot(&format!("{}.preprocess", case.name), &rendered) {
            failures.push(e);
        }

        if case.expand {
            for (i, block) in folded_engine_blocks(&items).into_iter().enumerate() {
                let expanded = verus_spec_check_engine::expand_verus_spec_check(block, /*verified=*/ false);
                let rendered = normalize(&pretty(&expanded));
                let suffix = if i == 0 {
                    String::new()
                } else {
                    format!("_{i}")
                };
                if let Err(e) = check_snapshot(&format!("{}.expand{suffix}", case.name), &rendered)
                {
                    failures.push(e);
                }
            }
        }
    }

    for case in EXEC_SPEC_CASES {
        let ts: TokenStream = case.src.parse().expect("tokenize");
        let expanded = verus_spec_check_engine::expand_exec_spec(ts, /*unverified=*/ true);
        let rendered = normalize(&pretty(&expanded));
        if let Err(e) = check_snapshot(&format!("{}.exec_spec", case.name), &rendered) {
            failures.push(e);
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} snapshot(s) failed:\n\n{}",
            failures.len(),
            failures.join("\n\n")
        );
    }
}
