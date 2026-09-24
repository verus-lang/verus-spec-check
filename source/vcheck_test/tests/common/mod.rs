//! Shared infrastructure for the snippet-based end-to-end suite,
//! basically modeled on verus's `rust_verify_test` infrastructure
//!
//! Each test declares an inline code snippet and an expected outcome:
//!
//! ```ignore
//! test_vcheck_one_file! {
//!     #[test] checked_add vcheck_code! {
//!         verus_spec_check_unverified! {
//!             fn add(a: u8, b: u8) -> (r: u16)
//!                 ensures r == a as u16 + b as u16,
//!             { a as u16 + b as u16 }
//!         }
//!     } => HarnessOutcome::Pass { harnesses: 1 }
//! }
//! ```
//!
//! Mechanics: the snippet is materialized as a standalone crate under
//! `target/vcheck_test/cases/<case>/` using `scaffold/Cargo.toml.in`
//! (the examples/ template with absolutized paths), then driven with
//! `cargo test --lib` (harness tests) or `cargo verus focus` (verify
//! tests). All cases share one CARGO_TARGET_DIR per mode, so the heavy
//! dependencies (vstd, verus_syn, the overlay) compile exactly once per
//! mode; each case then only compiles its own tiny lib. Cargo's
//! target-dir lock serializes concurrent builds from parallel test
//! threads — correct, if not maximally parallel. If that ever becomes
//! the bottleneck, the escape hatch is verus's approach: extract
//! `--extern` flags once and invoke rustc directly per case.
//!
//! Conventions:
//! - Name `test_verify_one_file!` tests `verify_*`. Verify tests need
//!   `cargo-verus` + the pinned toolchain on PATH (`nix develop`);
//!   without it they panic with instructions. Harness tests run under
//!   plain cargo, so locally you can `cargo test -p verus_spec_check_test --
//!   --skip verify_`.
//! - `vcheck_code!` wraps the snippet in the standard example prelude and
//!   a `verus! {}` block. Use `vcheck_code_raw!` when the test needs to
//!   control the whole file (own imports, code outside `verus!`).
//! - Snippets go through `stringify!`, which collapses the snippet to
//!   one line; compile errors in a snippet therefore point at useless
//!   columns. If this hurts, the fix is a tiny proc macro that
//!   preserves source text via spans (what verus's
//!   `rust_verify_test_macros` does).

#![allow(dead_code)]

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

// ---------------------------------------------------------------------------
// Public macro surface
// ---------------------------------------------------------------------------

// Each test binary compiles its own copy of this module, so a binary
// that doesn't use every macro is normal.

/// Snippet wrapped in the standard prelude + `verus! {}` (the shape
/// every `examples/` lib.rs had).
#[allow(unused_macros)]
macro_rules! vcheck_code {
    ($($t:tt)*) => {
        crate::common::wrap_verus(stringify!($($t)*))
    };
}
#[allow(unused_imports)]
pub(crate) use vcheck_code;

/// Whole-file snippet: no prelude, no `verus! {}`. The test controls
/// everything.
#[allow(unused_macros)]
macro_rules! vcheck_code_raw {
    ($($t:tt)*) => {
        String::from(stringify!($($t)*))
    };
}
#[allow(unused_imports)]
pub(crate) use vcheck_code_raw;

/// Declare a test that materializes the snippet and runs the generated
/// vcheck harness via `cargo test --lib`.
#[allow(unused_macros)]
macro_rules! test_vcheck_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_harness_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
                crate::common::Scaffold::Default,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_vcheck_one_file;

/// Like [`test_vcheck_one_file!`] but materializes the case with the bolero
/// scaffold (`verus_spec_check` with the `bolero` feature, `[profile.fuzz]`,
/// `cfg(kani)` registered). For `#[vcheck(mode = "fuzz" | "kani")]` and the
/// legacy `backend = "bolero"` spelling.
#[allow(unused_macros)]
macro_rules! test_bolero_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_harness_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
                crate::common::Scaffold::Bolero,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_bolero_one_file;

/// Like [`test_vcheck_one_file!`] but materializes the case with the
/// covext scaffold (a local `covext_dep` crate as the
/// assume_specification subject) and ENABLES the external-coverage
/// side-profile orchestration. Skips (with an explanation) when the
/// llvm-tools component is absent.
#[allow(unused_macros)]
macro_rules! test_covext_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_covext_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_covext_one_file;

/// Like [`test_vcheck_one_file!`] but runs the KANI tier: materializes with
/// the bolero scaffold and model-checks the `mode = "kani"` harnesses via
/// `cargo kani --tests`. Skips (with an explanation) when cargo-kani is
/// not installed — see [`run_kani_case`].
#[allow(unused_macros)]
macro_rules! test_kani_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_kani_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_kani_one_file;

/// Like [`test_kani_one_file!`] but exercises the ONE-COMMAND path:
/// plain `cargo test` on the materialized case, with the emitted
/// `__vcheck_kani_report` orchestration enabled (`VERUS_SPEC_CHECK_KANI=1`), so
/// the report test itself spawns and gates on `cargo kani --tests`.
#[allow(unused_macros)]
macro_rules! test_kani_report_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_kani_report_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_kani_report_one_file;

/// Declare a test that materializes the snippet and runs
/// `cargo verus focus` on it. Name these tests `verify_*` so harness-only
/// runs can `--skip verify_`.
#[allow(unused_macros)]
macro_rules! test_verify_one_file {
    ($(#[$attr:meta])* $name:ident $code:expr => $outcome:expr) => {
        $(#[$attr])*
        fn $name() {
            crate::common::run_verify_case(
                concat!(env!("CARGO_CRATE_NAME"), "_", stringify!($name)),
                &$code,
                $outcome,
                crate::common::Scaffold::Default,
            );
        }
    };
}
#[allow(unused_imports)]
pub(crate) use test_verify_one_file;

// ---------------------------------------------------------------------------
// Scaffolds
// ---------------------------------------------------------------------------

/// Which manifest template a case is materialized from. Each scaffold
/// gets its OWN shared target dir: the dependency features differ, so
/// sharing one dir would make cases thrash each other's fingerprints and
/// rebuild vstd on every alternation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scaffold {
    /// The examples/ template: proptest backend.
    Default,
    /// `verus_spec_check` with the `bolero` feature + `[profile.fuzz]`.
    Bolero,
    /// The default template plus a local `covext_dep` crate — the
    /// external-coverage subject for `assume_specification` +
    /// `#[vcheck_cov_fuzz]` side-profile cases.
    CovExt,
}

impl Scaffold {
    fn template(self) -> &'static str {
        match self {
            Scaffold::Default => "Cargo.toml.in",
            Scaffold::Bolero => "Cargo.bolero.toml.in",
            Scaffold::CovExt => "Cargo.covext.toml.in",
        }
    }

    /// Shared target dir suffix, per scaffold *and* per mode (harness vs.
    /// verify), since `cargo verus` passes different flags.
    fn shared_dir(self, mode: &str) -> String {
        match self {
            Scaffold::Default => format!("shared-{mode}"),
            Scaffold::Bolero => format!("shared-bolero-{mode}"),
            Scaffold::CovExt => format!("shared-covext-{mode}"),
        }
    }
}

/// Source of the materialized `covext_dep` crate: deliberately branchy
/// so the side profile has arms to count, and coarse enough (a 50/50
/// split on `u8`) that the wrapper harness's default 256 samples reach
/// every arm with probability ~1 — keeping the `threshold = 100`
/// assertion deterministic in practice.
const COVEXT_DEP_LIB: &str = r#"
/// Stand-in for "code we do not control".
pub fn classify(x: u8) -> u8 {
    if x < 128 {
        1
    } else {
        2
    }
}

/// MATCH-based (no `if` anywhere): rustc's branch instrumentation emits
/// NO llvm branch records for this shape, so a 100% branch threshold on
/// it can only be satisfied through MIR-arm witnessing (each arm's body
/// is its own counted region; the covdriver manifest anchors them).
/// Four uniform 64-wide buckets keep every arm reachable with
/// certainty at the default sample counts.
pub fn grade(x: u8) -> u8 {
    match x / 64 {
        0 => 10,
        1 => 20,
        2 => 30,
        _ => 40,
    }
}
"#;

const COVEXT_DEP_MANIFEST: &str = r#"[package]
name = "covext_dep"
version = "0.1.0"
edition = "2021"
"#;

// ---------------------------------------------------------------------------
// Expected outcomes
// ---------------------------------------------------------------------------

/// Expected outcome of a `cargo test --lib` run on a snippet crate.
#[derive(Debug, Clone, Copy)]
pub enum HarnessOutcome {
    /// The crate builds, every test passes, and exactly `harnesses`
    /// property harnesses ran. The count assertion is the per-test
    /// version of run_examples.sh's "0 tests ran" check: it catches
    /// `#[vcheck]`/`verus_spec_check_*!` silently generating nothing (e.g. the
    /// contrib-hooks feature wiring regressing).
    ///
    /// Counts contract harnesses (`vcheck_<fn>`) and inline-assert
    /// harnesses (`__vcheck_assert*`); see [`harness_results`] for what is
    /// excluded.
    Pass { harnesses: usize },
    /// Like [`HarnessOutcome::Pass`], and additionally asserts the
    /// `#[vcheck_cov_mutate]` reporter test ran. Use for cov_mutate cases,
    /// where the report is the feature under test — without this the
    /// mutator could silently stop emitting it and the case would still
    /// pass on harness count alone.
    PassWithMutationReport { harnesses: usize },
    /// Like [`HarnessOutcome::Pass`], and additionally asserts the
    /// `#[vcheck_cov_fuzz]` reporter test ran. Same rationale as
    /// [`HarnessOutcome::PassWithMutationReport`], for the branch-
    /// coverage report.
    PassWithCovFuzzReport { harnesses: usize },
    /// Like [`HarnessOutcome::PassWithCovFuzzReport`], and additionally
    /// requires every `needle` to appear in the uncaptured report output.
    /// This pins report semantics for advisory findings rather than merely
    /// checking that a reporter test was emitted.
    PassWithCovFuzzReportContaining {
        harnesses: usize,
        needles: &'static [&'static str],
    },
    /// Like [`HarnessOutcome::Pass`], and additionally asserts the
    /// `mode = "kani"` proof reporter test ran (and passed — a report
    /// failure fails the whole case via the `failed` tally). Used by
    /// the kani-report cases, which opt back into the orchestration
    /// the case-runner defaults disable.
    PassWithKaniReport { harnesses: usize },
    /// The crate BUILDS but at least one generated harness test FAILS.
    /// This is the soundness-fixture outcome (higher_order_unsound
    /// style): the spec is known-unsound and the detector must flag it.
    /// A passing run means detector regression; a build error means the
    /// fixture rotted. Both are reported as test failures.
    FailsHarness,
    /// Like [`HarnessOutcome::FailsHarness`], and additionally asserts
    /// the combined test output contains `needle`. Use to pin the SHAPE
    /// of a failure — e.g. the `mode = "fuzz"` guided loop's
    /// counterexample report or its vacuity diagnostic — not just that
    /// something failed.
    FailsHarnessWith { needle: &'static str },
    /// The crate must fail during compilation and emit `needle`.
    /// Used for fail-closed macro/attribute diagnostics where silently
    /// accepting malformed configuration would weaken a requested gate.
    FailsBuildWith { needle: &'static str },
}

/// Expected outcome of a `cargo kani --tests` run on a snippet crate.
#[derive(Debug, Clone, Copy)]
pub enum KaniOutcome {
    /// Every `#[kani::proof]` harness verifies (`VERIFICATION:- SUCCESSFUL`).
    Proves,
    /// At least one harness is refuted (`VERIFICATION:- FAILED`, non-zero
    /// exit). For pinning that Kani actually CATCHES a broken contract —
    /// without this, `Proves` cases can't distinguish "verified" from
    /// "vacuously analyzed nothing".
    Refutes,
}

/// Expected outcome of a `cargo verus focus` run on a snippet crate.
#[derive(Debug, Clone, Copy)]
pub enum VerifyOutcome {
    /// Verifies clean (exit 0; the cached "nothing to do" case counts).
    Verifies,
    /// Fails verification (non-zero exit that is NOT a missing
    /// cargo-verus). For pinning known-unverifiable shapes.
    VerifyErr,
}

// ---------------------------------------------------------------------------
// Runners
// ---------------------------------------------------------------------------

pub fn run_harness_case(case: &str, code: &str, outcome: HarnessOutcome, scaffold: Scaffold) {
    let dir = materialize(case, code, scaffold);
    let args: &[&str] = if matches!(
        outcome,
        HarnessOutcome::PassWithCovFuzzReportContaining { .. }
    ) {
        &["test", "--lib", "--", "--nocapture"]
    } else {
        &["test", "--lib"]
    };
    let out = run_cargo(&dir, args, &scaffold.shared_dir("harness"));
    assert_harness_outcome(case, &dir, &out, outcome);
}

/// Harness case with external-coverage orchestration ENABLED (the
/// defaults disable it; see `run_cargo_inner`). Probes for the
/// llvm-tools component first and SKIPS (with an explanation) when it
/// is absent, mirroring the verify-tier toolchain probe — the
/// orchestrator's own graceful degradation would otherwise turn a
/// missing host component into a threshold failure.
pub fn run_covext_case(case: &str, code: &str, outcome: HarnessOutcome) {
    if let Err(why) = llvm_tools_status() {
        eprintln!(
            "{case}: SKIPPED — {why}. External-coverage cases need the \
             llvm-tools rustup component (`rustup component add llvm-tools`)."
        );
        return;
    }
    // The dependency tier's TRUE branch evidence needs nightly branch
    // instrumentation; without a nightly toolchain the orchestrator
    // degrades to a stable region proxy, which cannot satisfy the
    // `threshold = 100` these cases gate on — outcomes would invert for
    // toolchain reasons, not feature reasons. Same probing rationale as
    // the llvm-tools skip above.
    if let Err(why) = nightly_toolchain_status() {
        eprintln!(
            "{case}: SKIPPED — {why}. External-coverage cases need a nightly \
             toolchain (`rustup toolchain install nightly`)."
        );
        return;
    }
    let scaffold = Scaffold::CovExt;
    let dir = materialize(case, code, scaffold);
    let out = run_cargo_env(
        &dir,
        &["test", "--lib"],
        &scaffold.shared_dir("harness"),
        &[("VERUS_SPEC_CHECK_COV_FUZZ_EXT", "1")],
    );
    assert_harness_outcome(case, &dir, &out, outcome);
}

/// Campaign-mode case (`VERUS_SPEC_CHECK_COV_CAMPAIGN=1`). The fixture must
/// hold MULTIPLE macro expansions, each with a `#[vcheck_cov_fuzz]` target
/// whose threshold fails. Asserts the whole-binary audit semantics:
/// exactly ONE report test performs the aggregated audit (and fails
/// with every expansion's violations in one message, proving the
/// link-time registry collected all of them), while every other report
/// test no-ops and passes.
pub fn run_campaign_case(case: &str, code: &str, violation_needles: &[&str]) {
    let scaffold = Scaffold::Default;
    let dir = materialize(case, code, scaffold);
    let out = run_cargo_env(
        &dir,
        &["test", "--lib"],
        &scaffold.shared_dir("harness"),
        &[("VERUS_SPEC_CHECK_COV_CAMPAIGN", "1")],
    );
    let combined = combined_output(&out);
    assert!(
        !is_build_error(&combined),
        "{case}: fixture failed to BUILD:\n{}",
        tail(&combined, 60),
    );
    assert!(
        !out.status.success(),
        "{case}: campaign case must fail its thresholds\n{}",
        tail(&combined, 60),
    );
    let report_line = |l: &&str| l.starts_with("test ") && l.contains("__vcheck_cov_fuzz_report");
    let report_ok = combined
        .lines()
        .filter(report_line)
        .filter(|l| l.trim_end().ends_with("ok"))
        .count();
    let report_failed = combined
        .lines()
        .filter(report_line)
        .filter(|l| l.trim_end().ends_with("FAILED"))
        .count();
    assert_eq!(
        report_failed,
        1,
        "{case}: exactly one elected report test must run (and fail) the \
         aggregated campaign; got {report_failed} failing report tests\n{}",
        tail(&combined, 60),
    );
    assert!(
        report_ok >= 1,
        "{case}: the non-elected report test(s) must no-op and pass\n{}",
        tail(&combined, 60),
    );
    for needle in violation_needles {
        assert!(
            combined.contains(needle),
            "{case}: aggregated campaign violation message must include \
             `{needle}` (all expansions' targets in ONE report)\n{}",
            tail(&combined, 80),
        );
    }
    // The campaign report spans several modules, so the per-module
    // disposition rollup must be present.
    assert!(
        combined.contains("per-module summary:"),
        "{case}: campaign report must include the per-module summary table\n{}",
        tail(&combined, 80),
    );
}

/// Like [`run_covext_case`] but with the MIR branch-manifest pass
/// ENABLED (arm witnessing). Additionally requires nightly + rust-src +
/// rustc-dev (covdriver builds against rustc_private); skips with an
/// explanation when absent so case outcomes stay machine-independent.
pub fn run_covext_mir_case(case: &str, code: &str, outcome: HarnessOutcome) {
    if let Err(why) = llvm_tools_status() {
        eprintln!("{case}: SKIPPED — {why}.");
        return;
    }
    if let Err(why) = covdriver_toolchain_status() {
        eprintln!(
            "{case}: SKIPPED — {why}. Arm-witnessing cases need \
             `rustup component add rustc-dev rust-src --toolchain nightly`."
        );
        return;
    }
    let scaffold = Scaffold::CovExt;
    let dir = materialize(case, code, scaffold);
    let out = run_cargo_env(
        &dir,
        &["test", "--lib"],
        &scaffold.shared_dir("harness"),
        &[
            ("VERUS_SPEC_CHECK_COV_FUZZ_EXT", "1"),
            ("VERUS_SPEC_CHECK_COVEXT_MIR", "1"),
        ],
    );
    assert_harness_outcome(case, &dir, &out, outcome);
}

/// Whether a nightly toolchain is reachable via rustup at all (the
/// dependency tier's branch instrumentation needs it).
fn nightly_toolchain_status() -> Result<(), String> {
    let ok = Command::new("rustup")
        .args(["run", "nightly", "rustc", "--print", "sysroot"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if ok {
        Ok(())
    } else {
        Err("no nightly toolchain reachable via rustup".to_string())
    }
}

/// Whether the nightly toolchain can build covdriver (rustc-dev) and
/// run its analysis pass (rust-src).
fn covdriver_toolchain_status() -> Result<(), String> {
    let out = Command::new("rustup")
        .args(["component", "list", "--toolchain", "nightly", "--installed"])
        .output()
        .map_err(|e| format!("spawn rustup: {e}"))?;
    if !out.status.success() {
        return Err("no nightly toolchain reachable via rustup".to_string());
    }
    let installed = String::from_utf8_lossy(&out.stdout);
    for needed in ["rustc-dev", "rust-src"] {
        if !installed.lines().any(|l| l.starts_with(needed)) {
            return Err(format!("nightly `{needed}` component not installed"));
        }
    }
    Ok(())
}

/// Whether llvm-profdata/llvm-cov are available in the active
/// toolchain's sysroot (the llvm-tools rustup component).
fn llvm_tools_status() -> Result<(), String> {
    let out = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .map_err(|e| format!("spawn rustc: {e}"))?;
    if !out.status.success() {
        return Err("rustc --print sysroot failed".to_string());
    }
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let host = Command::new("rustc")
        .args(["-vV"])
        .output()
        .ok()
        .and_then(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .find_map(|l| l.strip_prefix("host: ").map(|s| s.trim().to_string()))
        })
        .ok_or_else(|| "could not determine host triple".to_string())?;
    let bin = std::path::Path::new(&sysroot)
        .join("lib/rustlib")
        .join(host)
        .join("bin");
    if bin.join("llvm-profdata").exists() && bin.join("llvm-cov").exists() {
        return Ok(());
    }
    // PATH fallback, mirroring the runtime's `cov_fuzz_ext::llvm_tools`:
    // non-rustup toolchains (nixpkgs rustc) provide the tools via an
    // LLVM package on PATH instead of the sysroot.
    let on_path = |name: &str| {
        std::env::var_os("PATH")
            .map(|p| std::env::split_paths(&p).any(|d| d.join(name).is_file()))
            .unwrap_or(false)
    };
    if on_path("llvm-profdata") && on_path("llvm-cov") {
        Ok(())
    } else {
        Err("llvm-tools not installed in the active toolchain (and not on PATH)".to_string())
    }
}

fn assert_harness_outcome(case: &str, dir: &PathBuf, out: &Output, outcome: HarnessOutcome) {
    let combined = combined_output(out);
    let t = harness_results(out);
    let (ok, failed) = (t.ok, t.failed);

    match outcome {
        HarnessOutcome::Pass { harnesses }
        | HarnessOutcome::PassWithMutationReport { harnesses }
        | HarnessOutcome::PassWithCovFuzzReport { harnesses }
        | HarnessOutcome::PassWithCovFuzzReportContaining { harnesses, .. }
        | HarnessOutcome::PassWithKaniReport { harnesses } => {
            assert!(
                out.status.success(),
                "{case}: expected all tests to pass (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            assert_eq!(
                ok,
                harnesses,
                "{case}: expected {harnesses} generated harness test(s), saw {ok} \
                 — if 0, harness generation silently produced nothing \
                 (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            if matches!(outcome, HarnessOutcome::PassWithMutationReport { .. }) {
                assert!(
                    t.mutation_report,
                    "{case}: expected a #[vcheck_cov_mutate] mutation report test, \
                     none ran (crate at {}):\n{}",
                    dir.display(),
                    tail(&combined, 60),
                );
            }
            if matches!(
                outcome,
                HarnessOutcome::PassWithCovFuzzReport { .. }
                    | HarnessOutcome::PassWithCovFuzzReportContaining { .. }
            ) {
                assert!(
                    t.cov_fuzz_report,
                    "{case}: expected a #[vcheck_cov_fuzz] branch coverage report test, \
                     none ran (crate at {}):\n{}",
                    dir.display(),
                    tail(&combined, 60),
                );
            }
            if let HarnessOutcome::PassWithCovFuzzReportContaining { needles, .. } = outcome {
                for needle in needles {
                    assert!(
                        combined.contains(needle),
                        "{case}: passing coverage report lacks {needle:?} \
                         (crate at {}):\n{}",
                        dir.display(),
                        tail(&combined, 80),
                    );
                }
            }
            if matches!(outcome, HarnessOutcome::PassWithKaniReport { .. }) {
                assert!(
                    t.kani_report,
                    "{case}: expected a mode=\"kani\" proof report test, none ran \
                     (crate at {}):\n{}",
                    dir.display(),
                    tail(&combined, 60),
                );
            }
        }
        HarnessOutcome::FailsHarness | HarnessOutcome::FailsHarnessWith { .. } => {
            assert!(
                !is_build_error(&combined),
                "{case}: soundness fixture must BUILD and fail at test time, \
                 got a build error (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            assert!(
                !out.status.success() && failed > 0,
                "{case}: unsound-spec fixture PASSED ({ok} ok, {failed} failed) — \
                 detector regression (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            if let HarnessOutcome::FailsHarnessWith { needle } = outcome {
                assert!(
                    combined.contains(needle),
                    "{case}: harness failed as expected, but the output lacks \
                     {needle:?} (crate at {}):\n{}",
                    dir.display(),
                    tail(&combined, 60),
                );
            }
        }
        HarnessOutcome::FailsBuildWith { needle } => {
            assert!(
                !out.status.success() && is_build_error(&combined),
                "{case}: expected compilation to fail (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            assert!(
                combined.contains(needle),
                "{case}: compilation failed, but the output lacks {needle:?} \
                 (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
        }
    }
}

/// Kani tier: materialize the snippet with the bolero scaffold and run
/// `cargo kani --tests` — model-checking every `#[kani::proof]` harness
/// the `mode = "kani"` fns expanded to. SKIPS (with an explanation)
/// when cargo-kani isn't installed, mirroring the verify tier's
/// toolchain probe: CI runners and most dev machines don't carry Kani,
/// and a missing tool must read as "not run here", not as a failure.
///
/// The kani tier exists because it exercises a lowering no other tier
/// does: `requires` -> `kani::assume` and the `cfg(kani)`-selected i128
/// spec-int model (`spec_int_kani.rs`). Regressions there — like the
/// BigInt digit loops that made every kani harness spin CBMC's
/// unwinder forever — are invisible to the proptest/fuzz tiers.
pub fn run_kani_case(case: &str, code: &str, outcome: KaniOutcome) {
    if let Err(why) = kani_toolchain_status() {
        eprintln!(
            "{case}: SKIPPED — {why}. Kani cases need cargo-kani \
             (`cargo install --locked kani-verifier && cargo kani setup`)."
        );
        return;
    }
    let scaffold = Scaffold::Bolero;
    let dir = materialize(case, code, scaffold);
    // Kani drives its own codegen through CARGO_TARGET_DIR like any
    // cargo subcommand; a dedicated shared dir keeps its artifacts from
    // thrashing the harness tier's cache (different codegen backend).
    let out = run_cargo(&dir, &["kani", "--tests"], &scaffold.shared_dir("kani"));
    let combined = combined_output(&out);

    match outcome {
        KaniOutcome::Proves => {
            assert!(
                out.status.success() && combined.contains("VERIFICATION:- SUCCESSFUL"),
                "{case}: expected every kani harness to verify (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
        }
        KaniOutcome::Refutes => {
            assert!(
                !is_build_error(&combined),
                "{case}: refutation fixture must BUILD and fail at verification \
                 time, got a build error (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
            assert!(
                !out.status.success() && combined.contains("VERIFICATION:- FAILED"),
                "{case}: broken-contract fixture VERIFIED — kani-tier detector \
                 regression (crate at {}):\n{}",
                dir.display(),
                tail(&combined, 60),
            );
        }
    }
}

/// Kani-REPORT tier: run the snippet's harnesses under plain
/// `cargo test --lib` with the `mode = "kani"` proof orchestration
/// ENABLED (the case-runner defaults disable it via `VERUS_SPEC_CHECK_KANI=0`).
/// This is the "one interface" path end to end: the emitted
/// `__vcheck_kani_report` test spawns `cargo kani --tests` itself and the
/// case asserts on the report's outcome. SKIPS when cargo-kani is
/// absent, like [`run_kani_case`] — the orchestration's own loud
/// missing-kani failure is covered by a unit-level knob, not by
/// requiring every dev machine to have kani.
pub fn run_kani_report_case(case: &str, code: &str, outcome: HarnessOutcome) {
    if let Err(why) = kani_toolchain_status() {
        eprintln!(
            "{case}: SKIPPED — {why}. Kani cases need cargo-kani \
             (`cargo install --locked kani-verifier && cargo kani setup`)."
        );
        return;
    }
    let scaffold = Scaffold::Bolero;
    let dir = materialize(case, code, scaffold);
    let out = run_cargo_env(
        &dir,
        &["test", "--lib"],
        &scaffold.shared_dir("harness"),
        &[
            ("VERUS_SPEC_CHECK_KANI", "1"),
            // The report's /dev/tty printing would bypass this suite's
            // capture; stderr instead (same as the other reporters).
            ("VERUS_SPEC_CHECK_KANI_QUIET", "1"),
        ],
    );
    assert_harness_outcome(case, &dir, &out, outcome);
}

/// Whether a usable cargo-kani is installed, as `Ok(())` or a
/// human-readable reason it isn't. `cargo kani --version` exercises
/// both the cargo subcommand lookup and the kani-verifier install.
fn kani_toolchain_status() -> Result<(), String> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let ok = Command::new(cargo)
        .args(["kani", "--version"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if ok {
        Ok(())
    } else {
        Err("no working `cargo kani` on PATH".to_string())
    }
}

pub fn run_verify_case(case: &str, code: &str, outcome: VerifyOutcome, scaffold: Scaffold) {
    let dir = materialize(case, code, scaffold);
    // Probe BEFORE spawning. Checking for a working `verus` up front is
    // more reliable than pattern-matching the failure text afterwards: a
    // host can have `cargo-verus` on PATH while the `verus` binary it
    // execs is missing (e.g. a stale /usr/local/bin install), in which
    // case `cargo verus focus` fails deep inside with "could not execute
    // process ... (never executed)" rather than any recognizable
    // "no such subcommand" message.
    if let Err(why) = verus_toolchain_status() {
        panic!(
            "{case}: {why}\n\
             Verify tests need the pinned Verus toolchain. Either run them \
             inside the dev shell:\n\
             \x20   nix develop --command cargo test -p verus_spec_check_test\n\
             or skip them:\n\
             \x20   cargo test -p verus_spec_check_test -- --skip verify_"
        );
    }

    let out = run_cargo(&dir, &["verus", "focus"], &scaffold.shared_dir("verify"));
    let combined = combined_output(&out);

    match outcome {
        VerifyOutcome::Verifies => assert!(
            out.status.success(),
            "{case}: expected clean verification (crate at {}):\n{}",
            dir.display(),
            tail(&combined, 60),
        ),
        VerifyOutcome::VerifyErr => assert!(
            !out.status.success(),
            "{case}: expected a verification error but it verified clean \
             (crate at {}):\n{}",
            dir.display(),
            tail(&combined, 60),
        ),
    }
}

// ---------------------------------------------------------------------------
// Snippet wrapping
// ---------------------------------------------------------------------------

pub fn wrap_verus(snippet: &str) -> String {
    format!(
        "#![allow(unused_imports)]\n\
         use vstd::prelude::*;\n\
         use verus_spec_check::*;\n\
         use verus_spec_check_vstd_ext::*;\n\
         \n\
         verus! {{\n\
         \n\
         {snippet}\n\
         \n\
         }} // verus!\n"
    )
}

// ---------------------------------------------------------------------------
// Crate materialization
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
    // source/vcheck_test -> repo root
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

/// The vstd / verus_builtin_macros pin, read from source/vstd_ext's
/// manifest so tools/release/sync-verus.sh stays the single place that
/// bumps versions.
fn version_pin() -> String {
    let manifest = repo_root().join("source/vstd_ext/Cargo.toml");
    let text = fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("read {}: {e}", manifest.display()));
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("vstd = \"=") {
            if let Some(v) = rest.split('"').next() {
                return v.to_string();
            }
        }
    }
    panic!("no `vstd = \"=...\"` pin found in {}", manifest.display());
}

/// Write the snippet crate under target/vcheck_test/cases/<case>/ and
/// return its path. Rewritten on every run; stale dirs are debuggable
/// leftovers and vanish with `cargo clean`.
fn materialize(case: &str, code: &str, scaffold: Scaffold) -> PathBuf {
    let root = repo_root();
    let dir = root.join("target/vcheck_test/cases").join(case);
    fs::create_dir_all(dir.join("src")).expect("create case dir");

    let template = root
        .join("source/vcheck_test/scaffold")
        .join(scaffold.template());
    let manifest = fs::read_to_string(&template)
        .unwrap_or_else(|e| panic!("read {}: {e}", template.display()))
        .replace("@NAME@", case)
        .replace("@ROOT@", root.to_str().expect("utf-8 repo root path"))
        .replace("@PIN@", &version_pin());

    fs::write(dir.join("Cargo.toml"), manifest).expect("write Cargo.toml");
    fs::write(dir.join("src/lib.rs"), code).expect("write src/lib.rs");

    // CovExt cases additionally materialize the local dependency crate
    // the snippet's assume_specification targets.
    if scaffold == Scaffold::CovExt {
        let dep = dir.join("covext_dep");
        fs::create_dir_all(dep.join("src")).expect("create covext_dep dir");
        fs::write(dep.join("Cargo.toml"), COVEXT_DEP_MANIFEST)
            .expect("write covext_dep Cargo.toml");
        fs::write(dep.join("src/lib.rs"), COVEXT_DEP_LIB).expect("write covext_dep lib.rs");
    }
    dir
}

// ---------------------------------------------------------------------------
// Process plumbing + output parsing
// ---------------------------------------------------------------------------

fn run_cargo(dir: &PathBuf, args: &[&str], shared: &str) -> Output {
    run_cargo_env(dir, args, shared, &[])
}

/// Like [`run_cargo`] but with case-specific env overrides applied
/// AFTER the defaults (so a case can re-enable something the defaults
/// disable, e.g. external-coverage orchestration).
fn run_cargo_env(dir: &PathBuf, args: &[&str], shared: &str, extra_env: &[(&str, &str)]) -> Output {
    // One shared CARGO_TARGET_DIR per (scaffold, mode) so the heavy deps
    // build once. Cargo's target-dir lock serializes concurrent builds
    // from parallel test threads.
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let target_dir = repo_root().join("target/vcheck_test").join(shared);
    Command::new(cargo)
        .args(args)
        .current_dir(dir)
        .env("CARGO_TARGET_DIR", &target_dir)
        // The `#[vcheck_cov_mutate]` reporter writes to /dev/tty by default
        // so a developer sees it inline without `--nocapture`. That also
        // bypasses the pipe below, so reports from every cov_mutate case
        // would blast into THIS suite's output. Ask for stderr instead,
        // which the pipe captures — the report still shows up in the
        // failure diagnostics when a case fails.
        .env("VERUS_SPEC_CHECK_COV_MUTATE_QUIET", "1")
        // Same for the `#[vcheck_cov_fuzz]` branch-coverage reporter.
        .env("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1")
        // External-target side-profile orchestration is DISABLED for
        // ordinary cases: it spawns instrumented cargo builds and its
        // availability depends on host toolchain components, which
        // would make case outcomes machine-dependent. The dedicated
        // covext case (run_covext_case) opts back in explicitly.
        .env("VERUS_SPEC_CHECK_COV_FUZZ_EXT", "0")
        // The MIR branch-manifest pass spawns `cargo check -Z build-std`
        // (plus a covdriver build needing nightly rustc-dev) — disabled
        // by default for the same machine-dependence reason. Plain
        // covext cases measure through llvm branch records exactly as
        // before; the dedicated arm-witnessing cases
        // (run_covext_mir_case) opt back in explicitly.
        .env("VERUS_SPEC_CHECK_COVEXT_MIR", "0")
        // Same rationale for the `mode = "kani"` proof orchestration:
        // the emitted `__vcheck_kani_report` would spawn `cargo kani
        // --tests` (and fail loudly where kani isn't installed), so
        // ordinary cases disable the tier. The dedicated kani-report
        // cases (run_kani_report_case) opt back in explicitly.
        .env("VERUS_SPEC_CHECK_KANI", "0")
        .envs(
            extra_env
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string())),
        )
        .output()
        .expect("spawn cargo")
}

fn combined_output(out: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// Tally of generated tests in one libtest run.
#[derive(Debug, Default, Clone, Copy)]
pub struct Tally {
    /// Property harnesses that passed.
    pub ok: usize,
    /// Property harnesses that failed.
    pub failed: usize,
    /// Whether the `#[vcheck_cov_mutate]` reporter test ran.
    pub mutation_report: bool,
    /// Whether the `#[vcheck_cov_fuzz]` reporter test ran.
    pub cov_fuzz_report: bool,
    /// Whether the `mode = "kani"` proof reporter test ran.
    pub kani_report: bool,
}

/// Parse libtest output for generated tests. Lines look like
/// `test __verus_spec_check_0::vcheck_append_vec ... ok`.
///
/// Everything the engine emits lives under a `__verus_spec_check_<n>` module:
///   - `vcheck_<fn>`            — a contract harness  (counted)
///   - `__vcheck_assert*`       — an inline-assert harness (counted)
///   - `__vcheck_mutation_report` — the cov_mutate REPORTER, not a
///     property test: it prints kill rates and passes regardless. Kept
///     out of the harness count so `harnesses: n` means the same thing
///     whether or not a case uses `#[vcheck_cov_mutate]`; asserted
///     separately via `PassWithMutationReport`.
///   - `__vcheck_cov_fuzz_report` — the cov_fuzz REPORTER; same treatment,
///     asserted separately via `PassWithCovFuzzReport`.
fn harness_results(out: &Output) -> Tally {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut t = Tally::default();
    for line in stdout.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("test __verus_spec_check") else {
            continue;
        };
        let leaf = rest.rsplit("::").next().unwrap_or("");
        // Reporter tests are kept out of the `ok` harness count (so
        // `harnesses: n` means the same thing with or without a
        // reporter), but a FAILED reporter — e.g. a violated
        // `threshold = N` — is a real failure and counts as one.
        if leaf.starts_with("__vcheck_mutation_report") {
            t.mutation_report = true;
            if line.ends_with("... FAILED") {
                t.failed += 1;
            }
            continue;
        }
        if leaf.starts_with("__vcheck_cov_fuzz_report") {
            t.cov_fuzz_report = true;
            if line.ends_with("... FAILED") {
                t.failed += 1;
            }
            continue;
        }
        // `__vcheck_covext_replay_*` — external-coverage replay machinery
        // (a no-op outside the instrumented side-profile run), not a
        // contract harness; excluded from the harness count like the
        // reporters. A FAILED replay is still a real failure.
        if leaf.starts_with("__vcheck_covext_replay_") {
            if line.ends_with("... FAILED") {
                t.failed += 1;
            }
            continue;
        }
        if leaf.starts_with("__vcheck_kani_report") {
            t.kani_report = true;
            if line.ends_with("... FAILED") {
                t.failed += 1;
            }
            continue;
        }
        if line.ends_with("... ok") {
            t.ok += 1;
        } else if line.ends_with("... FAILED") {
            t.failed += 1;
        }
    }
    t
}

/// Same build-error detection run_examples.sh used: `error:` alone is
/// unusable ("error: test failed" appears on ordinary test failures).
fn is_build_error(combined: &str) -> bool {
    combined.contains("could not compile") || combined.lines().any(|l| l.starts_with("error["))
}

/// Whether a usable Verus toolchain is on PATH, as `Ok(())` or a
/// human-readable reason it isn't.
///
/// Checks BOTH halves, because they can be present independently:
///   - the `verus` binary itself, which does the verification;
///   - the `cargo-verus` cargo subcommand, which drives it.
///
/// A stale partial install (e.g. `/usr/local/bin/cargo-verus` present but
/// its sibling `verus` missing) satisfies neither `cargo verus --help`
/// nor a plain PATH lookup for `cargo-verus`, so probing `verus` first is
/// what actually distinguishes "no Verus here" from "verification
/// failed".
fn verus_toolchain_status() -> Result<(), String> {
    let verus_ok = Command::new("verus")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !verus_ok {
        return Err("no working `verus` binary on PATH.".to_string());
    }

    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let subcmd_ok = Command::new(cargo)
        .args(["verus", "--help"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !subcmd_ok {
        return Err(
            "`verus` is on PATH but the `cargo verus` subcommand is not \
                    available."
                .to_string(),
        );
    }

    Ok(())
}

fn tail(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}
