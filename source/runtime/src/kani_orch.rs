//! Kani proof orchestration for `#[vcheck(mode = "kani")]` — makes plain
//! `cargo test` drive `cargo kani --tests` so the kani tier lives under
//! the same one-command interface as every other mode.
//!
//! ## Architecture
//!
//! Kani cannot run in-process: it is a separate compilation pipeline
//! (the whole crate graph is recompiled through kani's codegen into
//! CBMC's input language), so a normally-compiled test binary has no
//! model of itself to check. Instead, when an expansion block contains
//! kani-mode targets the macro emits ONE aggregating test,
//! `__vcheck_kani_report`, which calls [`run_kani_report`]:
//!
//!  1. probe `cargo kani --version` (fail LOUDLY with setup
//!     instructions when missing — you wrote `mode = "kani"`, so a
//!     machine that can't prove it must go red, not silently green);
//!  2. spawn `cargo kani --tests` once, in a dedicated scratch
//!     `CARGO_TARGET_DIR` (kani's codegen must not thrash the primary
//!     build cache);
//!  3. parse per-harness `VERIFICATION:- SUCCESSFUL / FAILED` blocks;
//!  4. print a report and panic if any expected harness was refuted —
//!     or never appeared (an expected proof that didn't run must not
//!     pass vacuously).
//!
//! The report test is emitted under
//! `cfg(not(any(fuzzing_*, kani)))`, which yields two structural
//! guarantees: the kani side build (compiled with `--cfg kani`)
//! cannot contain the test that spawns kani, so re-entrancy is
//! impossible by construction; and cargo-bolero's target discovery
//! (which executes tests) never trips a minutes-long proof run.
//!
//! Multiple `verus!` blocks each emit their own report test, but all
//! run in one test process: a process-global [`OnceLock`] runs the
//! side build once and every report test checks its own harness
//! subset against the cached results.
//!
//! ## Environment knobs
//!
//! - `VERUS_SPEC_CHECK_KANI=0` — explicit opt-out: the report prints a
//!   "disabled" note and passes. Distinct from missing-kani, which
//!   fails.
//! - `VERUS_SPEC_CHECK_KANI_TIMEOUT` — wall-clock seconds for the whole
//!   `cargo kani --tests` run (default: none). On expiry the child is
//!   killed and the report fails with the partial output.
//! - `VERUS_SPEC_CHECK_KANI_INSTALL=1` — on a missing-kani probe, run
//!   `cargo install --locked kani-verifier` + `cargo kani setup`
//!   before failing. Opt-in only: a test that silently downloads a
//!   toolchain is not an acceptable default.
//! - `VERUS_SPEC_CHECK_KANI_QUIET=1` — report to stderr (obeying cargo's
//!   capture) instead of `/dev/tty`.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// Outcome of one kani harness, parsed from the side run.
#[derive(Clone, Debug)]
pub struct HarnessResult {
    /// Full harness path as kani printed it (e.g.
    /// `__verus_spec_check_0::vcheck_safe_add`).
    pub path: String,
    /// `true` = `VERIFICATION:- SUCCESSFUL`.
    pub verified: bool,
    /// `Verification Time: ...` line, when present (display only).
    pub time: Option<String>,
}

/// Cached result of the once-per-process side run: harness results
/// keyed by full path, or the human-readable reason the run couldn't
/// happen. `None` in the Ok position of the outer map is never used;
/// the Err string is reported (and panicked) by every report test.
static SIDE_RUN: OnceLock<Result<BTreeMap<String, HarnessResult>, String>> = OnceLock::new();

/// Entry point invoked by the macro-emitted `__vcheck_kani_report` test.
/// `expected` holds the bare harness fn names of THIS expansion
/// block's kani-mode targets (`vcheck_<fn>` / `vcheck_<Self>_<fn>`); kani
/// reports full module paths, so matching is on the `::<name>` suffix.
///
/// Panics (failing the test) when kani is unavailable, the side run
/// breaks, any expected harness is refuted, or any expected harness
/// never appeared in kani's output.
pub fn run_kani_report(crate_dir: &str, expected: &[&str]) {
    if expected.is_empty() {
        return;
    }
    // Explicit opt-out: pass with a note. This is the ONLY silent-ish
    // path, and it requires the user to have set the knob themselves.
    if std::env::var("VERUS_SPEC_CHECK_KANI").as_deref() == Ok("0") {
        eprintln!(
            "verus_spec_check: kani tier disabled (VERUS_SPEC_CHECK_KANI=0) — {} `mode = \"kani\"` \
             harness(es) NOT proven in this run",
            expected.len()
        );
        return;
    }

    let results = SIDE_RUN
        .get_or_init(|| side_run(crate_dir))
        .as_ref()
        .unwrap_or_else(|why| panic!("verus_spec_check: kani tier failed: {why}"));

    // Match each expected bare name against the full paths.
    let mut report = String::new();
    report.push_str("kani proof report (mode = \"kani\")\n");
    report.push_str("──────────────────────────────────\n");
    let mut refuted: Vec<&str> = Vec::new();
    let mut missing: Vec<&str> = Vec::new();
    for name in expected {
        let matches: Vec<&HarnessResult> = results
            .values()
            .filter(|r| r.path == *name || r.path.ends_with(&format!("::{name}")))
            .collect();
        if matches.is_empty() {
            missing.push(name);
            report.push_str(&format!("{name}    NOT ANALYZED\n"));
            continue;
        }
        for m in matches {
            if m.verified {
                let t = m.time.as_deref().unwrap_or("");
                report.push_str(&format!("{name}    verified  {t}\n"));
            } else {
                refuted.push(name);
                report.push_str(&format!("{name}    REFUTED\n"));
            }
        }
    }
    print_report(&report);

    if !refuted.is_empty() || !missing.is_empty() {
        let mut msg = String::from("verus_spec_check: kani tier failed:\n");
        for r in &refuted {
            msg.push_str(&format!(
                "  {r}: REFUTED — kani found an input violating the contract \
                 (rerun `cargo kani --tests --harness {r}` for the counterexample trace)\n"
            ));
        }
        for m in &missing {
            msg.push_str(&format!(
                "  {m}: expected proof harness never appeared in kani's output — \
                 the gate must not pass vacuously\n"
            ));
        }
        panic!("{msg}");
    }
}

/// The once-per-process `cargo kani --tests` side run.
fn side_run(crate_dir: &str) -> Result<BTreeMap<String, HarnessResult>, String> {
    probe_or_install()?;

    // Scratch target dir under the user's target root (same convention
    // as the covext side profile): kani's codegen artifacts must not
    // thrash the primary cache, and one scratch dir serves repeated
    // runs so only the first is slow.
    let base = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("target"));
    let scratch = base.join("verus-spec-check-kani");

    eprintln!(
        "verus_spec_check: running `cargo kani --tests` (first run compiles the dependency \
         graph under kani's codegen — minutes; later runs reuse {scratch:?})"
    );

    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let mut child = Command::new(&cargo)
        .args(["kani", "--tests"])
        .current_dir(crate_dir)
        .env("CARGO_TARGET_DIR", &scratch)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("spawn `cargo kani --tests`: {e}"))?;

    // Wall-clock cap, when requested. Reading the pipes AFTER wait
    // risks deadlock on full pipe buffers, so drain them on threads.
    let timeout: Option<Duration> = std::env::var("VERUS_SPEC_CHECK_KANI_TIMEOUT")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .map(Duration::from_secs);
    let mut stdout_pipe = child.stdout.take().expect("piped stdout");
    let mut stderr_pipe = child.stderr.take().expect("piped stderr");
    let out_thread = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stdout_pipe.read_to_string(&mut s);
        s
    });
    let err_thread = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr_pipe.read_to_string(&mut s);
        s
    });
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|e| format!("wait on cargo kani: {e}"))?
        {
            break status;
        }
        if let Some(cap) = timeout {
            if start.elapsed() > cap {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!(
                    "`cargo kani --tests` exceeded VERUS_SPEC_CHECK_KANI_TIMEOUT ({}s) and was \
                     killed. Raise the timeout, or investigate the slow harness with \
                     `cargo kani --tests --harness <name>`.",
                    cap.as_secs()
                ));
            }
        }
        std::thread::sleep(Duration::from_millis(200));
    };
    let stdout = out_thread.join().unwrap_or_default();
    let stderr = err_thread.join().unwrap_or_default();
    let combined = format!("{stdout}\n{stderr}");

    let results = parse_kani_output(&combined);

    // A run that produced NO harness results and failed is a build /
    // setup problem, not a refutation — surface the output tail.
    if results.is_empty() {
        let tail: String = combined
            .lines()
            .rev()
            .take(30)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n");
        return Err(format!(
            "`cargo kani --tests` produced no harness results (exit: {status}). \
             Output tail:\n{tail}"
        ));
    }
    Ok(results)
}

/// Probe for cargo-kani; optionally self-install when
/// `VERUS_SPEC_CHECK_KANI_INSTALL=1`.
fn probe_or_install() -> Result<(), String> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let probe = |cargo: &str| {
        Command::new(cargo)
            .args(["kani", "--version"])
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    };
    if probe(&cargo) {
        return Ok(());
    }
    if std::env::var("VERUS_SPEC_CHECK_KANI_INSTALL").as_deref() == Ok("1") {
        eprintln!(
            "verus_spec_check: cargo-kani not found; VERUS_SPEC_CHECK_KANI_INSTALL=1 — installing \
             (downloads kani's toolchain + CBMC; this can take a while)"
        );
        let install_ok = Command::new(&cargo)
            .args(["install", "--locked", "kani-verifier"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        let setup_ok = install_ok
            && Command::new(&cargo)
                .args(["kani", "setup"])
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
        if setup_ok && probe(&cargo) {
            return Ok(());
        }
        return Err("self-install failed — install manually: \
                    `cargo install --locked kani-verifier && cargo kani setup`"
            .to_string());
    }
    Err(
        "cargo-kani is not installed, but this crate has `#[vcheck(mode = \"kani\")]` \
         harnesses. Install it:\n    cargo install --locked kani-verifier && cargo kani setup\n\
         or set VERUS_SPEC_CHECK_KANI_INSTALL=1 to let the report install it, \
         or set VERUS_SPEC_CHECK_KANI=0 to skip the kani tier on this machine."
            .to_string(),
    )
}

/// Parse `cargo kani --tests` output into per-harness results.
///
/// Shape (kani 0.6x):
/// ```text
/// Checking harness __verus_spec_check_0::vcheck_safe_add...
/// ...
/// VERIFICATION:- SUCCESSFUL
/// Verification Time: 0.32s
/// ```
/// The `Checking harness` line opens a block; the next
/// `VERIFICATION:-` line closes it. Anything outside blocks is
/// ignored.
fn parse_kani_output(out: &str) -> BTreeMap<String, HarnessResult> {
    let mut results = BTreeMap::new();
    let mut current: Option<String> = None;
    let mut time: Option<String> = None;
    for line in out.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("Checking harness ") {
            current = Some(rest.trim_end_matches("...").to_string());
            time = None;
            continue;
        }
        if let Some(t) = line.strip_prefix("Verification Time: ") {
            time = Some(t.to_string());
        }
        if line.starts_with("VERIFICATION:-") {
            if let Some(path) = current.take() {
                let verified = line.contains("SUCCESSFUL");
                results.insert(
                    path.clone(),
                    HarnessResult {
                        path,
                        verified,
                        time: time.take(),
                    },
                );
            }
        }
    }
    // `Verification Time` prints AFTER the verdict line; a second pass
    // attaching times would need block tracking — instead accept the
    // pre-verdict capture when present and let the trailing time of the
    // LAST harness attach on the next `Checking harness` reset. Times
    // are display-only, so best-effort is fine.
    results
}

/// Report printing: /dev/tty by default so `cargo test` shows it
/// inline; stderr in quiet mode (same convention as the cov_fuzz and
/// cov_mutate reporters).
fn print_report(s: &str) {
    #[cfg(unix)]
    if std::env::var("VERUS_SPEC_CHECK_KANI_QUIET").as_deref() != Ok("1") {
        use std::io::Write;
        if let Ok(mut tty) = std::fs::OpenOptions::new().write(true).open("/dev/tty") {
            if tty.write_all(s.as_bytes()).is_ok() {
                return;
            }
        }
    }
    eprintln!("{s}");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_successful_and_failed_blocks() {
        let out = "\
Checking harness __verus_spec_check_0::vcheck_good...

VERIFICATION:- SUCCESSFUL
Verification Time: 0.32s

Checking harness __verus_spec_check_0::vcheck_bad...

VERIFICATION:- FAILED

Complete - 1 successfully verified harnesses, 1 failures, 2 total.";
        let r = parse_kani_output(out);
        assert_eq!(r.len(), 2);
        assert!(r["__verus_spec_check_0::vcheck_good"].verified);
        assert!(!r["__verus_spec_check_0::vcheck_bad"].verified);
    }

    #[test]
    fn ignores_noise_outside_blocks() {
        let out = "Compiling foo\nVERIFICATION:- SUCCESSFUL\nwarning: bar";
        // A verdict with no opening `Checking harness` line is dropped.
        assert!(parse_kani_output(out).is_empty());
    }
}
