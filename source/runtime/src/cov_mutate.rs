//! Runtime support for `#[vcheck_cov_mutate]` — measures how thoroughly each
//! marked fn's `ensures` clause covers its body.
//!
//! ## Architecture
//!
//! The macro emits one [`VcheckCovMutateTarget`] constant per marked fn,
//! plus a synthesized `__vcheck_mutation_report` test. The target carries
//! a slice of [`VcheckCovMutant`] records, one per mutation site found in
//! the body. Each mutant has a `run` callback that executes a self-
//! contained proptest harness against the mutated body, returning
//! `true` when the post-condition fails on at least one input (the
//! mutant is *killed*) or `false` when every input passes (the mutant
//! *survives*).
//!
//! [`run_mutation_report`] walks the targets, tallies per-fn kill
//! rates, prints a report to stderr, and panics when any per-fn
//! threshold is violated. There is no external tool, no subprocess,
//! and no JSON parsing — the entire pipeline runs in-process.

use std::collections::BTreeMap;

/// A function whose ensures-clause coverage we want to assess. One per
/// `#[vcheck_cov_mutate]`-marked fn in the crate.
#[derive(Clone, Debug)]
pub struct VcheckCovMutateTarget {
    /// Display name used in the report (qualified for impl methods,
    /// e.g. `"Counter::step"`; bare ident for free fns).
    pub fn_name: &'static str,
    /// Source file of the original fn (informational; the report uses
    /// the per-mutant `line` instead).
    pub file: &'static str,
    /// One entry per mutation site found in the fn's body. Built at
    /// macro expansion time by the body-mutator visitor.
    pub mutants: &'static [VcheckCovMutant],
    /// Optional kill-rate threshold (0..=100). When set and the kill
    /// rate falls below it, the report run panics so `cargo test`
    /// fails.
    pub threshold: Option<u8>,
    /// When `true`, the runner records the target in the report header
    /// but does not execute the mutant runners. Useful for muting one
    /// fn temporarily without removing the attribute.
    pub skip: bool,
}

/// Metadata + executor for one body mutation. The `run` callback is a
/// closure-equivalent fn the macro emits alongside the parallel mutant
/// fn; it sets up a small proptest harness and returns whether the
/// mutated body's post-condition was violated by any sampled input.
#[derive(Clone, Debug)]
pub struct VcheckCovMutant {
    /// 1-based index used for diagnostics.
    pub idx: u32,
    /// Source line of the mutation site in the original body.
    pub line: u32,
    /// Short human-readable description (e.g. `"+ -> -"`,
    /// `"return -> Default::default()"`).
    pub description: &'static str,
    /// Fn that runs the mutant's harness. Returns `true` if the mutant
    /// is *killed* (some input made the post-condition fail) and
    /// `false` if it *survives*.
    pub run: fn() -> MutantOutcome,
}

/// Outcome of running one mutant's harness in-process.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MutantOutcome {
    /// At least one input made the post-condition fail (mutant killed).
    Killed,
    /// Every sampled input satisfied the post-condition (mutant
    /// survived).
    Survived,
    /// All sampled inputs were rejected by `prop_assume!` for the
    /// pre-condition. The mutant is recorded but excluded from the
    /// kill-rate denominator since we don't have evidence either way.
    Inconclusive,
}

/// Aggregated per-fn results.
#[derive(Default, Debug)]
struct TargetResult {
    killed: u32,
    survived: u32,
    inconclusive: u32,
    survivors: Vec<&'static VcheckCovMutant>,
}

impl TargetResult {
    fn kill_rate_pct(&self) -> u32 {
        let denom = self.killed + self.survived;
        if denom == 0 {
            return 0;
        }
        (self.killed * 100) / denom
    }
}

/// Entry point invoked by the macro-emitted `__vcheck_mutation_report`
/// test. Walks `targets`, runs each non-skipped mutant in process,
/// prints a report, and panics on per-fn threshold violations.
/// Entry point invoked by the macro-emitted `__vcheck_mutation_report`
/// test. Walks `targets`, runs each non-skipped mutant in process,
/// prints a concise report directly to the controlling terminal
/// (`/dev/tty` on Unix; falls back to stderr on other platforms),
/// and panics on per-fn threshold violations.
///
/// The terminal write bypasses cargo's per-test stdout/stderr
/// capture, so plain `cargo test` shows the report inline without
/// needing `--nocapture`.
pub fn run_mutation_report(_crate_dir: &str, targets: &[VcheckCovMutateTarget]) {
    if targets.is_empty() {
        return;
    }
    let mut results: BTreeMap<&'static str, TargetResult> = BTreeMap::new();
    let mut skipped: Vec<&'static str> = Vec::new();
    for target in targets {
        if target.skip {
            skipped.push(target.fn_name);
            continue;
        }
        let mut tr = TargetResult::default();
        for m in target.mutants {
            match (m.run)() {
                MutantOutcome::Killed => tr.killed += 1,
                MutantOutcome::Survived => {
                    tr.survived += 1;
                    tr.survivors.push(m);
                }
                MutantOutcome::Inconclusive => tr.inconclusive += 1,
            }
        }
        results.insert(target.fn_name, tr);
    }

    let report = format_report(targets, &results, &skipped);
    print_to_terminal(&report);

    let mut violations: Vec<(String, u32, u8)> = Vec::new();
    for target in targets {
        if target.skip {
            continue;
        }
        if let Some(thr) = target.threshold {
            if let Some(tr) = results.get(target.fn_name) {
                let pct = tr.kill_rate_pct();
                if (pct as u8) < thr {
                    violations.push((target.fn_name.to_string(), pct, thr));
                }
            }
        }
    }
    if !violations.is_empty() {
        let lines: Vec<String> = violations
            .iter()
            .map(|(n, pct, thr)| format!("  {n}: kill rate {pct}% < threshold {thr}%"))
            .collect();
        panic!(
            "verus_spec_check cov_mutate threshold(s) violated:\n{}",
            lines.join("\n")
        );
    }
}

/// Write `s` to the controlling terminal, bypassing cargo's per-test
/// stdout/stderr capture. On Unix the terminal is reachable via
/// `/dev/tty`. On other platforms (Windows) we fall back to stderr,
/// which `cargo test` still captures by default — Windows users
/// can pass `--nocapture` or `--show-output` to see the report.
///
/// Set `VERUS_SPEC_CHECK_COV_MUTATE_QUIET=1` to skip the terminal write and
/// emit on stderr instead, so the report obeys normal `cargo test`
/// capture. Useful when these harnesses run nested inside another test
/// process, or in CI logs, where an uncapturable write is noise. The
/// report is still there with `--nocapture` / `--show-output`, and still
/// lands in captured output that a harness failure would print.
fn print_to_terminal(s: &str) {
    #[cfg(unix)]
    if !quiet_requested() {
        use std::io::Write;
        if let Ok(mut tty) = std::fs::OpenOptions::new().write(true).open("/dev/tty") {
            if tty.write_all(s.as_bytes()).is_ok() {
                return;
            }
        }
    }
    // Non-Unix, quiet requested, or `/dev/tty` open/write failed (e.g.
    // running headless under CI without a controlling terminal): fall
    // back to stderr. Visible only with `--nocapture` / `--show-output`
    // under cargo test.
    eprint!("{}", s);
}

/// Whether `VERUS_SPEC_CHECK_COV_MUTATE_QUIET` asks us to skip the `/dev/tty`
/// write. Any value except unset, empty, or `0` counts as "quiet".
fn quiet_requested() -> bool {
    match std::env::var("VERUS_SPEC_CHECK_COV_MUTATE_QUIET") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

/// Build the human-readable mutation coverage report as a single
/// owned `String`. Caller decides what to do with it (write to file,
/// print to stderr, both, panic with it as a message).
fn format_report(
    targets: &[VcheckCovMutateTarget],
    results: &BTreeMap<&'static str, TargetResult>,
    skipped: &[&'static str],
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();

    let _ = writeln!(out);
    let _ = writeln!(out, "mutation coverage report");
    let _ = writeln!(out, "────────────────────────");

    let max_name = targets
        .iter()
        .map(|t| t.fn_name.len())
        .max()
        .unwrap_or(0)
        .max(20);

    let mut grand_killed: u32 = 0;
    let mut grand_total: u32 = 0;
    for target in targets {
        if target.skip {
            let _ = writeln!(out, "{:<width$}  skipped", target.fn_name, width = max_name);
            continue;
        }
        let Some(tr) = results.get(target.fn_name) else {
            continue;
        };
        if target.mutants.is_empty() {
            let _ = writeln!(
                out,
                "{:<width$}  (no mutation sites — body too small or only spec syntax)",
                target.fn_name,
                width = max_name
            );
            continue;
        }
        let scored = tr.killed + tr.survived;
        let pct = tr.kill_rate_pct();
        let threshold_note = match target.threshold {
            Some(t) => format!("  (threshold {}%)", t),
            None => String::new(),
        };
        let _ = writeln!(
            out,
            "{:<width$}  ensures clause kills {}/{} body mutants  ({}%){}",
            target.fn_name,
            tr.killed,
            scored,
            pct,
            threshold_note,
            width = max_name
        );
        if !tr.survivors.is_empty() {
            let _ = writeln!(out, "  surviving:");
            for s in &tr.survivors {
                let _ = writeln!(out, "    {}:{}  {}", target.file, s.line, s.description);
                let _ = writeln!(out, "                  ensures clause did not detect");
            }
        }
        if tr.inconclusive > 0 {
            let _ = writeln!(
                out,
                "  ({} inconclusive — all inputs rejected by prop_assume!)",
                tr.inconclusive
            );
        }
        grand_killed += tr.killed;
        grand_total += scored;
    }
    if grand_total > 0 {
        let overall_pct = (grand_killed * 100) / grand_total;
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "overall:  {} / {}  ({}%)",
            grand_killed, grand_total, overall_pct
        );
    } else {
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "overall:  no mutation sites found in any target — \
             coverage assessment doesn't apply to these bodies."
        );
    }
    if !skipped.is_empty() {
        let _ = writeln!(out, "skipped: {}", skipped.join(", "));
    }
    let _ = writeln!(out);
    out
}
