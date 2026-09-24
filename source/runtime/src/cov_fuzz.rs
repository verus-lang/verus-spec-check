//! Runtime support for `#[vcheck_cov_fuzz]` — measures how many branch arms
//! of each marked fn's *implementation* are reachable by inputs drawn from
//! its specification's domain (the `requires`-constrained generator).
//!
//! ## Architecture
//!
//! The macro emits, per marked fn:
//!  - an *instrumented twin* of the body (each branch arm entry bumps a
//!    hit bit in a per-fn `static [AtomicBool; N]`),
//!  - a runner fn that decodes byte buffers into the fn's parameter tuple
//!    (via the bolero generator stack), filters them through `requires`,
//!    calls the twin, and — when at least one `ensures` clause ENGAGES on
//!    the execution (its `==>` antecedent chain holds; non-implication
//!    clauses engage always) — credits the arms this execution reached to
//!    the per-fn `covered` array. The threshold gates the covered
//!    percentage: "how much of the implementation does the spec speak
//!    about". Ablating an ensures clause shrinks it,
//!  - one [`VcheckCovFuzzTarget`] record per fn, aggregated by a synthesized
//!    `__vcheck_cov_fuzz_report` test.
//!
//! The runner does not sample blindly: [`coverage_guided_loop`] runs an
//! in-process coverage-guided search. Byte buffers are the genome; the
//! feedback signal is the union of (a) the implementation's branch hit
//! bits and (b) per-`requires`-clause "satisfied" bits (guidance-only —
//! they steer the search toward precondition-conforming inputs but are
//! NOT part of the reported statistic). Buffers that light a new bit
//! join the corpus and are mutated further; standard greedy corpus
//! evolution. This is the same mechanism a coverage-guided fuzzer uses,
//! scoped per-fn and running under plain `cargo test` — no nightly, no
//! external tool, no subprocess.
//!
//! [`run_cov_fuzz_report`] walks the targets, runs each non-skipped
//! search, reads back the hit bits, prints a report, and panics when a
//! per-fn `threshold` is violated.
//!
//! ## Reading the report
//!
//! Two numbers per fn:
//!
//! - **spec covers N/M** — the gated statistic: arms reached by an
//!   execution at least one ensures clause ENGAGES on. Ablating an
//!   ensures clause shrinks it; a fn with no ensures covers nothing.
//! - **inputs reach N/M** — plain reachability from the requires-
//!   constrained domain (the generator-adequacy signal).
//!
//! An *unspecified* arm is reached, but only by inputs no ensures
//! clause speaks about — a spec gap: add (or un-ablate) a clause whose
//! antecedent covers those inputs. An *unreached* arm means the search
//! never found a `requires`-conforming input that executes it. That is
//! one of: (a) the spec's precondition excludes the path (spec-domain
//! gap — often the interesting finding), (b) the generator can't
//! produce the shape (generator gap), (c) the path is dead code, or
//! (d) the search budget was too small (raise
//! `VERUS_SPEC_CHECK_COV_FUZZ_BUDGET`). Both statistics are search-based and
//! therefore lower bounds; give thresholds headroom. Engagement is a
//! syntactic proxy (antecedent truth): it cannot detect a consequent
//! that is trivially true — that spec-strength question belongs to
//! `#[vcheck_cov_mutate]`.
//!
//! ## Environment knobs
//!
//! - `VERUS_SPEC_CHECK_COV_FUZZ_BUDGET`  — executions per target (default 4096).
//! - `VERUS_SPEC_CHECK_COV_FUZZ_SEED`    — u64 RNG seed (default fixed, so runs
//!   are deterministic unless overridden).
//! - `VERUS_SPEC_CHECK_COV_FUZZ_QUIET`   — `1` routes the report to stderr
//!   (obeying cargo's capture) instead of `/dev/tty`.
//! - `VERUS_SPEC_CHECK_COV_CAMPAIGN`    — `1` switches every `__vcheck_cov_fuzz_report`
//!   test into campaign mode: the first report test to run performs ONE
//!   audit over ALL registered targets in the binary (via the link-time
//!   registry) and every other report test returns immediately. This is
//!   the repository-audit entry point — external side-profile tiers are
//!   probed and built once for the whole campaign instead of once per
//!   module.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicBool, Ordering};

// Re-exported for the macro-generated registry entries
// (`#[distributed_slice(...)]` needs a nameable path to the real crate).
#[doc(hidden)]
pub use linkme;

/// Link-time registry of every expansion's cov_fuzz target block. Each
/// `#[vcheck_cov_fuzz]`-bearing macro expansion contributes one entry; the
/// campaign audit walks the whole slice. Entries exist only in test
/// builds (the generated statics live in `#[cfg(test)]` modules).
#[linkme::distributed_slice]
pub static VCHECK_COV_FUZZ_REGISTRY: [VcheckCovFuzzRegistryEntry];

/// One expansion's contribution to [`VCHECK_COV_FUZZ_REGISTRY`].
#[derive(Debug)]
pub struct VcheckCovFuzzRegistryEntry {
    /// `CARGO_MANIFEST_DIR` of the crate the targets were expanded in —
    /// the directory the external side-profile build runs from.
    pub crate_dir: &'static str,
    /// The expansion's target table (same array its own report test uses).
    pub targets: &'static [VcheckCovFuzzTarget],
}

/// A function whose implementation branch coverage we want to assess.
/// One per `#[vcheck_cov_fuzz]`-marked fn in the crate.
#[derive(Debug)]
pub struct VcheckCovFuzzTarget {
    /// Collision-safe registration identity. This is the only value used
    /// for maps, replay selection, and artifacts; `fn_name` is display-only.
    pub target_id: &'static str,
    /// Display name used in the report (qualified for impl methods,
    /// e.g. `"Counter::step"`; bare ident for free fns).
    pub fn_name: &'static str,
    /// Source file of the original fn.
    pub file: &'static str,
    /// The source instrumenter reached its per-function branch-arm cap.
    /// Such a target is partial evidence and can never satisfy a threshold.
    pub branch_cap_hit: bool,
    /// One entry per branch arm found in the fn's body. Built at macro
    /// expansion time by the branch instrumenter; `branches[i]`
    /// describes hit slot `hits[i]`.
    pub branches: &'static [VcheckCovFuzzBranch],
    /// The per-fn hit-bit array the instrumented twin writes into.
    /// Read (not written) by the report after the runner finishes.
    pub hits: &'static [AtomicBool],
    /// Parallel to `hits`: arm i is set when some execution reached it
    /// while at least one `ensures` clause was ENGAGED on that same
    /// execution (an implication clause engages when its antecedent
    /// chain holds; a non-implication clause engages every execution).
    /// This is the spec-coverage statistic the `threshold` gates:
    /// "which parts of the implementation does the specification
    /// actually speak about". Ablating an ensures clause shrinks it.
    pub covered: &'static [AtomicBool],
    /// Parallel to `hits`: arm i was reached by an execution for which no
    /// lowerable clause engaged and at least one clause's antecedent was
    /// unlowerable. These arms are neither covered nor safely classifiable
    /// as unspecified.
    pub indeterminate: &'static [AtomicBool],
    /// Static descriptions of clauses whose engagement could not be lowered.
    pub unlowerable_ensures: &'static [VcheckCovFuzzUnlowerableClause],
    /// Runs the coverage-guided search for this fn and returns its
    /// execution stats. Emitted by the macro; drives the instrumented
    /// twin via [`coverage_guided_loop`].
    pub run: fn() -> CovFuzzRunStats,
    /// Optional branch-coverage threshold (0..=100). When set and the
    /// reached percentage falls below it, the report run panics so
    /// `cargo test` fails.
    pub threshold: Option<u8>,
    /// When `true`, the target appears in the report header but the
    /// search is not run. Useful for muting one fn temporarily without
    /// removing the attribute.
    pub skip: bool,
    /// `Some(..)` when the marked fn is an `assume_specification`
    /// wrapper: the measured implementation lives in an external crate
    /// (often std/core), so there is no source-level twin — `branches`
    /// and `hits` are empty and `run` is a stub. External targets are
    /// measured via an instrumented side profile (llvm-cov) rather than
    /// the in-process search; until that orchestration runs, the report
    /// annotates the row as not-yet-measured.
    pub external: Option<VcheckCovFuzzExternal>,
}

/// One ensures clause whose engagement antecedent has no runtime lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VcheckCovFuzzUnlowerableClause {
    pub clause: usize,
    pub reason: &'static str,
}

/// External-measurement metadata for an assume_specification target.
#[derive(Debug)]
pub struct VcheckCovFuzzExternal {
    /// The path the assume_specification names (e.g. `u32::checked_add`,
    /// `<[u8]>::binary_search`) — matched against demangled function
    /// names in the coverage profile.
    pub target_path: &'static str,
    /// Type parameters in the generated assume-spec wrapper. The external
    /// matcher uses these to distinguish generic self-type patterns such as
    /// `[T]` from concrete self types such as `[u8]` without relying on
    /// identifier naming conventions.
    pub generic_type_params: &'static [&'static str],
    /// Stable macro-time selector used to compile a rescue side binary
    /// containing only this target (or a small shard containing it). Unlike
    /// `target_id`, this cannot use `module_path!()` because compile-time
    /// selection happens while the target crate is being compiled.
    pub compile_selector: &'static str,
    /// Exact fully-qualified libtest name of this target's replay test.
    pub replay_test: &'static str,
    /// Records spec engagement per ensures clause. The side-profile
    /// orchestrator replays the aggregate sample set and each clause's
    /// sample subset in isolated profiles.
    pub recorder: fn() -> CovExtRecording,
}

/// Arbitrarily-sized set of engaged ensures-clause indices.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClauseMask {
    words: Vec<u64>,
}

impl ClauseMask {
    pub fn new(clause_count: usize) -> Self {
        Self {
            words: vec![0; clause_count.saturating_add(63) / 64],
        }
    }

    pub fn set(&mut self, clause: usize) {
        if let Some(word) = self.words.get_mut(clause / 64) {
            *word |= 1u64 << (clause % 64);
        }
    }

    pub fn contains(&self, clause: usize) -> bool {
        self.words
            .get(clause / 64)
            .map(|word| word & (1u64 << (clause % 64)) != 0)
            .unwrap_or(false)
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CovExtSample {
    pub genome: Vec<u8>,
    pub engaged_clauses: ClauseMask,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CovExtRecording {
    pub clause_count: usize,
    pub samples: Vec<CovExtSample>,
    pub unlowerable_clauses: Vec<VcheckCovFuzzUnlowerableClause>,
    pub probes: Vec<CovFuzzProbeResult>,
}

/// Metadata for one branch arm (parallel to one hit bit).
#[derive(Clone, Debug)]
pub struct VcheckCovFuzzBranch {
    /// 0-based hit-array slot.
    pub idx: u32,
    /// Source line of the branch construct in the original body.
    pub line: u32,
    /// Short human-readable arm description (e.g. `"if (then branch)"`).
    pub description: &'static str,
}

/// Outcome of driving ONE decoded input through the runner's closure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecOutcome {
    /// The input satisfied `requires` and the twin ran.
    Tested,
    /// The input was rejected by a `requires` clause (or skipped as an
    /// unspecified-`real` case).
    Skipped,
    /// The byte buffer failed to decode into the parameter tuple.
    Invalid,
}

/// Observation from a non-failing specification-strengthening probe.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CovFuzzProbeResult {
    /// Verifier-facing clause the observed invariant suggests adding.
    pub suggestion: &'static str,
    pub checks: u64,
    pub violations: u64,
}

/// Aggregate stats from one target's search run.
#[derive(Clone, Debug, Default)]
pub struct CovFuzzRunStats {
    /// Inputs that satisfied `requires` and executed the twin.
    pub tested: u64,
    /// Inputs rejected by `requires`.
    pub skipped: u64,
    /// Byte buffers that failed to decode.
    pub invalid: u64,
    /// Executions that panicked inside the twin (counted as tested —
    /// the body was entered and its hit bits up to the panic stand).
    pub panicked: u64,
    /// Final corpus size (inputs that each lit at least one new
    /// feedback bit when first executed).
    pub corpus: usize,
    /// Total executions attempted (the budget actually spent).
    pub executions: u64,
    /// Advisory observations that never affect pass/fail by themselves.
    pub probes: Vec<CovFuzzProbeResult>,
}

// ---------------------------------------------------------------------------
// Environment knobs
// ---------------------------------------------------------------------------

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(default)
}

/// Executions per target. Deliberately modest by default so the report
/// test stays fast in a big suite; raise it when chasing a stubborn arm.
pub fn budget_from_env() -> u64 {
    env_u64("VERUS_SPEC_CHECK_COV_FUZZ_BUDGET", 4096)
}

fn seed_from_env() -> u64 {
    // An arbitrary fixed odd constant (splitmix64's golden-ratio
    // increment) so default runs are deterministic.
    env_u64("VERUS_SPEC_CHECK_COV_FUZZ_SEED", 0x9E37_79B9_7F4A_7C15)
}

// ---------------------------------------------------------------------------
// Deterministic RNG (no external dep)
// ---------------------------------------------------------------------------

/// splitmix64: tiny, deterministic, plenty good for mutation scheduling.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform-ish value in `0..n` (n > 0).
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

// ---------------------------------------------------------------------------
// Coverage-guided search
// ---------------------------------------------------------------------------

/// Number of feedback bits currently set across all feedback arrays.
/// Feedback is monotone (bits only turn on), so a simple recount after
/// each execution detects novelty. Arrays are small (branch arms +
/// requires clauses), so recounting is cheap relative to an execution.
fn count_set(feedback: &[&[AtomicBool]]) -> usize {
    feedback
        .iter()
        .flat_map(|arr| arr.iter())
        .filter(|b| b.load(Ordering::Relaxed))
        .count()
}

/// Mutate `buf` in place with one randomly chosen byte-level operator.
/// The operator set is the standard small-fuzzer kit: bit flip, byte
/// splat, arithmetic nudge, interesting-value splat, insert, remove,
/// duplicate-extend, and splice-with-donor.
fn mutate(buf: &mut Vec<u8>, rng: &mut Rng, donor: Option<&[u8]>) {
    const INTERESTING: [u8; 8] = [0x00, 0x01, 0x7F, 0x80, 0xFF, 0x10, 0x40, 0xFE];
    // Ensure there's something to mutate.
    if buf.is_empty() {
        buf.push(rng.next() as u8);
        return;
    }
    match rng.below(8) {
        0 => {
            // Bit flip.
            let i = rng.below(buf.len());
            buf[i] ^= 1 << rng.below(8);
        }
        1 => {
            // Byte splat.
            let i = rng.below(buf.len());
            buf[i] = rng.next() as u8;
        }
        2 => {
            // Arithmetic nudge.
            let i = rng.below(buf.len());
            let delta = (rng.below(8) as u8).wrapping_add(1);
            buf[i] = if rng.next() & 1 == 0 {
                buf[i].wrapping_add(delta)
            } else {
                buf[i].wrapping_sub(delta)
            };
        }
        3 => {
            // Interesting-value splat.
            let i = rng.below(buf.len());
            buf[i] = INTERESTING[rng.below(INTERESTING.len())];
        }
        4 => {
            // Insert a random byte.
            let i = rng.below(buf.len() + 1);
            buf.insert(i, rng.next() as u8);
        }
        5 => {
            // Remove a byte.
            let i = rng.below(buf.len());
            buf.remove(i);
        }
        6 => {
            // Duplicate a tail chunk (grows the buffer, which lets
            // collection generators draw more elements).
            let start = rng.below(buf.len());
            let chunk: Vec<u8> = buf[start..].to_vec();
            buf.extend_from_slice(&chunk);
            buf.truncate(MAX_BUF_LEN);
        }
        _ => {
            // Splice with a donor corpus entry (crossover), when one
            // exists; otherwise append random bytes.
            if let Some(d) = donor.filter(|d| !d.is_empty()) {
                let cut = rng.below(buf.len());
                let dcut = rng.below(d.len());
                buf.truncate(cut);
                buf.extend_from_slice(&d[dcut..]);
                buf.truncate(MAX_BUF_LEN);
            } else {
                let extra = rng.below(8) + 1;
                for _ in 0..extra {
                    buf.push(rng.next() as u8);
                }
                buf.truncate(MAX_BUF_LEN);
            }
        }
    }
}

/// Genome size cap. The bolero byte driver zero-fills past the end of
/// the buffer, so a short genome always decodes; longer genomes give
/// collection generators room to draw more elements.
const MAX_BUF_LEN: usize = 4096;

// ---------------------------------------------------------------------------
// Deterministic boundary seeds
// ---------------------------------------------------------------------------

/// Selector bytes that address every edge bucket of the edge-biased
/// integer generators (`bolero_gen.rs`): each integer parameter draws a
/// selector `u8` first, and `sel % 30` (signed) / `sel % 24` (unsigned)
/// routes to an edge value. The values below cover every bucket of both
/// tables — e.g. `0` = signed MIN / unsigned 0, `10` = signed `-1`,
/// `4` = signed MAX, `2` = unsigned MAX.
const BOUNDARY_SELECTORS: [u8; 8] = [0, 2, 4, 6, 8, 10, 14, 16];

/// Focused selector pairs for the small unsigned widths. Each tuple is
/// `(draw width, first selector, second selector)`: u8 consumes two bytes
/// per draw and u16 consumes three. Keep these ahead of the broad Cartesian
/// sweep so low budgets and per-clause replay quotas retain underflow,
/// zero-divisor, and next-multiple overflow inputs without displacing the
/// existing i64-first broad priority.
const FOCUSED_UNSIGNED_PAIR_SEEDS: [(usize, u8, u8); 6] = [
    (2, 0, 6), // u8:  (MIN, 1) — checked_sub underflow
    (2, 2, 0), // u8:  (MAX, 0) — zero rhs
    (2, 2, 8), // u8:  (MAX, MAX - 1) — next-multiple overflow
    (3, 0, 6), // u16: (MIN, 1) — checked_sub underflow
    (3, 2, 0), // u16: (MAX, 0) — zero rhs
    (3, 2, 8), // u16: (MAX, MAX - 1) — next-multiple overflow
];

/// Split points for the broad two-segment sweep: one selector byte plus the
/// raw width of each primitive size (8/16/32/64/128-bit -> 2/3/5/9/17 bytes
/// per parameter draw). Ordered 64-bit-first: the widest types are where
/// random search misses unseeded boundary pairs most often.
const BOUNDARY_SPLITS: [usize; 5] = [9, 5, 3, 2, 17];

/// Length of the constant fill; enough bytes for several parameter draws
/// at any width (the driver zero-fills past the end regardless).
const BOUNDARY_FILL_LEN: usize = 40;

/// Deterministic boundary seed genomes, executed before random search in
/// both guided loops.
///
/// Rationale: random byte mutation essentially never coordinates 16+
/// bytes into value pairs like `(i64::MIN, -1)` or `(iN::MIN, 1)`, yet
/// those exact pairs are where trusted numeric specs have historically
/// been wrong (`checked_rem(MIN, -1)`) and where the vstd audit's only
/// generator-caused coverage gaps were (the overflow/zero-divisor arms
/// of `i64::checked_div`/`rem`/`div_euclid`/`rem_euclid`/
/// `checked_sub_unsigned`). The edge-biased generators make every such
/// pair BYTE-ADDRESSABLE through selector bytes, so seeds need no
/// knowledge of the concrete parameter types:
///
/// - a constant fill `[k; N]` makes EVERY parameter draw selector `k`
///   (each draw reads only `k` bytes), pinning all parameters to one
///   edge bucket — `(MIN, MIN)`, `(MAX, MAX)`, ...;
/// - a two-segment fill `[a; split] ++ [b; ...]` pins the first
///   parameter to bucket `a` and subsequent parameters to bucket `b`
///   whenever `split` matches the first parameter's draw width; sweeping
///   `split` over the primitive widths covers every alignment, and a
///   mismatched split merely produces another (harmless) combination;
/// - raw-extreme fills (`0x7F`/`0x80`/`0xFF`) feed the uniform buckets'
///   raw draws with sign/magnitude extremes.
///
/// Seeds that light new feedback bits enter the corpus and per-clause
/// samples exactly like any other input — for external targets this is
/// what guarantees boundary pairs are RETAINED for replay before the
/// per-clause quotas fill with ordinary inputs. The list is truncated to
/// half the execution budget so seeding can never crowd out the search.
pub(crate) fn boundary_seed_genomes(budget: u64) -> Vec<Vec<u8>> {
    let mut seeds: Vec<Vec<u8>> = Vec::new();
    for (split, first, second) in FOCUSED_UNSIGNED_PAIR_SEEDS {
        let mut genome = vec![first; split];
        genome.resize(BOUNDARY_FILL_LEN.max(split), second);
        seeds.push(genome);
    }
    for k in BOUNDARY_SELECTORS {
        seeds.push(vec![k; BOUNDARY_FILL_LEN]);
    }
    for k in [0x7Fu8, 0x80, 0xFF] {
        seeds.push(vec![k; BOUNDARY_FILL_LEN]);
    }
    for split in BOUNDARY_SPLITS {
        for a in BOUNDARY_SELECTORS {
            for b in BOUNDARY_SELECTORS {
                if a == b {
                    continue; // identical to the constant fill above
                }
                let mut genome = vec![a; split];
                genome.resize(BOUNDARY_FILL_LEN.max(split), b);
                seeds.push(genome);
            }
        }
    }
    let cap = usize::try_from(budget / 2).unwrap_or(usize::MAX);
    seeds.truncate(cap);
    seeds
}

/// Run the coverage-guided search: repeatedly execute `exec` on byte
/// buffers, keeping any buffer that lights a new feedback bit as a
/// corpus entry for further mutation.
///
/// Panic note: panicking executions are caught, but the default panic
/// hook still PRINTS each one. Under plain `cargo test` that lands in
/// the captured (discarded-on-pass) output; with `--nocapture` a
/// panic-heavy target is noisy. Deliberately not suppressed — swapping
/// the process-global hook would race with concurrently running tests
/// (and cov_mutate's proptest-based runners behave the same way).
///
/// `feedback` is the union of feedback arrays — by convention the
/// target's branch hit bits plus its requires-clause guidance bits. The
/// caller (the macro-emitted runner) owns the arrays; this loop only
/// counts them. Executions that panic are caught (the twin's hit bits
/// up to the panic still count) and tallied as `panicked` + `tested`.
///
/// Deterministic for a fixed seed/budget: no wall-clock, no OS RNG.
pub fn coverage_guided_loop(
    feedback: &[&[AtomicBool]],
    exec: &mut dyn FnMut(&[u8]) -> ExecOutcome,
) -> CovFuzzRunStats {
    let budget = budget_from_env();
    let mut rng = Rng(seed_from_env());
    let mut stats = CovFuzzRunStats::default();
    let mut corpus: Vec<Vec<u8>> = Vec::new();
    let mut known_bits = count_set(feedback);

    // A panic in the twin must not abort the report test: catch it,
    // count it, and keep searching. The closure only touches atomics
    // and its own locals, so unwind-safety is fine to assert.
    let mut run_one = |bytes: &[u8], stats: &mut CovFuzzRunStats| -> ExecOutcome {
        stats.executions += 1;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec(bytes)));
        match result {
            Ok(outcome) => outcome,
            Err(_) => {
                stats.panicked += 1;
                ExecOutcome::Tested
            }
        }
    };

    // Seed executions: the empty buffer (all-zero decode — minimal
    // values), the deterministic boundary genomes (edge-value
    // combinations random mutation essentially never coordinates — see
    // `boundary_seed_genomes`), plus a few fixed-size random buffers, so
    // the corpus has material before mutation starts.
    // Small seeds concentrate subsequent mutations on few bytes (the
    // buffer can still grow via insert/duplicate, and the bolero driver
    // zero-fills past the end, so short buffers always decode).
    let mut seeds: Vec<Vec<u8>> = vec![Vec::new()];
    seeds.extend(boundary_seed_genomes(budget));
    for len in [4usize, 16, 64] {
        let mut b = Vec::with_capacity(len);
        for _ in 0..len {
            b.push(rng.next() as u8);
        }
        seeds.push(b);
    }
    for seed in seeds {
        if stats.executions >= budget {
            break;
        }
        let outcome = run_one(&seed, &mut stats);
        tally(outcome, &mut stats);
        let now = count_set(feedback);
        if now > known_bits {
            known_bits = now;
            corpus.push(seed);
        }
    }

    while stats.executions < budget {
        // Candidate: usually a mutation of a corpus entry; sometimes a
        // fresh random buffer to keep exploring globally.
        let mut candidate: Vec<u8> = if corpus.is_empty() || rng.below(8) == 0 {
            let len = rng.below(32) + 1;
            let mut b = Vec::with_capacity(len);
            for _ in 0..len {
                b.push(rng.next() as u8);
            }
            b
        } else {
            corpus[rng.below(corpus.len())].clone()
        };
        if !corpus.is_empty() {
            // 1..=4 stacked mutations per candidate.
            let donor_idx = rng.below(corpus.len());
            let donor = corpus[donor_idx].clone();
            let n_mut = rng.below(4) + 1;
            for _ in 0..n_mut {
                mutate(&mut candidate, &mut rng, Some(&donor));
            }
        }

        let outcome = run_one(&candidate, &mut stats);
        tally(outcome, &mut stats);
        let now = count_set(feedback);
        if now > known_bits {
            known_bits = now;
            corpus.push(candidate);
        }
    }

    stats.corpus = corpus.len();
    stats
}

fn tally(outcome: ExecOutcome, stats: &mut CovFuzzRunStats) {
    match outcome {
        ExecOutcome::Tested => stats.tested += 1,
        ExecOutcome::Skipped => stats.skipped += 1,
        ExecOutcome::Invalid => stats.invalid += 1,
    }
}

// ---------------------------------------------------------------------------
// External-target engagement recording + replay
// ---------------------------------------------------------------------------

/// Outcome of one recorder execution. `clauses` is the exact local
/// engagement mask for this input, not the cumulative search feedback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordOutcome {
    Tested { clauses: ClauseMask },
    Skipped,
    Invalid,
}

/// Maximum retained genomes per ensures clause. The old aggregate knob is
/// accepted as a compatibility fallback.
pub fn covext_samples_per_clause_from_env() -> usize {
    let value = std::env::var("VERUS_SPEC_CHECK_COVEXT_SAMPLES_PER_CLAUSE")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or_else(|| env_u64("VERUS_SPEC_CHECK_COVEXT_SAMPLES", 256));
    usize::try_from(value).unwrap_or(usize::MAX)
}

/// Engagement-guided search for external targets. Samples are retained
/// independently per ensures clause and carry the exact engagement mask from
/// their own execution. Search-corpus admission remains feedback-based and is
/// independent of replay-sample admission.
pub fn covext_record_loop(
    feedback: &[&[AtomicBool]],
    clause_count: usize,
    exec: &mut dyn FnMut(&[u8]) -> RecordOutcome,
) -> CovExtRecording {
    let budget = budget_from_env();
    let per_clause_cap = covext_samples_per_clause_from_env();
    let mut rng = Rng(seed_from_env());
    let mut stats = CovFuzzRunStats::default();
    let mut corpus: Vec<Vec<u8>> = Vec::new();
    let mut samples: Vec<CovExtSample> = Vec::new();
    let mut saved_per_clause = vec![0usize; clause_count];
    let mut seen: BTreeSet<Vec<u8>> = BTreeSet::new();
    let mut known_bits = count_set(feedback);

    let mut run_one = |bytes: &[u8], stats: &mut CovFuzzRunStats| -> RecordOutcome {
        stats.executions += 1;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec(bytes))) {
            Ok(outcome) => outcome,
            Err(_) => {
                stats.panicked += 1;
                RecordOutcome::Invalid
            }
        }
    };

    let mut retain = |genome: &[u8], outcome: RecordOutcome| {
        let RecordOutcome::Tested { clauses } = outcome else {
            return;
        };
        if clauses.is_empty() || seen.contains(genome) {
            return;
        }
        let serves_open_clause =
            (0..clause_count).any(|j| clauses.contains(j) && saved_per_clause[j] < per_clause_cap);
        if !serves_open_clause {
            return;
        }
        for (j, saved) in saved_per_clause.iter_mut().enumerate() {
            if clauses.contains(j) && *saved < per_clause_cap {
                *saved += 1;
            }
        }
        seen.insert(genome.to_vec());
        samples.push(CovExtSample {
            genome: genome.to_vec(),
            engaged_clauses: clauses,
        });
    };

    // Same seed schedule as `coverage_guided_loop`, with one extra
    // property that matters here: boundary seeds run BEFORE random
    // search, so the per-clause replay quotas retain edge-value
    // combinations first instead of filling up with ordinary inputs
    // (the exact failure mode behind the vstd i64 overflow-arm gaps).
    let mut seeds: Vec<Vec<u8>> = vec![Vec::new()];
    seeds.extend(boundary_seed_genomes(budget));
    for len in [4usize, 16, 64] {
        let mut b = Vec::with_capacity(len);
        for _ in 0..len {
            b.push(rng.next() as u8);
        }
        seeds.push(b);
    }
    for seed in seeds {
        if stats.executions >= budget {
            break;
        }
        let outcome = run_one(&seed, &mut stats);
        retain(&seed, outcome);
        let now = count_set(feedback);
        if now > known_bits {
            known_bits = now;
            corpus.push(seed);
        }
    }

    while stats.executions < budget {
        let mut candidate: Vec<u8> = if corpus.is_empty() || rng.below(8) == 0 {
            let len = rng.below(32) + 1;
            let mut b = Vec::with_capacity(len);
            for _ in 0..len {
                b.push(rng.next() as u8);
            }
            b
        } else {
            corpus[rng.below(corpus.len())].clone()
        };
        if !corpus.is_empty() {
            let donor_idx = rng.below(corpus.len());
            let donor = corpus[donor_idx].clone();
            let n_mut = rng.below(4) + 1;
            for _ in 0..n_mut {
                mutate(&mut candidate, &mut rng, Some(&donor));
            }
        }

        let outcome = run_one(&candidate, &mut stats);
        retain(&candidate, outcome);
        let now = count_set(feedback);
        if now > known_bits {
            known_bits = now;
            corpus.push(candidate);
        }
    }

    CovExtRecording {
        clause_count,
        samples,
        unlowerable_clauses: Vec::new(),
        probes: Vec::new(),
    }
}

/// Stable, filesystem-safe artifact key for a target registration ID.
pub(crate) fn covext_target_file_key(target_id: &str) -> String {
    // Two seeded FNV-1a lanes make accidental collisions negligible while
    // avoiding a new hashing dependency in the runtime crate.
    fn lane(s: &str, mut hash: u64) -> u64 {
        for byte in s.bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01B3);
        }
        hash
    }
    format!(
        "{:016x}{:016x}",
        lane(target_id, 0xcbf2_9ce4_8422_2325),
        lane(target_id, 0x8422_2325_cbf2_9ce4)
    )
}

/// Compile-time membership test for comma-separated rescue selectors.
/// Generated replay functions call this with `option_env!`, allowing MIR
/// constant propagation to remove every nonselected target call before
/// codegen while Cargo tracks selector changes as an environment dependency.
pub const fn covext_rescue_selector_enabled(list: &str, selector: &str) -> bool {
    let list = list.as_bytes();
    let selector = selector.as_bytes();
    let mut start = 0usize;
    while start <= list.len() {
        let mut end = start;
        while end < list.len() && list[end] != b',' {
            end += 1;
        }
        if end - start == selector.len() {
            let mut i = 0usize;
            let mut equal = true;
            while i < selector.len() {
                if list[start + i] != selector[i] {
                    equal = false;
                    break;
                }
                i += 1;
            }
            if equal {
                return true;
            }
        }
        if end == list.len() {
            break;
        }
        start = end + 1;
    }
    false
}

/// Load genomes for the one target selected by the side-profile runner.
/// Outside a selected side run this is a normal no-op; once selected, every
/// missing or malformed artifact is an error.
pub fn covext_replay_genomes(target_id: &str) -> Result<Option<Vec<Vec<u8>>>, String> {
    let Some(selected) = std::env::var_os("VERUS_SPEC_CHECK_COVEXT_TARGET_ID") else {
        return Ok(None);
    };
    if selected != std::ffi::OsStr::new(target_id) {
        return Ok(None);
    }
    let dir = std::env::var_os("VERUS_SPEC_CHECK_COVEXT_GENOME_DIR")
        .ok_or_else(|| "selected replay has no genome directory".to_string())?;
    let path =
        std::path::Path::new(&dir).join(format!("{}.genomes", covext_target_file_key(target_id)));
    let bytes =
        std::fs::read(&path).map_err(|e| format!("read selected replay genomes {path:?}: {e}"))?;
    parse_genomes(&bytes)
        .map(Some)
        .map_err(|e| format!("parse selected replay genomes {path:?}: {e}"))
}

/// Write the selected replay's completion marker. The orchestrator requires
/// this marker in addition to a successful libtest exit, because libtest also
/// exits successfully when an exact filter matches zero tests.
pub fn covext_mark_replay_complete(target_id: &str) -> Result<(), String> {
    let selected = std::env::var("VERUS_SPEC_CHECK_COVEXT_TARGET_ID")
        .map_err(|_| "replay completion without selected target".to_string())?;
    if selected != target_id {
        return Err(format!(
            "replay target mismatch: selected `{selected}`, executed `{target_id}`"
        ));
    }
    let marker = std::env::var_os("VERUS_SPEC_CHECK_COVEXT_COMPLETION_FILE")
        .ok_or_else(|| "selected replay has no completion marker path".to_string())?;
    std::fs::write(&marker, target_id.as_bytes())
        .map_err(|e| format!("write replay completion marker {marker:?}: {e}"))
}

/// Serialize genomes: `u32 LE count`, then per genome `u32 LE len` + bytes.
pub(crate) fn encode_genomes(genomes: &[Vec<u8>]) -> Result<Vec<u8>, String> {
    let count = u32::try_from(genomes.len())
        .map_err(|_| "too many replay genomes to serialize".to_string())?;
    let mut out = Vec::new();
    out.extend_from_slice(&count.to_le_bytes());
    for genome in genomes {
        let len = u32::try_from(genome.len())
            .map_err(|_| "replay genome is too large to serialize".to_string())?;
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(genome);
    }
    Ok(out)
}

fn parse_genomes(bytes: &[u8]) -> Result<Vec<Vec<u8>>, String> {
    const MAX_GENOMES: usize = 1_000_000;
    let mut at = 0usize;
    let take = |at: &mut usize, n: usize| -> Result<&[u8], String> {
        let end = at
            .checked_add(n)
            .ok_or_else(|| "replay genome length overflow".to_string())?;
        let slice = bytes
            .get(*at..end)
            .ok_or_else(|| "truncated replay genome data".to_string())?;
        *at = end;
        Ok(slice)
    };
    let count = u32::from_le_bytes(
        take(&mut at, 4)?
            .try_into()
            .map_err(|_| "invalid replay genome count".to_string())?,
    ) as usize;
    if count > MAX_GENOMES {
        return Err(format!("replay genome count {count} exceeds safety limit"));
    }
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let len = u32::from_le_bytes(
            take(&mut at, 4)?
                .try_into()
                .map_err(|_| "invalid replay genome length".to_string())?,
        ) as usize;
        if len > MAX_BUF_LEN {
            return Err(format!("replay genome length {len} exceeds {MAX_BUF_LEN}"));
        }
        out.push(take(&mut at, len)?.to_vec());
    }
    if at != bytes.len() {
        return Err("trailing bytes after replay genomes".to_string());
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Contract-checking guided search (`#[vcheck(mode = "fuzz")]` under cargo test)
// ---------------------------------------------------------------------------

/// Outcome of driving ONE decoded input through a *contract-checking*
/// runner closure (the `mode = "fuzz"` harness under plain `cargo
/// test`). Same shape as [`ExecOutcome`] plus a failure arm: an
/// `ensures` clause that evaluated false. The payload is the macro-
/// stringified clause text, used in the counterexample report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContractExec {
    /// The input satisfied `requires`, the body ran, every `ensures`
    /// clause held.
    Tested,
    /// The input was rejected by a `requires` clause (or skipped as an
    /// unspecified-`real` case).
    Skipped,
    /// The byte buffer failed to decode into the parameter tuple.
    Invalid,
    /// An `ensures` clause evaluated false for this input.
    Failed(&'static str),
}

/// Result of one [`guided_contract_loop`] run.
#[derive(Debug)]
pub enum ContractVerdict {
    /// The budget was spent without finding a violation.
    Passed(CovFuzzRunStats),
    /// A violating input was found (and shrunk). `genome` is the
    /// minimized byte buffer — re-decoding it through the same
    /// generator reproduces the counterexample. `failure` is either
    /// the failing clause text or the panic message when the body
    /// itself panicked.
    Failed {
        genome: Vec<u8>,
        failure: String,
        stats: CovFuzzRunStats,
    },
}

/// Executions per `mode = "fuzz"` harness under plain `cargo test`.
/// Separate knob from the cov_fuzz report budget: this one gates every
/// fuzz-mode test's runtime, not a single aggregated report. Miri
/// executes ~orders-of-magnitude slower, so the default drops there.
pub fn fuzz_budget_from_env() -> u64 {
    let default = if cfg!(miri) { 64 } else { 4096 };
    env_u64("VERUS_SPEC_CHECK_FUZZ_BUDGET", default)
}

fn fuzz_seed_from_env() -> u64 {
    // Same fixed default as the cov_fuzz search: deterministic unless
    // overridden.
    env_u64("VERUS_SPEC_CHECK_FUZZ_SEED", 0x9E37_79B9_7F4A_7C15)
}

/// Extra executions granted to the shrink phase after a failure. Kept
/// separate from the search budget so a failure found on the last
/// execution still shrinks.
const SHRINK_BUDGET: u64 = 768;

/// Best-effort text of a caught panic payload.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// Coverage-guided search that CHECKS the contract: same corpus
/// mechanics as [`coverage_guided_loop`] (byte genomes, greedy
/// evolution on the union of branch-hit and requires-guidance bits),
/// but a `Failed` outcome — or a panic in `exec` — stops the search,
/// and the failing genome is minimized by a byte-level shrink pass
/// before being returned.
///
/// This is the `#[vcheck(mode = "fuzz")]` engine under plain `cargo
/// test`: strictly stronger than a random smoke run (the loop injects
/// fresh random buffers as part of exploration), with branch feedback
/// steering the search into the body and guidance bits steering it
/// through the precondition.
///
/// Deterministic for a fixed seed/budget, like its sibling.
pub fn guided_contract_loop(
    feedback: &[&[AtomicBool]],
    exec: &mut dyn FnMut(&[u8]) -> ContractExec,
) -> ContractVerdict {
    let budget = fuzz_budget_from_env();
    let mut rng = Rng(fuzz_seed_from_env());
    let mut stats = CovFuzzRunStats::default();
    let mut corpus: Vec<Vec<u8>> = Vec::new();
    let mut known_bits = count_set(feedback);

    // A failing execution is a panic (caught) or an explicit
    // `Failed(..)`. Both count as `tested` — the body was entered.
    let mut run_one = |bytes: &[u8], stats: &mut CovFuzzRunStats| -> ContractExec {
        stats.executions += 1;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec(bytes))) {
            Ok(outcome) => outcome,
            Err(payload) => {
                stats.panicked += 1;
                // The panic message is recovered by the caller via a
                // re-run during shrinking; here it only needs to read
                // as a failure. The leaked-str trick is avoided by
                // carrying panic text separately below.
                let _ = payload;
                ContractExec::Failed("<panicked>")
            }
        }
    };

    // Shared post-execution bookkeeping. Returns the failure text when
    // the outcome is failing.
    fn digest(outcome: ContractExec, stats: &mut CovFuzzRunStats) -> Option<&'static str> {
        match outcome {
            ContractExec::Tested => {
                stats.tested += 1;
                None
            }
            ContractExec::Skipped => {
                stats.skipped += 1;
                None
            }
            ContractExec::Invalid => {
                stats.invalid += 1;
                None
            }
            ContractExec::Failed(clause) => {
                stats.tested += 1;
                Some(clause)
            }
        }
    }

    let mut failure: Option<(Vec<u8>, &'static str)> = None;

    // Seed executions (same shapes as the coverage loop).
    let mut seeds: Vec<Vec<u8>> = vec![Vec::new()];
    for len in [4usize, 16, 64] {
        let mut b = Vec::with_capacity(len);
        for _ in 0..len {
            b.push(rng.next() as u8);
        }
        seeds.push(b);
    }
    'search: {
        for seed in seeds {
            if stats.executions >= budget {
                break 'search;
            }
            let outcome = run_one(&seed, &mut stats);
            if let Some(clause) = digest(outcome, &mut stats) {
                failure = Some((seed, clause));
                break 'search;
            }
            let now = count_set(feedback);
            if now > known_bits {
                known_bits = now;
                corpus.push(seed);
            }
        }

        while stats.executions < budget {
            let mut candidate: Vec<u8> = if corpus.is_empty() || rng.below(8) == 0 {
                let len = rng.below(32) + 1;
                let mut b = Vec::with_capacity(len);
                for _ in 0..len {
                    b.push(rng.next() as u8);
                }
                b
            } else {
                corpus[rng.below(corpus.len())].clone()
            };
            if !corpus.is_empty() {
                let donor_idx = rng.below(corpus.len());
                let donor = corpus[donor_idx].clone();
                let n_mut = rng.below(4) + 1;
                for _ in 0..n_mut {
                    mutate(&mut candidate, &mut rng, Some(&donor));
                }
            }

            let outcome = run_one(&candidate, &mut stats);
            if let Some(clause) = digest(outcome, &mut stats) {
                failure = Some((candidate, clause));
                break 'search;
            }
            let now = count_set(feedback);
            if now > known_bits {
                known_bits = now;
                corpus.push(candidate);
            }
        }
    }

    stats.corpus = corpus.len();

    let Some((genome, _clause)) = failure else {
        return ContractVerdict::Passed(stats);
    };

    // Shrink, then run the minimized genome one final time (uncaught
    // stats bump aside) to recover the definitive failure text — the
    // shrunk input may fail a different clause than the original, and
    // panic messages are only recoverable from a live run.
    let genome = shrink_genome(genome, exec, &mut stats);
    stats.executions += 1;
    let failure_text =
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec(&genome))) {
            Ok(ContractExec::Failed(clause)) => clause.to_string(),
            Ok(_) => {
                // Shouldn't happen (shrink only keeps failing candidates),
                // but never mask the original find.
                "ensures clause failed (unstable reproduction — rerun with \
                 VERUS_SPEC_CHECK_FUZZ_SEED to investigate)"
                    .to_string()
            }
            Err(payload) => format!("body panicked: {}", panic_message(payload.as_ref())),
        };
    ContractVerdict::Failed {
        genome,
        failure: failure_text,
        stats,
    }
}

/// Byte-level minimization of a failing genome. "Still fails" =
/// `Failed(..)` or panic, clause identity NOT required (any failure is
/// as good as the original — clause drift is resolved by the final
/// re-run in the caller). Every candidate decodes because the bolero
/// byte driver zero-fills past the end of the buffer, which is what
/// makes naive byte-level shrinking effective here: truncation and
/// zeroing move every decoded value toward its minimal shape.
///
/// Passes, repeated to fixpoint within [`SHRINK_BUDGET`] executions:
///   1. prefix truncation (binary search on length),
///   2. chunk removal (halving chunk sizes, ddmin-lite),
///   3. per-byte zeroing,
///   4. per-byte halving (drives magnitudes down when 0 flips the
///      branch away from the failure).
fn shrink_genome(
    mut genome: Vec<u8>,
    exec: &mut dyn FnMut(&[u8]) -> ContractExec,
    stats: &mut CovFuzzRunStats,
) -> Vec<u8> {
    let mut spent: u64 = 0;
    let mut still_fails = |bytes: &[u8], spent: &mut u64, stats: &mut CovFuzzRunStats| -> bool {
        *spent += 1;
        stats.executions += 1;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| exec(bytes))) {
            Ok(outcome) => matches!(outcome, ContractExec::Failed(_)),
            Err(_) => {
                stats.panicked += 1;
                true
            }
        }
    };

    loop {
        let before = genome.clone();

        // Pass 1: shortest failing prefix, by binary search. The
        // predicate isn't guaranteed monotone in length, but in
        // practice zero-fill makes shorter prefixes strictly simpler.
        let mut lo = 0usize; // longest known-passing length (as prefix)
        let mut hi = genome.len(); // known-failing length
        while lo < hi && spent < SHRINK_BUDGET {
            let mid = lo + (hi - lo) / 2;
            if still_fails(&genome[..mid], &mut spent, stats) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        genome.truncate(hi);

        // Pass 2: remove chunks, largest first.
        let mut chunk = (genome.len() / 2).max(1);
        while chunk >= 1 && spent < SHRINK_BUDGET {
            let mut start = 0usize;
            while start < genome.len() && spent < SHRINK_BUDGET {
                let end = (start + chunk).min(genome.len());
                let mut candidate = Vec::with_capacity(genome.len() - (end - start));
                candidate.extend_from_slice(&genome[..start]);
                candidate.extend_from_slice(&genome[end..]);
                if still_fails(&candidate, &mut spent, stats) {
                    genome = candidate;
                    // Same start now names the next chunk; don't advance.
                } else {
                    start += chunk;
                }
            }
            if chunk == 1 {
                break;
            }
            chunk /= 2;
        }

        // Pass 3: zero bytes.
        for i in 0..genome.len() {
            if genome[i] == 0 || spent >= SHRINK_BUDGET {
                continue;
            }
            let saved = genome[i];
            genome[i] = 0;
            if !still_fails(&genome, &mut spent, stats) {
                genome[i] = saved;
            }
        }

        // Pass 4: halve bytes toward zero.
        for i in 0..genome.len() {
            while genome[i] > 0 && spent < SHRINK_BUDGET {
                let saved = genome[i];
                genome[i] /= 2;
                if !still_fails(&genome, &mut spent, stats) {
                    genome[i] = saved;
                    break;
                }
            }
        }

        if genome == before || spent >= SHRINK_BUDGET {
            return genome;
        }
    }
}

// ---------------------------------------------------------------------------
// Report
// ---------------------------------------------------------------------------

/// Per-target result assembled after the search ran.
#[derive(Debug)]
struct TargetResult {
    /// Arms some requires-conforming input reached (regardless of
    /// whether the spec engages there) — the generator-adequacy signal.
    reached: u32,
    /// Arms reached by an input at least one ensures clause ENGAGES on
    /// — the spec-coverage statistic the threshold gates.
    covered: u32,
    total: u32,
    /// Arms no input reached at all.
    unreached: Vec<&'static VcheckCovFuzzBranch>,
    /// Arms reached only while engagement remained unknowable because an
    /// antecedent could not be lowered.
    indeterminate: Vec<&'static VcheckCovFuzzBranch>,
    /// Arms reached, but only by inputs no ensures clause speaks about
    /// (spec gap: the implementation path exists, the spec is silent).
    unspecified: Vec<&'static VcheckCovFuzzBranch>,
    stats: CovFuzzRunStats,
}

impl TargetResult {
    fn covered_pct(&self) -> u32 {
        if self.total == 0 {
            // A straight-line body has nothing to miss.
            return 100;
        }
        (self.covered * 100) / self.total
    }
}

/// Entry point invoked by the macro-emitted `__vcheck_cov_fuzz_report`
/// test. Walks `targets`, runs each non-skipped target's coverage
/// search in process, reads back the hit bits, prints a concise report
/// directly to the controlling terminal (`/dev/tty` on Unix; falls
/// back to stderr elsewhere), and panics on per-fn threshold
/// violations.
///
/// The terminal write bypasses cargo's per-test capture so plain
/// `cargo test` shows the report inline; set
/// `VERUS_SPEC_CHECK_COV_FUZZ_QUIET=1` to emit on stderr instead (obeying
/// normal capture — useful nested inside another test process or CI).
///
/// Under `VERUS_SPEC_CHECK_COV_CAMPAIGN=1`, per-module behavior is replaced by
/// a whole-binary campaign: see [`run_cov_fuzz_campaign`].
pub fn run_cov_fuzz_report(crate_dir: &str, targets: &[VcheckCovFuzzTarget]) {
    if campaign_requested() {
        run_cov_fuzz_campaign();
        return;
    }
    let refs: Vec<&VcheckCovFuzzTarget> = targets.iter().collect();
    run_cov_fuzz_report_refs(crate_dir, &refs);
}

/// Whether `VERUS_SPEC_CHECK_COV_CAMPAIGN` selects campaign mode. Any non-empty
/// value except `0` enables it.
fn campaign_requested() -> bool {
    match std::env::var("VERUS_SPEC_CHECK_COV_CAMPAIGN") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

/// Run ONE audit over every cov_fuzz target registered in this binary
/// (all expansions, all modules), exactly once per process.
///
/// The first caller is elected the runner; every subsequent caller
/// returns immediately. Because every module's `__vcheck_cov_fuzz_report`
/// test funnels here under `VERUS_SPEC_CHECK_COV_CAMPAIGN=1`, a plain
/// `cargo test __vcheck_cov_fuzz_report` performs the whole audit in one
/// pass regardless of which report test libtest schedules first — the
/// expensive side-profile tiers are probed and built once for the
/// entire campaign. Targets are grouped per crate dir (one external
/// orchestration per crate).
///
/// Threshold/strict violations panic in whichever report test was
/// elected; the others pass as no-ops.
pub fn run_cov_fuzz_campaign() {
    // Deliberately NOT `std::sync::Once`: a strict-mode violation panics
    // out of the campaign, and a poisoned `Once` would then fail every
    // remaining report test with a confusing poison message instead of
    // letting them no-op.
    static CLAIMED: AtomicBool = AtomicBool::new(false);
    if CLAIMED.swap(true, Ordering::SeqCst) {
        return;
    }
    let mut by_crate: BTreeMap<&'static str, Vec<&'static VcheckCovFuzzTarget>> = BTreeMap::new();
    for entry in VCHECK_COV_FUZZ_REGISTRY {
        for target in entry.targets {
            by_crate.entry(entry.crate_dir).or_default().push(target);
        }
    }
    assert!(
        !by_crate.is_empty(),
        "VERUS_SPEC_CHECK_COV_CAMPAIGN is set but no #[vcheck_cov_fuzz] targets are \
         registered in this binary"
    );
    for (crate_dir, targets) in &by_crate {
        run_cov_fuzz_report_refs(crate_dir, targets);
    }
}

/// Every non-skipped external target path registered in this binary,
/// across ALL expansions. Used to derive ONE MIR-manifest needle set
/// for the whole binary, so per-module report runs share a single
/// cached manifest pass instead of keying one per module.
pub(crate) fn registry_external_target_paths() -> Vec<&'static str> {
    let mut out = Vec::new();
    for entry in VCHECK_COV_FUZZ_REGISTRY {
        for target in entry.targets {
            if target.skip {
                continue;
            }
            if let Some(ext) = &target.external {
                out.push(ext.target_path);
            }
        }
    }
    out
}

fn run_cov_fuzz_report_refs(crate_dir: &str, targets: &[&VcheckCovFuzzTarget]) {
    if targets.is_empty() {
        return;
    }
    let mut target_ids = BTreeSet::new();
    for target in targets {
        assert!(
            target_ids.insert(target.target_id),
            "duplicate vcheck_cov_fuzz target_id `{}`",
            target.target_id
        );
    }
    let mut results: BTreeMap<&'static str, TargetResult> = BTreeMap::new();
    let mut skipped_targets: Vec<&'static str> = Vec::new();
    for target in targets {
        if target.skip {
            skipped_targets.push(target.fn_name);
            continue;
        }
        // External (assume_specification) targets have no in-process
        // search to run: their measurement comes from the instrumented
        // side profile, orchestrated once for all of them below.
        if target.external.is_some() {
            continue;
        }
        let stats = (target.run)();
        let mut reached = 0u32;
        let mut covered = 0u32;
        let mut unreached: Vec<&'static VcheckCovFuzzBranch> = Vec::new();
        let mut indeterminate: Vec<&'static VcheckCovFuzzBranch> = Vec::new();
        let mut unspecified: Vec<&'static VcheckCovFuzzBranch> = Vec::new();
        for branch in target.branches {
            let hit = target
                .hits
                .get(branch.idx as usize)
                .map(|b| b.load(Ordering::Relaxed))
                .unwrap_or(false);
            let cov = target
                .covered
                .get(branch.idx as usize)
                .map(|b| b.load(Ordering::Relaxed))
                .unwrap_or(false);
            let indet = target
                .indeterminate
                .get(branch.idx as usize)
                .map(|b| b.load(Ordering::Relaxed))
                .unwrap_or(false);
            if cov {
                covered += 1;
            }
            if hit {
                reached += 1;
                if !cov && indet {
                    indeterminate.push(branch);
                } else if !cov {
                    unspecified.push(branch);
                }
            } else {
                unreached.push(branch);
            }
        }
        results.insert(
            target.target_id,
            TargetResult {
                reached,
                covered,
                total: target.branches.len() as u32,
                unreached,
                indeterminate,
                unspecified,
                stats,
            },
        );
    }

    // Side-profile measurement for external (assume_specification)
    // targets: instrumented rebuild + llvm-cov extraction, driven by
    // the wrapper harnesses. Never panics; failures come back as
    // per-target explanations.
    let ext_inputs: Vec<(&'static str, &VcheckCovFuzzExternal)> = targets
        .iter()
        .filter(|t| !t.skip)
        .filter_map(|t| t.external.as_ref().map(|e| (t.target_id, e)))
        .collect();
    let ext_results = if ext_inputs.is_empty() {
        BTreeMap::new()
    } else {
        crate::cov_fuzz_ext::measure_external_targets(crate_dir, &ext_inputs)
    };

    let report = format_report(targets, &results, &skipped_targets, &ext_results);
    print_to_terminal(&report);

    // Machine-readable dump (`VERUS_SPEC_CHECK_COV_JSON=<path>`) for CI
    // trending and diffing audit baselines. One JSON object per run;
    // under campaign mode with multiple crate roots (rare) the last
    // group wins — one crate per binary is the practical case.
    if let Some(path) = std::env::var_os("VERUS_SPEC_CHECK_COV_JSON") {
        let value = json_dump(crate_dir, targets, &results, &ext_results);
        if let Err(error) = std::fs::write(&path, value.to_string()) {
            eprintln!("verus_spec_check cov_fuzz: could not write VERUS_SPEC_CHECK_COV_JSON: {error}");
        }
    }

    let mut violations: Vec<String> = Vec::new();
    for target in targets {
        if target.skip {
            continue;
        }
        let Some(thr) = target.threshold else {
            continue;
        };
        if !target.unlowerable_ensures.is_empty() {
            let clauses = target
                .unlowerable_ensures
                .iter()
                .map(|entry| format!("ensures[{}] ({})", entry.clause, entry.reason))
                .collect::<Vec<_>>()
                .join(", ");
            violations.push(format!(
                "  {}: threshold {thr}% cannot be evaluated because spec engagement is indeterminate for {clauses}",
                target.fn_name
            ));
            continue;
        }
        if target.branch_cap_hit {
            violations.push(format!(
                "  {}: threshold {thr}% cannot be evaluated because branch instrumentation hit its cap",
                target.fn_name
            ));
            continue;
        }
        // External targets gate on the side-profile measurement. A
        // threshold on an UNMEASURED external target must fail loudly:
        // the user asked for a gate, and a gate that silently passes
        // because nothing was measured is worse than none.
        if let Some(ext) = &target.external {
            match ext_results.get(target.target_id) {
                Some(crate::cov_fuzz_ext::ExtResult::Measured(m)) => {
                    match m.branch_pct() {
                        Some(pct) if (pct as u8) < thr => violations.push(format!(
                            "  {}: external branch coverage {pct}% < threshold {thr}% (target `{}`)",
                            target.fn_name, ext.target_path
                        )),
                        Some(_) => {}
                        None => violations.push(format!(
                            "  {}: threshold {thr}% requires true LLVM branch-arm evidence for `{}`, but only a reachability proxy was available",
                            target.fn_name, ext.target_path
                        )),
                    }
                }
                Some(crate::cov_fuzz_ext::ExtResult::Branchless { def_path, .. }) => {
                    // Same rule as branchless LOCAL targets: a branch
                    // threshold needs branch arms to gate on.
                    violations.push(format!(
                        "  {}: threshold {thr}% requires branch-arm evidence, but \
                         `{}` is branchless per the MIR manifest (`{def_path}`)",
                        target.fn_name, ext.target_path
                    ));
                }
                Some(crate::cov_fuzz_ext::ExtResult::Unavailable(why)) => {
                    violations.push(format!(
                        "  {}: threshold {thr}% set, but external target `{}` was \
                         not measured: {why}",
                        target.fn_name, ext.target_path
                    ));
                }
                None => {
                    violations.push(format!(
                        "  {}: threshold {thr}% set, but external target `{}` was \
                         not measured (orchestration did not run)",
                        target.fn_name, ext.target_path
                    ));
                }
            }
            continue;
        }
        if let Some(tr) = results.get(target.target_id) {
            if tr.total == 0 {
                violations.push(format!(
                    "  {}: threshold {thr}% requires branch-arm evidence, but the body has no instrumented branch sites",
                    target.fn_name
                ));
                continue;
            }
            let pct = tr.covered_pct();
            if (pct as u8) < thr {
                violations.push(format!(
                    "  {}: spec covers {pct}% of implementation branch arms \
                     < threshold {thr}% ({}/{} arms have an engaged ensures \
                     clause; {} reached)",
                    target.fn_name, tr.covered, tr.total, tr.reached
                ));
            }
        }
    }

    // Audit mode turns unavailable external measurements into hard failures
    // even when individual targets have no threshold. This is intended for
    // repository-wide coverage inventories, where a green test result must
    // not silently mean "measurement did not happen".
    if strict_audit_requested() {
        for target in targets {
            if target.skip {
                continue;
            }
            // A measured external target carries the same unlowerable
            // metadata in `measurement.clauses`; report it there with the
            // target path rather than duplicating it from the static target.
            if !matches!(
                ext_results.get(target.target_id),
                Some(crate::cov_fuzz_ext::ExtResult::Measured(_))
            ) {
                for entry in target.unlowerable_ensures {
                    violations.push(format!(
                        "  {}: strict audit cannot determine engagement for ensures[{}]: {}",
                        target.fn_name, entry.clause, entry.reason
                    ));
                }
            }
            let Some(ext) = &target.external else {
                continue;
            };
            match ext_results.get(target.target_id) {
                Some(crate::cov_fuzz_ext::ExtResult::Measured(measurement)) => {
                    for clause in &measurement.clauses {
                        match clause {
                            crate::cov_fuzz_ext::ExtClauseResult::Measured { .. } => {}
                            crate::cov_fuzz_ext::ExtClauseResult::NoSamples { clause } => {
                                violations.push(format!(
                                    "  {}: strict audit found no sampled engagement for ensures[{clause}] of `{}`",
                                    target.fn_name, ext.target_path
                                ));
                            }
                            crate::cov_fuzz_ext::ExtClauseResult::Unlowerable {
                                clause,
                                reason,
                            } => violations.push(format!(
                                "  {}: strict audit cannot determine engagement for ensures[{clause}] of `{}`: {reason}",
                                target.fn_name, ext.target_path
                            )),
                            crate::cov_fuzz_ext::ExtClauseResult::Unavailable {
                                clause, reason, ..
                            } => violations.push(format!(
                                "  {}: strict audit could not measure ensures[{clause}] of `{}`: {reason}",
                                target.fn_name, ext.target_path
                            )),
                        }
                    }
                }
                // Branchless targets PASS strict mode: the measurement
                // question was answered (by the MIR manifest) — there
                // are no branch arms to cover. This is the explicit
                // N/A class, distinct from "measurement did not happen".
                Some(crate::cov_fuzz_ext::ExtResult::Branchless { .. }) => {}
                Some(crate::cov_fuzz_ext::ExtResult::Unavailable(why)) => {
                    violations.push(format!(
                        "  {}: strict audit requires a measurement for `{}`, but it \
                         was unavailable: {}",
                        target.fn_name, ext.target_path, why
                    ));
                }
                None => {
                    violations.push(format!(
                        "  {}: strict audit requires a measurement for `{}`, but \
                         orchestration produced no result",
                        target.fn_name, ext.target_path
                    ));
                }
            }
        }
    }

    if !violations.is_empty() {
        panic!(
            "verus_spec_check cov_fuzz threshold(s) violated:\n{}",
            violations.join("\n")
        );
    }
}

/// Write `s` to the controlling terminal, bypassing cargo's per-test
/// capture (same convention as the cov_mutate reporter). Quiet mode or
/// a failed `/dev/tty` open falls back to stderr.
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
    eprint!("{}", s);
}

/// Whether `VERUS_SPEC_CHECK_COV_FUZZ_QUIET` asks us to skip the `/dev/tty`
/// write. Any value except unset, empty, or `0` counts as "quiet".
/// Shared with the side-profile orchestrator's progress notes.
pub(crate) fn quiet_requested() -> bool {
    match std::env::var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

/// Whether repository-audit mode requires every non-skipped external target
/// to produce a real measurement. Any non-empty value except `0` enables it.
fn strict_audit_requested() -> bool {
    match std::env::var("VERUS_SPEC_CHECK_COV_FUZZ_STRICT") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

/// Machine-readable audit dump: one row per target with its disposition
/// and evidence counts. Consumed by CI trending — the schema favors
/// stable, flat fields over mirroring internal types.
fn json_dump(
    crate_dir: &str,
    targets: &[&VcheckCovFuzzTarget],
    results: &BTreeMap<&'static str, TargetResult>,
    ext_results: &BTreeMap<&'static str, crate::cov_fuzz_ext::ExtResult>,
) -> serde_json::Value {
    let rows: Vec<serde_json::Value> = targets
        .iter()
        .map(|target| {
            let mut row = serde_json::json!({
                "target_id": target.target_id,
                "fn_name": target.fn_name,
            });
            let obj = row.as_object_mut().expect("object literal");
            if !target.unlowerable_ensures.is_empty() {
                obj.insert(
                    "unlowerable_ensures".into(),
                    serde_json::Value::Array(
                        target
                            .unlowerable_ensures
                            .iter()
                            .map(|entry| {
                                serde_json::json!({
                                    "clause": entry.clause,
                                    "reason": entry.reason,
                                })
                            })
                            .collect(),
                    ),
                );
            }
            if target.skip {
                obj.insert("disposition".into(), "skipped".into());
                return row;
            }
            let Some(ext) = &target.external else {
                obj.insert("disposition".into(), "local".into());
                if let Some(tr) = results.get(target.target_id) {
                    obj.insert("arms_covered".into(), tr.covered.into());
                    obj.insert("arms_reached".into(), tr.reached.into());
                    obj.insert("arms_indeterminate".into(), tr.indeterminate.len().into());
                    obj.insert("arms_total".into(), tr.total.into());
                    obj.insert(
                        "strengthening_probes".into(),
                        serde_json::Value::Array(
                            tr.stats
                                .probes
                                .iter()
                                .map(|probe| {
                                    serde_json::json!({
                                        "suggestion": probe.suggestion,
                                        "checks": probe.checks,
                                        "violations": probe.violations,
                                    })
                                })
                                .collect(),
                        ),
                    );
                }
                return row;
            };
            obj.insert("target_path".into(), ext.target_path.into());
            match ext_results.get(target.target_id) {
                Some(crate::cov_fuzz_ext::ExtResult::Measured(m)) => {
                    obj.insert("disposition".into(), "measured".into());
                    obj.insert("evidence".into(), format!("{:?}", m.evidence).into());
                    obj.insert("backend".into(), format!("{:?}", m.backend).into());
                    if let Some(reason) = &m.line_only_reason {
                        obj.insert("line_only_reason".into(), reason.as_str().into());
                    }
                    obj.insert(
                        "hit".into(),
                        m.branch_pct()
                            .map(|_| m.branches_hit)
                            .unwrap_or(m.regions_hit)
                            .into(),
                    );
                    obj.insert(
                        "total".into(),
                        m.branch_pct()
                            .map(|_| m.branches_total)
                            .unwrap_or(m.regions_total)
                            .into(),
                    );
                    obj.insert("regions_hit".into(), m.regions_hit.into());
                    obj.insert("regions_total".into(), m.regions_total.into());
                    if let Some(arms) = m.mir_arms {
                        obj.insert("mir_arms".into(), arms.into());
                    }
                    if let Some(note) = &m.arm_witness_note {
                        obj.insert("arm_witness_note".into(), note.as_str().into());
                    }
                    obj.insert(
                        "strengthening_probes".into(),
                        serde_json::Value::Array(
                            m.probes
                                .iter()
                                .map(|probe| {
                                    serde_json::json!({
                                        "suggestion": probe.suggestion,
                                        "checks": probe.checks,
                                        "violations": probe.violations,
                                    })
                                })
                                .collect(),
                        ),
                    );
                }
                Some(crate::cov_fuzz_ext::ExtResult::Branchless { def_path, probes }) => {
                    obj.insert("disposition".into(), "branchless".into());
                    obj.insert("def_path".into(), def_path.as_str().into());
                    obj.insert(
                        "strengthening_probes".into(),
                        serde_json::Value::Array(
                            probes
                                .iter()
                                .map(|probe| {
                                    serde_json::json!({
                                        "suggestion": probe.suggestion,
                                        "checks": probe.checks,
                                        "violations": probe.violations,
                                    })
                                })
                                .collect(),
                        ),
                    );
                }
                Some(crate::cov_fuzz_ext::ExtResult::Unavailable(reason)) => {
                    obj.insert("disposition".into(), "unavailable".into());
                    obj.insert("reason".into(), reason.as_str().into());
                }
                None => {
                    obj.insert("disposition".into(), "unavailable".into());
                    obj.insert("reason".into(), "orchestration did not run".into());
                }
            }
            row
        })
        .collect();
    serde_json::json!({
        "crate_dir": crate_dir,
        "targets": rows,
    })
}

/// Build the human-readable branch-coverage report as one owned String.
fn format_report(
    targets: &[&VcheckCovFuzzTarget],
    results: &BTreeMap<&'static str, TargetResult>,
    skipped: &[&'static str],
    ext_results: &BTreeMap<&'static str, crate::cov_fuzz_ext::ExtResult>,
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();

    let _ = writeln!(out);
    let _ = writeln!(out, "branch coverage report (cov_fuzz)");
    let _ = writeln!(out, "─────────────────────────────────");

    let max_name = targets
        .iter()
        .map(|t| t.fn_name.len())
        .max()
        .unwrap_or(0)
        .max(20);

    let mut branch_covered: u32 = 0;
    let mut branch_total: u32 = 0;
    let mut region_only_covered: u32 = 0;
    let mut region_only_total: u32 = 0;
    let mut external_unavailable: u32 = 0;
    let mut external_measured: u32 = 0;
    let mut external_branchless: u32 = 0;
    for target in targets {
        if target.skip {
            let _ = writeln!(out, "{:<width$}  skipped", target.fn_name, width = max_name);
            continue;
        }
        // Measured externals render unlowerable clauses below from their
        // isolated per-clause results. Keep static metadata here for local
        // targets and for externals whose measurement was unavailable.
        if !matches!(
            ext_results.get(target.target_id),
            Some(crate::cov_fuzz_ext::ExtResult::Measured(_))
        ) {
            for entry in target.unlowerable_ensures {
                let _ = writeln!(
                    out,
                    "  {} ensures[{}]: engagement indeterminate ({})",
                    target.fn_name, entry.clause, entry.reason
                );
            }
        }
        if let Some(ext) = &target.external {
            // External (assume_specification) target: measured via the
            // instrumented side profile (llvm-cov). Inputs are the
            // spec-engaged genomes recorded by the engagement-guided
            // search, so the number responds to ensures ablation
            // exactly like the in-process statistic.
            match ext_results.get(target.target_id) {
                Some(crate::cov_fuzz_ext::ExtResult::Measured(m)) => {
                    external_measured += 1;
                    let threshold_note = match target.threshold {
                        Some(t) => format!("  (branch threshold {}%)", t),
                        None => String::new(),
                    };
                    let pct = m
                        .observed_pct()
                        .map(|value| format!("{value}%"))
                        .unwrap_or_else(|| "N/A".to_string());
                    match m.evidence {
                        crate::cov_fuzz_ext::ExtEvidenceKind::MirArmsWitnessed => {
                            let _ = writeln!(
                                out,
                                "{:<width$}  external `{}`: {}/{} MIR branch arms witnessed via coverage counters ({}){}",
                                target.fn_name,
                                ext.target_path,
                                m.branches_hit,
                                m.branches_total,
                                pct,
                                threshold_note,
                                width = max_name
                            );
                        }
                        crate::cov_fuzz_ext::ExtEvidenceKind::BranchArms => {
                            let _ = writeln!(
                                out,
                                "{:<width$}  external `{}`: {}/{} true LLVM branch arms ({}){}",
                                target.fn_name,
                                ext.target_path,
                                m.branches_hit,
                                m.branches_total,
                                pct,
                                threshold_note,
                                width = max_name
                            );
                        }
                        crate::cov_fuzz_ext::ExtEvidenceKind::RegionsProxy => {
                            let _ = writeln!(
                                out,
                                "{:<width$}  external `{}`: {}/{} code regions ({}; REGION REACHABILITY PROXY){}",
                                target.fn_name,
                                ext.target_path,
                                m.regions_hit,
                                m.regions_total,
                                pct,
                                threshold_note,
                                width = max_name
                            );
                        }
                        crate::cov_fuzz_ext::ExtEvidenceKind::LinesProxy => {
                            let _ = writeln!(
                                out,
                                "{:<width$}  external `{}`: {}/{} source lines ({}; LINE REACHABILITY PROXY){}",
                                target.fn_name,
                                ext.target_path,
                                m.regions_hit,
                                m.regions_total,
                                pct,
                                threshold_note,
                                width = max_name
                            );
                        }
                    }
                    let _ = writeln!(
                        out,
                        "  [isolated side profile: {}; {:?} backend; {} matched instantiation(s)]",
                        m.tier, m.backend, m.instantiations
                    );
                    if let Some(reason) = &m.line_only_reason {
                        let _ = writeln!(out, "  [line-only reason: {reason}]");
                    } else if let Some(note) = &m.arm_witness_note {
                        let _ = writeln!(out, "  [{note}]");
                    }
                    // Non-witnessed rows still carry the authoritative
                    // MIR arm denominator, so a proxy percentage is
                    // always read against the arm count it failed to
                    // witness.
                    if m.evidence != crate::cov_fuzz_ext::ExtEvidenceKind::MirArmsWitnessed {
                        if let Some(arms) = m.mir_arms {
                            let _ =
                                writeln!(out, "  [MIR manifest denominator: {arms} branch arm(s)]");
                        }
                    }
                    if m.observed_pct() == Some(100) {
                        let _ = writeln!(
                            out,
                            "  [100% means every observed site was reached by sampled engaged inputs; it does not prove specification strength or correctness]"
                        );
                    }
                    for clause in &m.clauses {
                        match clause {
                            crate::cov_fuzz_ext::ExtClauseResult::Measured {
                                clause,
                                samples,
                                measurement,
                            } => {
                                let clause_pct = measurement
                                    .observed_pct()
                                    .map(|value| format!("{value}%"))
                                    .unwrap_or_else(|| "N/A".to_string());
                                let _ = writeln!(
                                    out,
                                    "  ensures[{clause}]: {clause_pct} from {samples} isolated sample(s) [{:?}]",
                                    measurement.evidence
                                );
                            }
                            crate::cov_fuzz_ext::ExtClauseResult::NoSamples { clause } => {
                                let _ = writeln!(out, "  ensures[{clause}]: no sampled engagement");
                            }
                            crate::cov_fuzz_ext::ExtClauseResult::Unlowerable {
                                clause,
                                reason,
                            } => {
                                let _ = writeln!(
                                    out,
                                    "  ensures[{clause}]: engagement indeterminate ({reason})"
                                );
                            }
                            crate::cov_fuzz_ext::ExtClauseResult::Unavailable {
                                clause,
                                samples,
                                reason,
                            } => {
                                let _ = writeln!(
                                    out,
                                    "  ensures[{clause}]: unavailable after {samples} sample(s): {reason}"
                                );
                            }
                        }
                    }
                    for probe in &m.probes {
                        if probe.checks == 0 {
                            continue;
                        }
                        if probe.violations == 0 {
                            let _ = writeln!(
                                out,
                                "  strengthening candidate (held {}/{}; not syntactically claimed): {}",
                                probe.checks, probe.checks, probe.suggestion
                            );
                        } else {
                            let _ = writeln!(
                                out,
                                "  strengthening probe rejected ({}/{} violations): {}",
                                probe.violations, probe.checks, probe.suggestion
                            );
                        }
                    }
                    if !m.unreached.is_empty() {
                        let _ = writeln!(out, "  unreached:");
                        for (file, line) in &m.unreached {
                            let _ = writeln!(out, "    {}:{}", file, line);
                        }
                    }
                }
                Some(crate::cov_fuzz_ext::ExtResult::Branchless { def_path, probes }) => {
                    external_branchless += 1;
                    let _ = writeln!(
                        out,
                        "{:<width$}  external `{}`: BRANCHLESS — 0 MIR branch arms, \
                         nothing to measure (N/A)",
                        target.fn_name,
                        ext.target_path,
                        width = max_name
                    );
                    let _ = writeln!(out, "  [MIR manifest def-path: `{def_path}`]");
                    for probe in probes {
                        if probe.checks == 0 {
                            continue;
                        }
                        if probe.violations == 0 {
                            let _ = writeln!(
                                out,
                                "  strengthening candidate (held {}/{}; not syntactically claimed): {}",
                                probe.checks, probe.checks, probe.suggestion
                            );
                        } else {
                            let _ = writeln!(
                                out,
                                "  strengthening probe rejected ({}/{} violations): {}",
                                probe.violations, probe.checks, probe.suggestion
                            );
                        }
                    }
                }
                Some(crate::cov_fuzz_ext::ExtResult::Unavailable(why)) => {
                    external_unavailable += 1;
                    let _ = writeln!(
                        out,
                        "{:<width$}  external target `{}` — not measured: {}",
                        target.fn_name,
                        ext.target_path,
                        why,
                        width = max_name
                    );
                }
                None => {
                    external_unavailable += 1;
                    let _ = writeln!(
                        out,
                        "{:<width$}  external target `{}` — not measured \
                         (orchestration did not run)",
                        target.fn_name,
                        ext.target_path,
                        width = max_name
                    );
                }
            }
            continue;
        }
        let Some(tr) = results.get(target.target_id) else {
            continue;
        };
        if target.branch_cap_hit {
            let _ = writeln!(
                out,
                "{:<width$}  PARTIAL: branch instrumentation cap reached; reported denominator is truncated",
                target.fn_name,
                width = max_name
            );
        }
        if tr.total == 0 {
            let _ = writeln!(
                out,
                "{:<width$}  (no branch sites — body is straight-line)",
                target.fn_name,
                width = max_name
            );
            for probe in &tr.stats.probes {
                if probe.checks == 0 {
                    continue;
                }
                if probe.violations == 0 {
                    let _ = writeln!(
                        out,
                        "  strengthening candidate (held {}/{}; not syntactically claimed): {}",
                        probe.checks, probe.checks, probe.suggestion
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "  strengthening probe rejected ({}/{} violations): {}",
                        probe.violations, probe.checks, probe.suggestion
                    );
                }
            }
            continue;
        }
        let threshold_note = match target.threshold {
            Some(t) => format!("  (threshold {}%)", t),
            None => String::new(),
        };
        let _ = writeln!(
            out,
            "{:<width$}  spec covers {}/{} implementation branch arms  ({}%){}  \
             [inputs reach {}/{}]",
            target.fn_name,
            tr.covered,
            tr.total,
            tr.covered_pct(),
            threshold_note,
            tr.reached,
            tr.total,
            width = max_name
        );
        let s = &tr.stats;
        let _ = writeln!(
            out,
            "  [{} executions: {} tested, {} skipped by requires, {} undecodable, {} panicked; corpus {}]",
            s.executions, s.tested, s.skipped, s.invalid, s.panicked, s.corpus
        );
        for probe in &s.probes {
            if probe.checks == 0 {
                continue;
            }
            if probe.violations == 0 {
                let _ = writeln!(
                    out,
                    "  strengthening candidate (held {}/{}; not syntactically claimed): {}",
                    probe.checks, probe.checks, probe.suggestion
                );
            } else {
                let _ = writeln!(
                    out,
                    "  strengthening probe rejected ({}/{} violations): {}",
                    probe.violations, probe.checks, probe.suggestion
                );
            }
        }
        if s.tested == 0 && s.skipped > 0 {
            let _ = writeln!(
                out,
                "  (inconclusive: every input was rejected by `requires` — the search \
                 never reached the body; narrow the generator or raise \
                 VERUS_SPEC_CHECK_COV_FUZZ_BUDGET)"
            );
        }
        if !tr.indeterminate.is_empty() {
            let _ = writeln!(
                out,
                "  indeterminate (reached, but clause engagement could not be evaluated):"
            );
            for b in &tr.indeterminate {
                let _ = writeln!(out, "    {}:{}  {}", target.file, b.line, b.description);
            }
        }
        if !tr.unspecified.is_empty() {
            let _ = writeln!(
                out,
                "  unspecified (reached, but no ensures clause engages on any \
                 input that gets there):"
            );
            for b in &tr.unspecified {
                let _ = writeln!(out, "    {}:{}  {}", target.file, b.line, b.description);
            }
        }
        if !tr.unreached.is_empty() {
            let _ = writeln!(out, "  unreached:");
            for b in &tr.unreached {
                let _ = writeln!(out, "    {}:{}  {}", target.file, b.line, b.description);
            }
        }
        branch_covered += tr.covered;
        branch_total += tr.total;
    }
    // Keep arm-witnessed, llvm branch-arm, and region-proxy evidence in
    // separate aggregates. They are different units and combining them
    // into one percentage produces a number with no defensible
    // interpretation.
    let mut witnessed_covered: u32 = 0;
    let mut witnessed_total: u32 = 0;
    for target in targets {
        if target.skip || target.external.is_none() {
            continue;
        }
        if let Some(crate::cov_fuzz_ext::ExtResult::Measured(m)) = ext_results.get(target.target_id)
        {
            match m.evidence {
                crate::cov_fuzz_ext::ExtEvidenceKind::MirArmsWitnessed => {
                    witnessed_covered += m.branches_hit;
                    witnessed_total += m.branches_total;
                }
                crate::cov_fuzz_ext::ExtEvidenceKind::BranchArms => {
                    branch_covered += m.branches_hit;
                    branch_total += m.branches_total;
                }
                crate::cov_fuzz_ext::ExtEvidenceKind::RegionsProxy
                | crate::cov_fuzz_ext::ExtEvidenceKind::LinesProxy => {
                    region_only_covered += m.regions_hit;
                    region_only_total += m.regions_total;
                }
            }
        }
    }

    let _ = writeln!(out);
    if witnessed_total > 0 {
        let pct = (witnessed_covered * 100) / witnessed_total;
        let _ = writeln!(
            out,
            "MIR arms witnessed:        {} / {}  ({}%)",
            witnessed_covered, witnessed_total, pct
        );
    }
    match (branch_covered * 100).checked_div(branch_total) {
        Some(pct) => {
            let _ = writeln!(
                out,
                "true branch-arm coverage:  {} / {}  ({}%)",
                branch_covered, branch_total, pct
            );
        }
        None if witnessed_total == 0 => {
            let _ = writeln!(
                out,
                "true branch-arm coverage:  not available (no branch-arm records)"
            );
        }
        None => {}
    }
    if region_only_total > 0 {
        let pct = (region_only_covered * 100) / region_only_total;
        let _ = writeln!(
            out,
            "region reachability proxy:   {} / {}  ({}%; reported separately)",
            region_only_covered, region_only_total, pct
        );
    }
    if external_branchless > 0 {
        let _ = writeln!(
            out,
            "external measurement status:  {} measured, {} branchless (N/A), {} unavailable",
            external_measured, external_branchless, external_unavailable
        );
    } else {
        let _ = writeln!(
            out,
            "external measurement status:  {} measured, {} unavailable",
            external_measured, external_unavailable
        );
    }
    if external_unavailable > 0 || targets.iter().any(|target| target.branch_cap_hit) {
        let _ = writeln!(
            out,
            "coverage completeness: INCOMPLETE — unavailable or partially instrumented targets are not counted as covered"
        );
    }
    if !skipped.is_empty() {
        let _ = writeln!(out, "skipped: {}", skipped.join(", "));
    }

    // Per-module disposition rollup — printed only when the report
    // spans several modules (the campaign-audit view; single-module
    // reports read fine row by row).
    let module_of = |target_id: &str| -> String {
        target_id
            .split("::cov_fuzz:")
            .next()
            .unwrap_or(target_id)
            .to_string()
    };
    #[derive(Default)]
    struct ModuleTally {
        local: u32,
        witnessed: u32,
        llvm_arms: u32,
        proxy: u32,
        branchless: u32,
        unavailable: u32,
        skipped: u32,
    }
    let mut modules: BTreeMap<String, ModuleTally> = BTreeMap::new();
    for target in targets {
        let tally = modules.entry(module_of(target.target_id)).or_default();
        if target.skip {
            tally.skipped += 1;
            continue;
        }
        if target.external.is_none() {
            tally.local += 1;
            continue;
        }
        match ext_results.get(target.target_id) {
            Some(crate::cov_fuzz_ext::ExtResult::Measured(m)) => match m.evidence {
                crate::cov_fuzz_ext::ExtEvidenceKind::MirArmsWitnessed => tally.witnessed += 1,
                crate::cov_fuzz_ext::ExtEvidenceKind::BranchArms => tally.llvm_arms += 1,
                crate::cov_fuzz_ext::ExtEvidenceKind::RegionsProxy
                | crate::cov_fuzz_ext::ExtEvidenceKind::LinesProxy => tally.proxy += 1,
            },
            Some(crate::cov_fuzz_ext::ExtResult::Branchless { .. }) => tally.branchless += 1,
            Some(crate::cov_fuzz_ext::ExtResult::Unavailable(_)) | None => tally.unavailable += 1,
        }
    }
    if modules.len() >= 2 {
        let name_width = modules
            .keys()
            .map(String::len)
            .max()
            .unwrap_or(6)
            .max("module".len());
        let _ = writeln!(out);
        let _ = writeln!(out, "per-module summary:");
        let _ = writeln!(
            out,
            "  {:<name_width$}  {:>5}  {:>9}  {:>9}  {:>5}  {:>10}  {:>11}  {:>7}",
            "module",
            "local",
            "witnessed",
            "llvm-arms",
            "proxy",
            "branchless",
            "unavailable",
            "skipped"
        );
        for (module, t) in &modules {
            let _ = writeln!(
                out,
                "  {:<name_width$}  {:>5}  {:>9}  {:>9}  {:>5}  {:>10}  {:>11}  {:>7}",
                module,
                t.local,
                t.witnessed,
                t.llvm_arms,
                t.proxy,
                t.branchless,
                t.unavailable,
                t.skipped
            );
        }
    }
    let _ = writeln!(out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The guided loop must find a "deep" bit that random byte buffers
    /// essentially never hit in one shot, by climbing intermediate
    /// feedback bits. Feedback: bit i requires the first i+1 bytes to
    /// each be >= 0xF0 (a threshold condition, the shape branch-hit
    /// feedback actually handles — exact-equality walls need value
    /// tracing and are documented as out of scope). Random one-shot
    /// probability of bit 3 is 16^-4 ≈ 1.5e-5; with greedy corpus
    /// evolution each level costs only a per-byte 1/16 splat.
    #[test]
    fn guided_loop_climbs_gradient() {
        const FALSE: AtomicBool = AtomicBool::new(false);
        static BITS: [AtomicBool; 4] = [FALSE; 4];
        // Reset for repeat runs in one process.
        for b in &BITS {
            b.store(false, Ordering::Relaxed);
        }
        let mut exec = |bytes: &[u8]| {
            for i in 0..4 {
                if bytes.len() > i && bytes[..=i].iter().all(|&x| x >= 0xF0) {
                    BITS[i].store(true, Ordering::Relaxed);
                } else {
                    break;
                }
            }
            ExecOutcome::Tested
        };
        let stats = coverage_guided_loop(&[&BITS[..]], &mut exec);
        assert!(stats.tested > 0);
        assert!(
            BITS[3].load(Ordering::Relaxed),
            "guided search failed to climb a 4-level gradient in {} execs",
            stats.executions
        );
    }

    /// Panics in the execution closure are contained and tallied.
    #[test]
    fn panics_are_caught_and_counted() {
        static HIT: [AtomicBool; 1] = [AtomicBool::new(false)];
        let mut exec = |bytes: &[u8]| -> ExecOutcome {
            if bytes.first().copied().unwrap_or(0) > 100 {
                panic!("boom");
            }
            HIT[0].store(true, Ordering::Relaxed);
            ExecOutcome::Tested
        };
        let stats = coverage_guided_loop(&[&HIT[..]], &mut exec);
        assert!(stats.panicked > 0, "expected some panicking executions");
        assert_eq!(
            stats.executions,
            stats.tested + stats.skipped + stats.invalid
        );
    }

    fn stub_run() -> CovFuzzRunStats {
        CovFuzzRunStats::default()
    }

    fn stub_recorder() -> CovExtRecording {
        CovExtRecording::default()
    }

    fn external_target(threshold: Option<u8>) -> VcheckCovFuzzTarget {
        static NO_HITS: [AtomicBool; 0] = [];
        VcheckCovFuzzTarget {
            target_id: "test::checked_add",
            fn_name: "__vcheck_assume_u32_checked_add",
            file: "src/lib.rs",
            branch_cap_hit: false,
            branches: &[],
            hits: &NO_HITS,
            covered: &NO_HITS,
            indeterminate: &NO_HITS,
            unlowerable_ensures: &[],
            run: stub_run,
            threshold,
            skip: false,
            external: Some(VcheckCovFuzzExternal {
                target_path: "u32::checked_add",
                generic_type_params: &[],
                compile_selector: "deadbeefdeadbeef",
                replay_test: "test::replay_checked_add",
                recorder: stub_recorder,
            }),
        }
    }

    /// External (assume_specification) targets render an annotated row,
    /// run no in-process search, and pass when informational — even
    /// when side-profile orchestration is unavailable.
    #[test]
    fn external_target_is_annotated_and_informational() {
        // Orchestration must not fire inside a unit test (it would
        // spawn a cargo build); the disable knob routes every external
        // target to `Unavailable`.
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_EXT", "0");
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1");
        let targets = [external_target(None)];
        // Must not panic (informational).
        run_cov_fuzz_report("/tmp", &targets);
        // Rendering: the row names the wrapped path and the reason.
        let mut ext = BTreeMap::new();
        ext.insert(
            "test::checked_add",
            crate::cov_fuzz_ext::ExtResult::Unavailable("disabled".to_string()),
        );
        let report = format_report(&[&targets[0]], &BTreeMap::new(), &[], &ext);
        assert!(
            report.contains("u32::checked_add"),
            "row missing path:\n{report}"
        );
        assert!(
            report.contains("not measured"),
            "row missing annotation:\n{report}"
        );
    }

    /// A threshold on an unmeasured external target must fail loudly —
    /// a requested gate must not vacuously pass.
    #[test]
    fn external_target_with_threshold_fails() {
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_EXT", "0");
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1");
        let targets = [external_target(Some(100))];
        let err = std::panic::catch_unwind(|| run_cov_fuzz_report("/tmp", &targets))
            .expect_err("threshold on unmeasured external target must panic");
        let msg = err.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(
            msg.contains("not measured"),
            "unexpected panic message: {msg}"
        );
    }

    /// Measured external targets render counts and gate on `gate_pct`.
    #[test]
    fn measured_external_target_renders_counts() {
        let targets = [external_target(None)];
        let mut ext = BTreeMap::new();
        ext.insert(
            "test::checked_add",
            crate::cov_fuzz_ext::ExtResult::Measured(crate::cov_fuzz_ext::ExtMeasurement {
                regions_total: 4,
                regions_hit: 3,
                branches_total: 2,
                branches_hit: 1,
                instantiations: 1,
                tier: "nightly, branches",
                evidence: crate::cov_fuzz_ext::ExtEvidenceKind::BranchArms,
                backend: crate::cov_fuzz_ext::ExtExtractionBackend::Export,
                line_only_reason: None,
                unreached: vec![("core/src/num/mod.rs".to_string(), 899)],
                arm_witness_note: None,
                mir_arms: None,
                clauses: Vec::new(),
                probes: Vec::new(),
            }),
        );
        let report = format_report(&[&targets[0]], &BTreeMap::new(), &[], &ext);
        assert!(
            report.contains("1/2 true LLVM branch arms"),
            "branch evidence missing:\n{report}"
        );
        assert!(
            report.contains("core/src/num/mod.rs:899"),
            "unreached missing:\n{report}"
        );
        assert!(
            report.contains("isolated side profile"),
            "isolation annotation missing:\n{report}"
        );
    }

    /// Branchless externals (MIR-manifest resolved) render as explicit
    /// N/A with their def-path evidence and count separately from both
    /// measured and unavailable rows.
    #[test]
    fn branchless_external_target_renders_as_na() {
        let targets = [external_target(None)];
        let mut ext = BTreeMap::new();
        ext.insert(
            "test::checked_add",
            crate::cov_fuzz_ext::ExtResult::Branchless {
                def_path: "core::clone::impls::<impl clone::Clone for i8>::clone".to_string(),
                probes: vec![CovFuzzProbeResult {
                    suggestion: "final(vec).len() == old(vec).len()",
                    checks: 64,
                    violations: 0,
                }],
            },
        );
        let report = format_report(&[&targets[0]], &BTreeMap::new(), &[], &ext);
        assert!(
            report.contains("BRANCHLESS") && report.contains("(N/A)"),
            "branchless row missing:\n{report}"
        );
        assert!(
            report.contains("<impl clone::Clone for i8>::clone"),
            "def-path evidence missing:\n{report}"
        );
        assert!(
            report.contains("strengthening candidate (held 64/64")
                && report.contains("final(vec).len() == old(vec).len()"),
            "branchless strengthening probe missing:\n{report}"
        );
        assert!(
            report.contains("0 measured, 1 branchless (N/A), 0 unavailable"),
            "branchless must count separately:\n{report}"
        );
        assert!(
            !report.contains("INCOMPLETE"),
            "branchless is answered, not incomplete:\n{report}"
        );

        let dump = json_dump("/tmp", &[&targets[0]], &BTreeMap::new(), &ext);
        assert_eq!(
            dump["targets"][0]["strengthening_probes"],
            serde_json::json!([{
                "suggestion": "final(vec).len() == old(vec).len()",
                "checks": 64,
                "violations": 0,
            }])
        );
    }

    /// Genome file round-trip: encode -> parse is identity, including
    /// empty genomes and the empty set.
    #[test]
    fn genome_encoding_round_trips() {
        for genomes in [
            vec![],
            vec![vec![]],
            vec![vec![1, 2, 3], vec![], vec![0xFF; 300]],
        ] {
            let encoded = encode_genomes(&genomes).expect("encode");
            let parsed = parse_genomes(&encoded).expect("parse");
            assert_eq!(parsed, genomes);
        }
        // Truncated input must not panic or mis-parse.
        let encoded = encode_genomes(&[vec![1, 2, 3]]).expect("encode");
        assert!(parse_genomes(&encoded[..encoded.len() - 1]).is_err());
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(parse_genomes(&trailing).is_err());
    }

    /// The record loop saves only ENGAGED genomes, honors the cap for
    /// bulk saves, and its engagement bit steers the search: an
    /// engagement gated behind a byte threshold is found and every
    /// saved genome satisfies it.
    #[test]
    fn record_loop_saves_only_engaged() {
        static ENGAGE: [AtomicBool; 1] = [AtomicBool::new(false)];
        ENGAGE[0].store(false, Ordering::Relaxed);
        let mut exec = |bytes: &[u8]| {
            let engaged = bytes.first().copied().unwrap_or(0) >= 0xC0;
            let mut clauses = ClauseMask::new(1);
            if engaged {
                ENGAGE[0].store(true, Ordering::Relaxed);
                clauses.set(0);
            }
            RecordOutcome::Tested { clauses }
        };
        let saved = covext_record_loop(&[&ENGAGE[..]], 1, &mut exec);
        assert!(
            !saved.samples.is_empty(),
            "engaged inputs exist in the domain"
        );
        for sample in &saved.samples {
            assert!(
                sample.genome.first().copied().unwrap_or(0) >= 0xC0,
                "non-engaged genome saved: {:?}",
                sample.genome
            );
            assert!(sample.engaged_clauses.contains(0));
        }
        assert!(
            saved.samples.len() <= covext_samples_per_clause_from_env(),
            "per-clause cap ignored: {} genomes",
            saved.samples.len()
        );
    }

    /// Panicking executions are never saved (a panicking genome would
    /// fail the replay test).
    #[test]
    fn record_loop_drops_panicking_genomes() {
        static NO_BITS: [AtomicBool; 0] = [];
        let mut exec = |bytes: &[u8]| -> RecordOutcome {
            if bytes.first().copied().unwrap_or(0) > 8 {
                panic!("external fn panicked");
            }
            let mut clauses = ClauseMask::new(1);
            clauses.set(0);
            RecordOutcome::Tested { clauses }
        };
        let saved = covext_record_loop(&[&NO_BITS[..]], 1, &mut exec);
        for sample in &saved.samples {
            assert!(
                sample.genome.first().copied().unwrap_or(0) <= 8,
                "panicking genome saved: {:?}",
                sample.genome
            );
        }
    }

    /// The contract loop must find a violation gated behind the same
    /// kind of feedback gradient the coverage loop climbs: the bug
    /// only fires when the first 3 bytes are each >= 0xF0 (one-shot
    /// random probability 16^-3 ≈ 2.4e-4 per byte-triple), with
    /// per-level guidance bits lighting the way.
    #[test]
    fn contract_loop_finds_gated_violation() {
        const FALSE: AtomicBool = AtomicBool::new(false);
        static BITS: [AtomicBool; 3] = [FALSE; 3];
        for b in &BITS {
            b.store(false, Ordering::Relaxed);
        }
        let mut exec = |bytes: &[u8]| {
            for i in 0..3 {
                if bytes.len() > i && bytes[..=i].iter().all(|&x| x >= 0xF0) {
                    BITS[i].store(true, Ordering::Relaxed);
                } else {
                    return ContractExec::Tested;
                }
            }
            ContractExec::Failed("deep clause")
        };
        match guided_contract_loop(&[&BITS[..]], &mut exec) {
            ContractVerdict::Failed {
                genome, failure, ..
            } => {
                assert_eq!(failure, "deep clause");
                // Shrink must keep the failure reproducible.
                assert!(
                    genome.len() >= 3 && genome[..3].iter().all(|&x| x >= 0xF0),
                    "shrunk genome no longer fails: {genome:?}"
                );
            }
            ContractVerdict::Passed(stats) => panic!(
                "guided contract search missed a 3-level-gated violation in {} execs",
                stats.executions
            ),
        }
    }

    /// The shrinker minimizes: a violation on `byte0 >= 0x10` must come
    /// back as a short genome with the first byte at the boundary.
    #[test]
    fn contract_loop_shrinks_counterexample() {
        static NO_BITS: [AtomicBool; 0] = [];
        let mut exec = |bytes: &[u8]| {
            if bytes.first().copied().unwrap_or(0) >= 0x10 {
                ContractExec::Failed("byte0 too big")
            } else {
                ContractExec::Tested
            }
        };
        match guided_contract_loop(&[&NO_BITS[..]], &mut exec) {
            ContractVerdict::Failed { genome, .. } => {
                assert_eq!(genome.len(), 1, "expected 1-byte genome, got {genome:?}");
                // Halving from any b >= 0x10 lands in 0x10..0x20 (the
                // last failing value before /2 crosses the boundary).
                assert!(
                    genome[0] >= 0x10 && genome[0] < 0x20,
                    "expected boundary-adjacent byte, got {:#04x}",
                    genome[0]
                );
            }
            ContractVerdict::Passed(_) => panic!("trivially-findable violation missed"),
        }
    }

    /// A panic in the body is a failure (not a tallied statistic like
    /// in the coverage loop), and the panic text survives into the
    /// verdict via the final re-run.
    #[test]
    fn contract_loop_treats_panic_as_failure() {
        static NO_BITS: [AtomicBool; 0] = [];
        let mut exec = |bytes: &[u8]| -> ContractExec {
            if bytes.first().copied().unwrap_or(0) > 4 {
                panic!("overflow in body");
            }
            ContractExec::Tested
        };
        match guided_contract_loop(&[&NO_BITS[..]], &mut exec) {
            ContractVerdict::Failed { failure, .. } => {
                assert!(
                    failure.contains("overflow in body"),
                    "panic text lost: {failure}"
                );
            }
            ContractVerdict::Passed(_) => panic!("panicking target reported as passing"),
        }
    }

    /// No violation -> Passed, with the full budget spent and sane
    /// tallies (mirrors the coverage loop's accounting).
    #[test]
    fn contract_loop_passes_clean_target() {
        static NO_BITS: [AtomicBool; 0] = [];
        let mut exec = |bytes: &[u8]| {
            if bytes.first().copied().unwrap_or(0) > 200 {
                ContractExec::Skipped
            } else {
                ContractExec::Tested
            }
        };
        match guided_contract_loop(&[&NO_BITS[..]], &mut exec) {
            ContractVerdict::Passed(stats) => {
                assert!(stats.tested > 0);
                assert!(stats.skipped > 0);
                assert_eq!(
                    stats.executions,
                    stats.tested + stats.skipped + stats.invalid
                );
            }
            ContractVerdict::Failed { failure, .. } => {
                panic!("clean target reported failing: {failure}")
            }
        }
    }

    /// The threshold gates SPEC-COVERED arms, not reached arms: a
    /// target whose arms are all reached but only partially covered
    /// fails a 100% threshold, and the report renders both numbers
    /// plus the unspecified listing.
    #[test]
    fn threshold_gates_covered_not_reached() {
        static HITS: [AtomicBool; 2] = [AtomicBool::new(true), AtomicBool::new(true)];
        static COVERED: [AtomicBool; 2] = [AtomicBool::new(true), AtomicBool::new(false)];
        static INDETERMINATE: [AtomicBool; 2] = [AtomicBool::new(false), AtomicBool::new(false)];
        static BRANCHES: [VcheckCovFuzzBranch; 2] = [
            VcheckCovFuzzBranch {
                idx: 0,
                line: 10,
                description: "if (then branch)",
            },
            VcheckCovFuzzBranch {
                idx: 1,
                line: 10,
                description: "if (else branch)",
            },
        ];
        let target = VcheckCovFuzzTarget {
            target_id: "test::half_specified",
            fn_name: "half_specified",
            file: "src/lib.rs",
            branch_cap_hit: false,
            branches: &BRANCHES,
            hits: &HITS,
            covered: &COVERED,
            indeterminate: &INDETERMINATE,
            unlowerable_ensures: &[],
            run: stub_run,
            threshold: Some(100),
            skip: false,
            external: None,
        };
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1");
        let err =
            std::panic::catch_unwind(|| run_cov_fuzz_report("/tmp", std::slice::from_ref(&target)))
                .expect_err("50% covered under threshold 100 must panic");
        let msg = err.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(
            msg.contains("spec covers 50%"),
            "unexpected panic message: {msg}"
        );
        // Rendering: covered and reached shown separately; the
        // reached-but-unengaged arm is listed as unspecified. Advisory
        // probes distinguish observed candidates from rejected hypotheses.
        let probes = vec![
            CovFuzzProbeResult {
                suggestion: "final(v).len() == old(v).len()",
                checks: 64,
                violations: 0,
            },
            CovFuzzProbeResult {
                suggestion: "final(ret.0).len() == mid",
                checks: 64,
                violations: 3,
            },
        ];
        let mut results = BTreeMap::new();
        results.insert(
            "test::half_specified",
            TargetResult {
                reached: 2,
                covered: 1,
                total: 2,
                unreached: vec![],
                indeterminate: vec![],
                unspecified: vec![&BRANCHES[1]],
                stats: CovFuzzRunStats {
                    probes,
                    ..CovFuzzRunStats::default()
                },
            },
        );
        let report = format_report(&[&target], &results, &[], &BTreeMap::new());
        assert!(
            report.contains("spec covers 1/2"),
            "covered missing:\n{report}"
        );
        assert!(
            report.contains("[inputs reach 2/2]"),
            "reached missing:\n{report}"
        );
        assert!(
            report.contains("strengthening candidate (held 64/64"),
            "accepted probe missing:\n{report}"
        );
        assert!(
            report.contains("final(v).len() == old(v).len()"),
            "accepted probe suggestion missing:\n{report}"
        );
        assert!(
            report.contains("strengthening probe rejected (3/64 violations)"),
            "rejected probe missing:\n{report}"
        );
        assert!(
            report.contains("final(ret.0).len() == mid"),
            "rejected probe suggestion missing:\n{report}"
        );
        assert!(
            report.contains("unspecified"),
            "unspecified listing missing:\n{report}"
        );
        assert!(
            report.contains("if (else branch)"),
            "arm description missing:\n{report}"
        );

        let dump = json_dump("/tmp", &[&target], &results, &BTreeMap::new());
        assert_eq!(
            dump["targets"][0]["strengthening_probes"],
            serde_json::json!([
                {
                    "suggestion": "final(v).len() == old(v).len()",
                    "checks": 64,
                    "violations": 0,
                },
                {
                    "suggestion": "final(ret.0).len() == mid",
                    "checks": 64,
                    "violations": 3,
                },
            ])
        );
    }

    /// Deterministic for a fixed seed: two runs produce identical stats.
    #[test]
    fn deterministic_for_fixed_seed() {
        let run = || {
            static B: [AtomicBool; 2] = [AtomicBool::new(false), AtomicBool::new(false)];
            B[0].store(false, Ordering::Relaxed);
            B[1].store(false, Ordering::Relaxed);
            let mut exec = |bytes: &[u8]| {
                if bytes.len() > 2 {
                    B[0].store(true, Ordering::Relaxed);
                }
                if bytes.first().copied().unwrap_or(0) == 0x7F {
                    B[1].store(true, Ordering::Relaxed);
                }
                ExecOutcome::Tested
            };
            coverage_guided_loop(&[&B[..]], &mut exec)
        };
        let a = run();
        let b = run();
        assert_eq!(a.tested, b.tested);
        assert_eq!(a.executions, b.executions);
    }
}

#[cfg(test)]
mod additional_tests {
    use super::*;

    fn empty_run() -> CovFuzzRunStats {
        CovFuzzRunStats::default()
    }

    #[test]
    fn clause_mask_supports_more_than_sixty_four_clauses() {
        let mut mask = ClauseMask::new(130);
        for clause in [0, 63, 64, 65, 129] {
            mask.set(clause);
        }
        for clause in 0..130 {
            assert_eq!(
                mask.contains(clause),
                [0, 63, 64, 65, 129].contains(&clause)
            );
        }
    }

    #[test]
    fn per_clause_recording_does_not_starve_later_clauses() {
        const FALSE: AtomicBool = AtomicBool::new(false);
        static ENGAGED: [AtomicBool; 3] = [FALSE; 3];
        for bit in &ENGAGED {
            bit.store(false, Ordering::Relaxed);
        }
        let mut exec = |bytes: &[u8]| {
            let value = bytes.first().copied().unwrap_or(0);
            let mut clauses = ClauseMask::new(3);
            let partition = if value < 128 { 0 } else { 1 };
            clauses.set(partition);
            clauses.set(2);
            ENGAGED[partition].store(true, Ordering::Relaxed);
            ENGAGED[2].store(true, Ordering::Relaxed);
            RecordOutcome::Tested { clauses }
        };
        let recording = covext_record_loop(&[&ENGAGED], 3, &mut exec);
        let replay_counts: Vec<usize> = (0..3)
            .map(|clause| {
                recording
                    .samples
                    .iter()
                    .filter(|sample| sample.engaged_clauses.contains(clause))
                    .take(covext_samples_per_clause_from_env())
                    .count()
            })
            .collect();
        assert!(
            replay_counts.iter().all(|count| *count > 0),
            "replay_counts={replay_counts:?}"
        );
        assert!(
            replay_counts
                .iter()
                .all(|count| *count <= covext_samples_per_clause_from_env()),
            "replay_counts={replay_counts:?}"
        );
        let unique: BTreeSet<&[u8]> = recording
            .samples
            .iter()
            .map(|sample| sample.genome.as_slice())
            .collect();
        assert_eq!(unique.len(), recording.samples.len());
        assert!(
            recording.samples.len() <= 3 * covext_samples_per_clause_from_env(),
            "retained {} unique genomes for three clause quotas",
            recording.samples.len()
        );
    }

    #[test]
    fn branch_cap_cannot_satisfy_a_threshold() {
        static HIT: [AtomicBool; 1] = [AtomicBool::new(true)];
        static INDETERMINATE: [AtomicBool; 1] = [AtomicBool::new(false)];
        static BRANCH: [VcheckCovFuzzBranch; 1] = [VcheckCovFuzzBranch {
            idx: 0,
            line: 1,
            description: "capped arm",
        }];
        let target = VcheckCovFuzzTarget {
            target_id: "test::capped",
            fn_name: "capped",
            file: "src/lib.rs",
            branch_cap_hit: true,
            branches: &BRANCH,
            hits: &HIT,
            covered: &HIT,
            indeterminate: &INDETERMINATE,
            unlowerable_ensures: &[],
            run: empty_run,
            threshold: Some(100),
            skip: false,
            external: None,
        };
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1");
        let failure =
            std::panic::catch_unwind(|| run_cov_fuzz_report("/tmp", std::slice::from_ref(&target)))
                .expect_err("truncated branch evidence must not satisfy a threshold");
        let message = failure
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default();
        assert!(message.contains("instrumentation hit its cap"), "{message}");
    }

    /// Seeding must never crowd out the mutation search: the seed list
    /// is capped at half the execution budget.
    #[test]
    fn boundary_seeds_respect_budget_cap() {
        assert!(boundary_seed_genomes(10).len() <= 5);
        assert!(boundary_seed_genomes(0).is_empty());
        // Full list is a few hundred seeds — well under the 4096 default.
        let full = boundary_seed_genomes(u64::MAX);
        assert!(full.len() < 2048, "seed list too large: {}", full.len());
    }

    /// The whole point of the boundary seeds: decoded through the REAL
    /// generator stack (the same `vcheck_gen` tuple + `ByteSliceDriver`
    /// path the emitted runners use), the seed set must produce the
    /// exact edge-value pairs where numeric specs break — the
    /// `(MIN, -1)` overflow pair, unsigned `(MAX, 1)` overflow, and the
    /// mixed-width `(iN::MIN, 1)` underflow of `checked_sub_unsigned`
    /// (the vstd i64 campaign's missed arms). This test pins the
    /// selector-byte addressing: if the generator bucket tables or the
    /// driver's byte consumption change, it fails and the seed tables
    /// must be re-derived.
    #[cfg(feature = "bolero")]
    #[test]
    fn boundary_seeds_decode_to_critical_pairs() {
        use bolero_generator::driver::ByteSliceDriver;
        use bolero_generator::ValueGenerator;

        let seeds = boundary_seed_genomes(u64::MAX);
        let decode_all = |check: &mut dyn FnMut(&[u8])| {
            for seed in &seeds {
                check(seed);
            }
        };

        let signed_pair = (crate::vcheck_gen::<i64>(), crate::vcheck_gen::<i64>());
        let mut min_neg1 = false;
        let mut neg1_min = false;
        decode_all(&mut |bytes| {
            let mut d = ByteSliceDriver::new(bytes, &Default::default());
            if let Some((x, y)) = ValueGenerator::generate(&signed_pair, &mut d) {
                min_neg1 |= x == i64::MIN && y == -1;
                neg1_min |= x == -1 && y == i64::MIN;
            }
        });
        assert!(min_neg1, "no seed decodes to (i64::MIN, -1)");
        assert!(neg1_min, "no seed decodes to (-1, i64::MIN)");

        let unsigned_pair = (crate::vcheck_gen::<u32>(), crate::vcheck_gen::<u32>());
        let mut max_one = false;
        let mut one_max = false;
        decode_all(&mut |bytes| {
            let mut d = ByteSliceDriver::new(bytes, &Default::default());
            if let Some((x, y)) = ValueGenerator::generate(&unsigned_pair, &mut d) {
                max_one |= x == u32::MAX && y == 1;
                one_max |= x == 1 && y == u32::MAX;
            }
        });
        assert!(max_one, "no seed decodes to (u32::MAX, 1)");
        assert!(one_max, "no seed decodes to (1, u32::MAX)");

        // Mixed widths: `i64::checked_sub_unsigned(i64, u64)` underflows
        // at (MIN, 1).
        let mixed_pair = (crate::vcheck_gen::<i64>(), crate::vcheck_gen::<u64>());
        let mut min_one = false;
        decode_all(&mut |bytes| {
            let mut d = ByteSliceDriver::new(bytes, &Default::default());
            if let Some((x, y)) = ValueGenerator::generate(&mixed_pair, &mut d) {
                min_one |= x == i64::MIN && y == 1;
            }
        });
        assert!(min_one, "no seed decodes to (i64::MIN, 1u64)");
    }

    /// End-to-end through the guided loop: a feedback bit that lights
    /// ONLY on the exact `(i64::MIN, -1)` overflow pair — which random
    /// byte search essentially never coordinates — must be found via
    /// the deterministic seeds.
    #[cfg(feature = "bolero")]
    #[test]
    fn guided_loop_finds_min_neg1_via_seeds() {
        use bolero_generator::driver::ByteSliceDriver;
        use bolero_generator::ValueGenerator;

        const FALSE: AtomicBool = AtomicBool::new(false);
        static HIT: [AtomicBool; 1] = [FALSE; 1];
        HIT[0].store(false, Ordering::Relaxed);

        let gen = (crate::vcheck_gen::<i64>(), crate::vcheck_gen::<i64>());
        let stats = coverage_guided_loop(&[&HIT], &mut |bytes| {
            let mut d = ByteSliceDriver::new(bytes, &Default::default());
            let Some((x, y)) = ValueGenerator::generate(&gen, &mut d) else {
                return ExecOutcome::Invalid;
            };
            if x == i64::MIN && y == -1 {
                HIT[0].store(true, Ordering::Relaxed);
            }
            ExecOutcome::Tested
        });
        assert!(
            HIT[0].load(Ordering::Relaxed),
            "guided loop never produced (i64::MIN, -1) in {} executions",
            stats.executions
        );
    }

    #[test]
    fn unlowerable_engagement_fails_threshold_closed() {
        static HIT: [AtomicBool; 1] = [AtomicBool::new(true)];
        static COVERED: [AtomicBool; 1] = [AtomicBool::new(false)];
        static INDETERMINATE: [AtomicBool; 1] = [AtomicBool::new(true)];
        static BRANCH: [VcheckCovFuzzBranch; 1] = [VcheckCovFuzzBranch {
            idx: 0,
            line: 7,
            description: "if (then branch)",
        }];
        static UNKNOWN: [VcheckCovFuzzUnlowerableClause; 1] = [VcheckCovFuzzUnlowerableClause {
            clause: 0,
            reason: "inline quantified antecedent has no runtime engagement lowering",
        }];
        fn no_run() -> CovFuzzRunStats {
            CovFuzzRunStats::default()
        }
        let target = VcheckCovFuzzTarget {
            target_id: "test::unknown",
            fn_name: "unknown",
            file: "src/lib.rs",
            branch_cap_hit: false,
            branches: &BRANCH,
            hits: &HIT,
            covered: &COVERED,
            indeterminate: &INDETERMINATE,
            unlowerable_ensures: &UNKNOWN,
            run: no_run,
            threshold: Some(0),
            skip: false,
            external: None,
        };
        std::env::set_var("VERUS_SPEC_CHECK_COV_FUZZ_QUIET", "1");
        let failure =
            std::panic::catch_unwind(|| run_cov_fuzz_report("/tmp", std::slice::from_ref(&target)))
                .expect_err("even a zero threshold must fail when engagement is unknown");
        let message = failure
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default();
        assert!(
            message.contains("spec engagement is indeterminate"),
            "{message}"
        );

        let mut results = BTreeMap::new();
        results.insert(
            "test::unknown",
            TargetResult {
                reached: 1,
                covered: 0,
                total: 1,
                unreached: vec![],
                indeterminate: vec![&BRANCH[0]],
                unspecified: vec![],
                stats: CovFuzzRunStats::default(),
            },
        );
        let report = format_report(&[&target], &results, &[], &BTreeMap::new());
        assert!(
            report.contains(
                "unknown ensures[0]: engagement indeterminate (inline quantified antecedent has no runtime engagement lowering)"
            ),
            "target-level unlowerable clause missing:\n{report}"
        );
        assert!(
            report
                .contains("indeterminate (reached, but clause engagement could not be evaluated):"),
            "indeterminate-arm section missing:\n{report}"
        );
        assert!(
            report.contains("if (then branch)"),
            "indeterminate arm description missing:\n{report}"
        );

        let dump = json_dump("/tmp", &[&target], &results, &BTreeMap::new());
        assert_eq!(dump["targets"][0]["arms_indeterminate"], 1);
        assert_eq!(
            dump["targets"][0]["unlowerable_ensures"],
            serde_json::json!([{
                "clause": 0,
                "reason": "inline quantified antecedent has no runtime engagement lowering",
            }])
        );
    }

    #[test]
    fn artifact_keys_use_registration_identity() {
        assert_ne!(
            covext_target_file_key("module_a::same_display"),
            covext_target_file_key("module_b::same_display")
        );
    }
}
