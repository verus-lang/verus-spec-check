//! Side-profile orchestration for EXTERNAL `#[vcheck_cov_fuzz]` targets
//! (`assume_specification` wrappers).
//!
//! An assume_specification target's implementation lives outside the
//! crate (a dependency crate, or std/core), where the source-level
//! instrumenter can't reach. Coverage for those targets comes from a
//! *side profile* instead:
//!
//!  1. Rebuild the crate's test binary with `-C instrument-coverage`
//!     into a dedicated scratch target dir (cached across runs; the
//!     RUSTFLAGS change must not thrash the primary target dir).
//!  2. Run ONLY the `__vcheck_covext_replay_*` tests from that binary:
//!     each replays the spec-ENGAGED input genomes its target's
//!     engagement-guided recorder saved in step 0 (run in THIS
//!     uninstrumented process — see `VcheckCovFuzzExternal::recorder`),
//!     collecting `.profraw` files that reflect exactly the inputs the
//!     spec speaks about.
//!  3. `llvm-profdata merge`, then `llvm-cov export` (JSON) filtered to
//!     the wrapped paths; match instantiations by demangled name and
//!     aggregate region/branch counts per target.
//!
//! Tiering: the user's default toolchain instruments every crate cargo
//! *compiles from source* — dependency crates work out of the box.
//! std/core are precompiled, so targets whose records don't appear in
//! the tier-1 profile escalate to a `-Z build-std` rebuild when a
//! nightly toolchain with `rust-src` is available (which also enables
//! true branch counts via `-Z coverage-options=branch`); otherwise the
//! target reports as unavailable with install instructions.
//!
//! Guards and knobs:
//!  - `VERUS_SPEC_CHECK_COV_FUZZ_EXT_INNER` — re-entrancy guard: the side
//!    build's binary contains this same report test, so orchestration
//!    is disabled inside it.
//!  - `VERUS_SPEC_CHECK_COV_FUZZ_EXT=0` — disable orchestration entirely
//!    (external rows report "disabled").
//!
//! Everything here degrades to an explanatory message rather than a
//! panic: the report test fails only when a `threshold` was set on a
//! target that couldn't be measured (a requested gate must not
//! vacuously pass).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

// libtest runs report tests in parallel threads inside one process. Each
// report launches Cargo, writes replay genomes, and creates/merges LLVM
// profiles under process-scoped scratch paths. Letting those report threads
// orchestrate simultaneously makes them share the same PID-keyed paths and
// race (deleted binaries, corrupt/missing profdata, and concurrent Cargo
// builds exhausting process resources). Cross-process runs already have
// distinct PIDs; this lock serializes the report threads within one process.
static EXTERNAL_MEASUREMENT_LOCK: Mutex<()> = Mutex::new(());

// An outer test binary is immutable for its lifetime, so every report in that
// process can reuse the same instrumented side-test binary for a given
// crate/tier/flag set. Profiles and genomes remain per report. Without this
// cache, dozens of report tests each invoke Cargo (and nightly build-std) just
// to rediscover an identical executable.
static SIDE_BINARY_CACHE: OnceLock<Mutex<BTreeMap<String, PathBuf>>> = OnceLock::new();

fn side_binary_cache() -> &'static Mutex<BTreeMap<String, PathBuf>> {
    SIDE_BINARY_CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

use crate::cov_fuzz::VcheckCovFuzzExternal;

/// Result of side-profile measurement for one external target.
pub(crate) enum ExtResult {
    Measured(ExtMeasurement),
    /// The MIR manifest resolved the target to a def with ZERO branch
    /// terminators in `optimized_mir`: there is nothing for branch
    /// coverage to measure. Explicit N/A — passes strict mode (unlike
    /// `Unavailable`), but can never satisfy a branch threshold.
    Branchless {
        /// The resolved compiler def-path, printed as evidence.
        def_path: String,
        /// Advisory strengthening observations remain meaningful even when
        /// the implementation has no branch denominator.
        probes: Vec<crate::cov_fuzz::CovFuzzProbeResult>,
    },
    /// Not measured; the string explains why / what to install.
    Unavailable(String),
}

/// Exact kind of coverage evidence. Proxy kinds are never accepted by a
/// branch threshold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExtEvidenceKind {
    /// Every MIR branch arm of the target (per the covdriver manifest)
    /// mapped to its own llvm-cov counter, and witnessing read those
    /// counters per arm. The authoritative arm denominator — covers
    /// `match`-based bodies llvm branch records never see.
    MirArmsWitnessed,
    /// llvm's own branch records (`if`/`&&`/`||` syntax only).
    BranchArms,
    RegionsProxy,
    LinesProxy,
}

/// Which llvm-cov extraction interface produced this measurement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExtExtractionBackend {
    Export,
    Show,
}

#[derive(Clone)]
pub(crate) enum ExtClauseResult {
    Measured {
        clause: usize,
        samples: usize,
        measurement: Box<ExtMeasurement>,
    },
    NoSamples {
        clause: usize,
    },
    Unlowerable {
        clause: usize,
        reason: &'static str,
    },
    Unavailable {
        clause: usize,
        samples: usize,
        reason: String,
    },
}

/// Coverage of one external function from one isolated replay profile.
#[derive(Clone)]
pub(crate) struct ExtMeasurement {
    pub regions_total: u32,
    pub regions_hit: u32,
    pub branches_total: u32,
    pub branches_hit: u32,
    pub instantiations: u32,
    pub tier: &'static str,
    pub evidence: ExtEvidenceKind,
    /// Whether structured JSON export or the text `show` fallback supplied
    /// the counters used by this row.
    pub backend: ExtExtractionBackend,
    /// Why only line/region reachability could be reported. Present only
    /// for proxy evidence; branch evidence and confirmed branchless targets
    /// leave this unset.
    pub line_only_reason: Option<String>,
    pub unreached: Vec<(String, u32)>,
    /// Why arm witnessing was NOT applied despite the manifest knowing
    /// this target's arms (an anchor mapped to no region, ...). Printed
    /// so a proxy row explains itself. `None` when witnessing succeeded
    /// or was never applicable.
    pub arm_witness_note: Option<String>,
    /// The MIR manifest's arm denominator for this target, when it
    /// resolved with branches — printed next to non-witnessed evidence
    /// so every row carries the authoritative arm count.
    pub mir_arms: Option<u64>,
    /// Per-ensures-clause isolated profiles. Empty on nested clause
    /// measurements and while extracting the aggregate profile.
    pub clauses: Vec<ExtClauseResult>,
    /// Advisory strengthening observations recorded by the outer harness.
    pub probes: Vec<crate::cov_fuzz::CovFuzzProbeResult>,
}

impl ExtMeasurement {
    pub fn observed_pct(&self) -> Option<u32> {
        let (hit, total) = match self.evidence {
            ExtEvidenceKind::MirArmsWitnessed | ExtEvidenceKind::BranchArms => {
                (self.branches_hit, self.branches_total)
            }
            ExtEvidenceKind::RegionsProxy | ExtEvidenceKind::LinesProxy => {
                (self.regions_hit, self.regions_total)
            }
        };
        (hit * 100).checked_div(total)
    }

    pub fn branch_pct(&self) -> Option<u32> {
        matches!(
            self.evidence,
            ExtEvidenceKind::MirArmsWitnessed | ExtEvidenceKind::BranchArms
        )
        .then(|| (self.branches_hit * 100).checked_div(self.branches_total))
        .flatten()
    }
}

/// Whether orchestration is disabled for this process (inner side-run,
/// explicit opt-out, or Miri).
fn orchestration_disabled() -> Option<String> {
    if std::env::var_os("VERUS_SPEC_CHECK_COV_FUZZ_EXT_INNER").is_some() {
        return Some("inner side-profile run".to_string());
    }
    if std::env::var("VERUS_SPEC_CHECK_COV_FUZZ_EXT")
        .map(|v| v == "0")
        .unwrap_or(false)
    {
        return Some("disabled via VERUS_SPEC_CHECK_COV_FUZZ_EXT=0".to_string());
    }
    None
}

struct RecordedTarget<'a> {
    target_id: &'static str,
    external: &'a VcheckCovFuzzExternal,
    recording: crate::cov_fuzz::CovExtRecording,
}

/// Whether `VERUS_SPEC_CHECK_COVEXT_STABLE_PROXY=1` asks for a stable-toolchain
/// region-proxy pass over every target BEFORE the nightly tiers (the
/// historical default). Off by default: the stable tier cannot produce
/// branch evidence, so running it first costs a full instrumented build
/// and one replay per target for measurements that are usually
/// superseded anyway. It remains the automatic fallback when no nightly
/// toolchain is available.
fn stable_proxy_requested() -> bool {
    match std::env::var("VERUS_SPEC_CHECK_COVEXT_STABLE_PROXY") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

/// Route a target directly to the `-Z build-std` tier when its wrapped
/// path can only live in `core`/`alloc`/`std` — primitives, slices/str,
/// std containers, or an explicit std crate root. The nightly
/// dependencies tier compiles only the crate's own dependency graph, so
/// probing it first for a std target wastes a full replay cycle per
/// target (the exact pattern the vstd audit showed: every std target
/// escalated through two tiers before build-std matched or failed).
///
/// Misclassification is safe in both directions: a std target classified
/// as a dependency escalates to build-std exactly as before, and a
/// dependency target classified as std still resolves in the build-std
/// profile (build-std instruments the dependency graph too) — it just
/// pays the more expensive tier.
fn target_is_std_origin(target_path: &str) -> bool {
    let p = target_path.trim();
    // Qualified-self forms: `<[T]>::first`, `<i8 as Clone>::clone`,
    // `<Vec<T,A> as core::ops::Deref>::deref`.
    let head = match p.strip_prefix('<') {
        Some(rest) => {
            let end = rest
                .find(" as ")
                .unwrap_or_else(|| rest.find('>').unwrap_or(rest.len()));
            rest[..end].trim()
        }
        None => p,
    };
    // Slices, arrays, tuples, references, raw pointers: core types.
    if head.starts_with('[')
        || head.starts_with('(')
        || head.starts_with('&')
        || head.starts_with('*')
    {
        return true;
    }
    let first = head.split("::").next().unwrap_or(head);
    let first = first.split('<').next().unwrap_or(first).trim();
    matches!(
        first,
        "core"
            | "std"
            | "alloc"
            | "bool"
            | "char"
            | "str"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
            | "Vec"
            | "VecDeque"
            | "String"
            | "Box"
            | "Rc"
            | "Arc"
            | "Option"
            | "Result"
            | "BTreeMap"
            | "BTreeSet"
            | "HashMap"
            | "HashSet"
            | "BinaryHeap"
            | "LinkedList"
            | "PhantomData"
            | "ManuallyDrop"
            | "MaybeUninit"
            | "Ordering"
            | "Bound"
            | "Range"
            | "RangeInclusive"
            | "RangeFrom"
            | "RangeTo"
            | "RangeToInclusive"
            | "RangeFull"
            | "NonZero"
            | "NonZeroU8"
            | "NonZeroU16"
            | "NonZeroU32"
            | "NonZeroU64"
            | "NonZeroU128"
            | "NonZeroUsize"
            | "NonZeroI8"
            | "NonZeroI16"
            | "NonZeroI32"
            | "NonZeroI64"
            | "NonZeroI128"
            | "NonZeroIsize"
    )
}

/// Measure every external target. Builds each instrumentation tier once
/// (lazily — a tier that no target routes to is never built), executing
/// one aggregate profile per target plus one isolated profile per
/// ensures clause.
///
/// Tier routing:
///  - std/core/alloc-origin targets go DIRECTLY to nightly build-std;
///  - dependency-crate targets try nightly dependency instrumentation
///    first and escalate to build-std only on no-match;
///  - the stable region proxy runs only when no nightly toolchain is
///    available (automatic fallback) or when explicitly requested via
///    `VERUS_SPEC_CHECK_COVEXT_STABLE_PROXY=1`.
pub(crate) fn measure_external_targets(
    crate_dir: &str,
    targets: &[(&'static str, &VcheckCovFuzzExternal)],
) -> BTreeMap<&'static str, ExtResult> {
    let _measurement_guard = EXTERNAL_MEASUREMENT_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    let mut out = BTreeMap::new();
    if let Some(why) = orchestration_disabled() {
        for (target_id, _) in targets {
            out.insert(*target_id, ExtResult::Unavailable(why.clone()));
        }
        return out;
    }

    let tools = match llvm_tools() {
        Ok(tools) => tools,
        Err(why) => {
            for (target_id, _) in targets {
                out.insert(*target_id, ExtResult::Unavailable(why.clone()));
            }
            return out;
        }
    };

    let mut recorded = Vec::new();
    let total = targets.len();
    for (position, (target_id, external)) in targets.iter().enumerate() {
        progress(&format!(
            "verus_spec_check cov_fuzz: recording engagement [{}/{total}] `{}`",
            position + 1,
            external.target_path
        ));
        let recording = (external.recorder)();
        if recording.samples.is_empty() {
            out.insert(
                *target_id,
                ExtResult::Unavailable(format!(
                    "no ensures clause engaged any sampled input of `{}`",
                    external.target_path
                )),
            );
        } else {
            recorded.push(RecordedTarget {
                target_id,
                external,
                recording,
            });
        }
    }
    if recorded.is_empty() {
        return out;
    }

    // Nightly toolchain probe up front: routing depends on it.
    let nightly_pair = nightly_toolchain_available()
        .and_then(|nightly| nightly.llvm_tools(&tools).map(|nt| (nightly, nt)));
    let (nightly, nightly_tools) = match nightly_pair {
        Ok(pair) => pair,
        Err(nightly_why) => {
            // No nightly: the stable region proxy is the only evidence
            // available. Same fallback as before, reached without first
            // paying for it when nightly exists.
            let stable = match prepare_side_binary(crate_dir, &tools, Tier::Stable, None) {
                Ok(side) => side,
                Err(why) => {
                    for target in &recorded {
                        out.insert(target.target_id, ExtResult::Unavailable(why.clone()));
                    }
                    return out;
                }
            };
            for target in &recorded {
                // No nightly toolchain ⇒ no MIR manifest ⇒ no arm anchors.
                match measure_recorded_target(crate_dir, &tools, &stable, target, None) {
                    Ok(Some(measurement)) => {
                        out.insert(target.target_id, ExtResult::Measured(measurement));
                    }
                    Ok(None) => {
                        out.insert(
                            target.target_id,
                            ExtResult::Unavailable(nightly_why.clone()),
                        );
                    }
                    Err(why) => {
                        out.insert(target.target_id, ExtResult::Unavailable(why));
                    }
                }
            }
            return out;
        }
    };

    // MIR-manifest resolutions for every target in this group, computed
    // ONCE up front: arm anchors feed [`witness_arms`] during
    // extraction, and the branchless / lost-records classification
    // reuses the same map after measurement. Needles are unioned across
    // the WHOLE registry so every report run in this binary shares one
    // cached manifest pass regardless of which module's report runs.
    let (resolutions, mir_err): (
        BTreeMap<usize, crate::cov_mir::MirResolution>,
        Option<String>,
    ) = {
        let mut needles: BTreeSet<String> = crate::cov_fuzz::registry_external_target_paths()
            .into_iter()
            .filter_map(crate::cov_mir::needle_of)
            .collect();
        for target in &recorded {
            if let Some(needle) = crate::cov_mir::needle_of(target.external.target_path) {
                needles.insert(needle);
            }
        }
        let mut nightly_cargo = |tool: &str| nightly.selector.command(tool);
        match crate::cov_mir::mir_entries(
            crate_dir,
            &tools.host,
            &nightly.rustc,
            &nightly.sysroot,
            &mut nightly_cargo,
            &needles,
        ) {
            Ok(entries) => (
                recorded
                    .iter()
                    .enumerate()
                    .map(|(index, target)| {
                        (
                            index,
                            crate::cov_mir::resolve(target.external.target_path, &entries),
                        )
                    })
                    .collect(),
                None,
            ),
            Err(why) => (BTreeMap::new(), Some(why)),
        }
    };
    // The full resolution travels into extraction: complete anchor sets
    // drive arm witnessing, incomplete ones still annotate the row with
    // the MIR arm denominator (and the reason witnessing was skipped).
    let arm_spans_for =
        |index: usize| -> Option<&crate::cov_mir::MirResolution> { resolutions.get(&index) };

    // Optional stable-proxy prelude (diagnostic; historical default).
    // Proxy measurements are kept only as fallbacks for targets whose
    // nightly tiers later fail to build.
    let mut stable_fallbacks: BTreeMap<usize, ExtMeasurement> = BTreeMap::new();
    if stable_proxy_requested() {
        if let Ok(stable) = prepare_side_binary(crate_dir, &tools, Tier::Stable, None) {
            for (index, target) in recorded.iter().enumerate() {
                match measure_recorded_target(
                    crate_dir,
                    &tools,
                    &stable,
                    target,
                    arm_spans_for(index),
                ) {
                    Ok(Some(measurement)) if measurement.branch_pct().is_some() => {
                        out.insert(target.target_id, ExtResult::Measured(measurement));
                    }
                    Ok(Some(measurement)) => {
                        stable_fallbacks.insert(index, measurement);
                    }
                    Ok(None) | Err(_) => {}
                }
            }
        }
    }

    // The MIR inventory is authoritative about whether a branch denominator
    // exists. Classify branchless targets before routing to LLVM tiers, even
    // when a stable line/region proxy happened to match; otherwise identity
    // implementations such as primitive Clone appear as misleading 0/N rows.
    // A manifest-free run cannot reach this point, so this never guesses.
    for (index, target) in recorded.iter().enumerate() {
        if let Some(crate::cov_mir::MirResolution::Branchless { def_path }) =
            resolutions.get(&index)
        {
            out.insert(
                target.target_id,
                ExtResult::Branchless {
                    def_path: def_path.clone(),
                    probes: target.recording.probes.clone(),
                },
            );
            stable_fallbacks.remove(&index);
        }
    }

    // Route: std-origin targets skip the dependency tier entirely.
    let mut dep_first: Vec<usize> = Vec::new();
    let mut build_std: Vec<usize> = Vec::new();
    for (index, target) in recorded.iter().enumerate() {
        if out.contains_key(target.target_id) {
            continue; // already final (stable BranchArms — never in practice)
        }
        if target_is_std_origin(target.external.target_path) {
            build_std.push(index);
        } else {
            dep_first.push(index);
        }
    }

    // Nightly dependency tier (branch instrumentation, no build-std).
    if !dep_first.is_empty() {
        match prepare_side_binary(
            crate_dir,
            &nightly_tools,
            Tier::NightlyDependencies,
            Some(&nightly),
        ) {
            Ok(side) => {
                let dep_total = dep_first.len();
                for (position, index) in dep_first.into_iter().enumerate() {
                    let target = &recorded[index];
                    progress(&format!(
                        "verus_spec_check cov_fuzz: measuring (dependency tier) \
                         [{}/{dep_total}] `{}`",
                        position + 1,
                        target.external.target_path
                    ));
                    match measure_recorded_target(
                        crate_dir,
                        &nightly_tools,
                        &side,
                        target,
                        arm_spans_for(index),
                    ) {
                        Ok(Some(measurement)) => {
                            out.insert(target.target_id, ExtResult::Measured(measurement));
                        }
                        Ok(None) => build_std.push(index),
                        Err(why) => {
                            // A failed replay invalidates this target; never
                            // accept a partial profile.
                            out.insert(target.target_id, ExtResult::Unavailable(why));
                        }
                    }
                }
            }
            Err(why) => {
                for index in dep_first {
                    let result = stable_fallbacks
                        .remove(&index)
                        .map(ExtResult::Measured)
                        .unwrap_or_else(|| ExtResult::Unavailable(why.clone()));
                    out.insert(recorded[index].target_id, result);
                }
            }
        }
    }
    if build_std.is_empty() {
        return out;
    }

    // Nightly build-std tier (std/core targets and dependency escalations).
    if let Err(why) = require_nightly_rust_src(&nightly) {
        for index in build_std {
            let result = stable_fallbacks
                .remove(&index)
                .map(ExtResult::Measured)
                .unwrap_or_else(|| ExtResult::Unavailable(why.clone()));
            out.insert(recorded[index].target_id, result);
        }
        return out;
    }
    let nightly_std = match prepare_side_binary(
        crate_dir,
        &nightly_tools,
        Tier::NightlyBuildStd,
        Some(&nightly),
    ) {
        Ok(side) => side,
        Err(why) => {
            for index in build_std {
                let result = stable_fallbacks
                    .remove(&index)
                    .map(ExtResult::Measured)
                    .unwrap_or_else(|| ExtResult::Unavailable(why.clone()));
                out.insert(recorded[index].target_id, result);
            }
            return out;
        }
    };

    let mut no_records: Vec<usize> = Vec::new();
    let std_total = build_std.len();
    // Rescue budget: each rescue compiles a selected side binary (cheap
    // after the first — build-std artifacts are shared; only the target
    // crate itself recompiles) and replays one target. Bounded so a
    // pathological module cannot rebuild indefinitely.
    let mut rescue_budget = rescue_limit();
    for (position, index) in build_std.into_iter().enumerate() {
        let target = &recorded[index];
        progress(&format!(
            "verus_spec_check cov_fuzz: measuring (build-std tier) [{}/{std_total}] `{}`",
            position + 1,
            target.external.target_path
        ));
        match measure_recorded_target(
            crate_dir,
            &nightly_tools,
            &nightly_std,
            target,
            arm_spans_for(index),
        ) {
            Ok(Some(measurement)) => {
                // Rescue pass: a Show-backend measurement that could not
                // witness its known MIR arms may succeed against a
                // SELECTED side binary whose small coverage map lets
                // `llvm-cov export` run (region-level witnessing).
                let measurement = if rescue_budget > 0 && rescue_could_improve(&measurement) {
                    rescue_budget -= 1;
                    progress(&format!(
                        "verus_spec_check cov_fuzz: rescue shard for `{}` (selected export retry)",
                        target.external.target_path
                    ));
                    match prepare_side_binary_selected(
                        crate_dir,
                        &nightly_tools,
                        Tier::NightlyBuildStd,
                        Some(&nightly),
                        Some(target.external.compile_selector),
                    )
                    .and_then(|shard| {
                        measure_recorded_target(
                            crate_dir,
                            &nightly_tools,
                            &shard,
                            target,
                            arm_spans_for(index),
                        )
                    }) {
                        Ok(Some(rescued))
                            if rescued.branch_pct().is_some()
                                && measurement.branch_pct().is_none() =>
                        {
                            rescued
                        }
                        Ok(Some(rescued))
                            if rescued.evidence == ExtEvidenceKind::MirArmsWitnessed
                                && measurement.evidence
                                    != ExtEvidenceKind::MirArmsWitnessed =>
                        {
                            rescued
                        }
                        // Rescue that does not improve evidence (or fails)
                        // keeps the original measurement — never worse.
                        _ => measurement,
                    }
                } else {
                    measurement
                };
                out.insert(target.target_id, ExtResult::Measured(measurement));
            }
            Ok(None) => {
                no_records.push(index);
                out.insert(
                    target.target_id,
                    ExtResult::Unavailable(format!(
                        "no coverage records matched `{}` in an isolated build-std profile",
                        target.external.target_path
                    )),
                );
            }
            Err(why) => {
                out.insert(target.target_id, ExtResult::Unavailable(why));
            }
        }
    }

    // llvm-cov found no function records for these targets. The MIR
    // manifest (pre-codegen def-paths, where inlining cannot have
    // erased the function — resolved up front) tells apart:
    //  - BRANCHLESS targets — nothing to measure, explicit N/A;
    //  - targets whose arms exist but whose records the LLVM tier lost —
    //    still fail-closed unavailable, now with the honest reason;
    //  - targets the manifest cannot resolve — fail-closed, precise.
    for index in no_records {
        let target = &recorded[index];
        let path = target.external.target_path;
        let result = if let Some(why) = &mir_err {
            ExtResult::Unavailable(format!(
                "no coverage records matched `{path}` in an isolated \
                 build-std profile (MIR manifest unavailable: {why})"
            ))
        } else {
            match resolutions.get(&index) {
                Some(crate::cov_mir::MirResolution::Branchless { def_path }) => {
                    ExtResult::Branchless {
                        def_path: def_path.clone(),
                        probes: target.recording.probes.clone(),
                    }
                }
                Some(crate::cov_mir::MirResolution::Branches { def_path, arms, .. }) => {
                    ExtResult::Unavailable(format!(
                        "no coverage records matched `{path}` in an isolated \
                         build-std profile, but the MIR manifest shows {arms} \
                         branch arm(s) at `{def_path}` — the LLVM tier lost \
                         the function records (inlining)"
                    ))
                }
                Some(crate::cov_mir::MirResolution::Ambiguous { candidates }) => {
                    ExtResult::Unavailable(format!(
                        "no coverage records matched `{path}` in an isolated \
                         build-std profile, and the MIR manifest match is \
                         ambiguous: {}",
                        candidates.join(", ")
                    ))
                }
                Some(crate::cov_mir::MirResolution::Unresolved) | None => {
                    ExtResult::Unavailable(format!(
                        "no coverage records matched `{path}` in an isolated \
                         build-std profile, and no def-path in the MIR \
                         manifest matches it"
                    ))
                }
            }
        };
        out.insert(target.target_id, result);
    }
    out
}

/// Maximum rescue-shard attempts per report run. Each attempt rebuilds
/// the target crate (build-std dependencies stay cached) and replays one
/// target's profiles. `VERUS_SPEC_CHECK_COVEXT_RESCUE=0` disables rescue.
fn rescue_limit() -> u32 {
    match std::env::var("VERUS_SPEC_CHECK_COVEXT_RESCUE") {
        Ok(v) if v == "0" => 0,
        Ok(v) => v.parse().unwrap_or(0),
        // LLVM 22.1.6 crashes even for selected rescue objects with an
        // empty profile, so rescue is opt-in until that upstream defect
        // is fixed. 
        Err(_) => 0,
    }
}

/// Whether a selected-export rescue could produce strictly better
/// evidence: the measurement came from the `show` fallback (export
/// crashed on the all-target coverage map), it is not already
/// arm-witnessed, and the MIR manifest knows a nonzero arm denominator
/// for the target (so export's region records have something to witness).
fn rescue_could_improve(m: &ExtMeasurement) -> bool {
    m.backend == ExtExtractionBackend::Show
        && m.evidence != ExtEvidenceKind::MirArmsWitnessed
        && m.mir_arms.is_some_and(|arms| arms > 0)
}

/// Remove one replay's isolated run directory (genomes, raw profiles,
/// merged profdata) once its evidence has been extracted. Replay dirs
/// are pure intermediates; keeping them accumulated gigabytes across a
/// repository audit (hundreds of `vcheck-run-*` dirs) for no evidentiary
/// value — the extracted `ExtMeasurement` is the record.
fn cleanup_replay_dir(profile: &Profile) {
    if matches!(
        std::env::var("VERUS_SPEC_CHECK_COVEXT_KEEP_PROFILES"),
        Ok(v) if !v.is_empty() && v != "0"
    ) {
        return;
    }
    if let Some(dir) = profile.profdata.parent() {
        let _ = std::fs::remove_dir_all(dir);
    }
}

fn measure_recorded_target(
    crate_dir: &str,
    tools: &LlvmTools,
    side: &SideBinary,
    target: &RecordedTarget<'_>,
    arm_spans: Option<&crate::cov_mir::MirResolution>,
) -> Result<Option<ExtMeasurement>, String> {
    let aggregate: Vec<Vec<u8>> = target
        .recording
        .samples
        .iter()
        .map(|sample| sample.genome.clone())
        .collect();
    let profile = profile_replay(
        crate_dir,
        tools,
        side,
        target.target_id,
        target.external.replay_test,
        "aggregate",
        &aggregate,
    )?;
    let extracted = extract_target(tools, &profile, target.external, arm_spans);
    cleanup_replay_dir(&profile);
    let Some(mut measurement) = extracted? else {
        return Ok(None);
    };
    measurement.probes = target.recording.probes.clone();

    for clause in 0..target.recording.clause_count {
        if let Some(unlowerable) = target
            .recording
            .unlowerable_clauses
            .iter()
            .find(|entry| entry.clause == clause)
        {
            measurement.clauses.push(ExtClauseResult::Unlowerable {
                clause,
                reason: unlowerable.reason,
            });
            continue;
        }
        let genomes: Vec<Vec<u8>> = target
            .recording
            .samples
            .iter()
            .filter(|sample| sample.engaged_clauses.contains(clause))
            // A sample may engage several clauses. Retaining it for a rarer
            // clause can therefore make it appear in more than one clause's
            // exact mask after another clause has filled. Enforce the quota
            // at replay selection without discarding that exact identity.
            .take(crate::cov_fuzz::covext_samples_per_clause_from_env())
            .map(|sample| sample.genome.clone())
            .collect();
        if genomes.is_empty() {
            measurement
                .clauses
                .push(ExtClauseResult::NoSamples { clause });
            continue;
        }
        // A clause engaged by EVERY retained sample replays the exact
        // aggregate set — its isolated profile is byte-identical to the
        // aggregate one, so reuse the aggregate measurement instead of
        // paying another subprocess replay + profile merge + llvm-cov
        // export. For single-clause targets (most of vstd) this halves
        // the external measurement cost; isolation is preserved because
        // the identical-input-set profile IS the isolated profile.
        if genomes.len() == aggregate.len() {
            let mut clause_measurement = measurement.clone();
            clause_measurement.clauses = Vec::new();
            measurement.clauses.push(ExtClauseResult::Measured {
                clause,
                samples: genomes.len(),
                measurement: Box::new(clause_measurement),
            });
            continue;
        }
        let label = format!("clause-{clause}");
        let clause_result = profile_replay(
            crate_dir,
            tools,
            side,
            target.target_id,
            target.external.replay_test,
            &label,
            &genomes,
        )
        .and_then(|profile| {
            let extracted = extract_target(tools, &profile, target.external, arm_spans);
            cleanup_replay_dir(&profile);
            extracted.and_then(|measurement| {
                measurement.ok_or_else(|| {
                    format!(
                        "no coverage records matched `{}` for clause {clause}",
                        target.external.target_path
                    )
                })
            })
        });
        match clause_result {
            Ok(clause_measurement) => measurement.clauses.push(ExtClauseResult::Measured {
                clause,
                samples: genomes.len(),
                measurement: Box::new(clause_measurement),
            }),
            Err(reason) => measurement.clauses.push(ExtClauseResult::Unavailable {
                clause,
                samples: genomes.len(),
                reason,
            }),
        }
    }
    Ok(Some(measurement))
}

// ---------------------------------------------------------------------------
// Toolchain probing
// ---------------------------------------------------------------------------

struct LlvmTools {
    profdata: PathBuf,
    cov: PathBuf,
    host: String,
}

/// `llvm-profdata` + `llvm-cov` from a toolchain sysroot's rustlib bin
/// (where rustup's `llvm-tools` component puts them), or `None` if the
/// component isn't installed there.
fn llvm_tools_in_sysroot(sysroot: &Path, host: &str) -> Option<(PathBuf, PathBuf)> {
    let bin = sysroot.join("lib/rustlib").join(host).join("bin");
    let profdata = bin.join("llvm-profdata");
    let cov = bin.join("llvm-cov");
    (profdata.is_file() && cov.is_file()).then_some((profdata, cov))
}

/// Tools for the STABLE tier: the active toolchain's own llvm-tools.
/// The .profraw format is version-locked to the LLVM that emitted it
/// ("raw profile format version = N; expected version = M" on
/// mismatch), so the tools MUST come from the same toolchain that
/// builds the instrumented binary — which for this tier is the active
/// one.
fn llvm_tools() -> Result<LlvmTools, String> {
    let sysroot = capture_ok("rustc", &["--print", "sysroot"])?;
    let sysroot = sysroot.trim();
    let host = rustc_host("rustc")?;
    if let Some((profdata, cov)) = llvm_tools_in_sysroot(Path::new(sysroot), &host) {
        return Ok(LlvmTools {
            profdata,
            cov,
            host,
        });
    }
    // PATH fallback: non-rustup toolchains (nixpkgs rustc, distro
    // packages) don't ship llvm-tools in the sysroot's rustlib bin —
    // the tools come from an LLVM package on PATH instead (the repo's
    // flake provides rustc's own LLVM, so the profraw format matches).
    // The sysroot location stays preferred when both exist: rustup's
    // component is exactly the toolchain's LLVM, while a PATH llvm-cov
    // could be anything.
    if let (Some(profdata), Some(cov)) = (which("llvm-profdata"), which("llvm-cov")) {
        return Ok(LlvmTools {
            profdata,
            cov,
            host,
        });
    }
    Err(
        "llvm-tools not found: neither in the active toolchain's sysroot \
         (`rustup component add llvm-tools`) nor as llvm-profdata/llvm-cov \
         on PATH (nix users: the repo flake's dev shell provides them). \
         External-target coverage measurement needs one of the two."
            .to_string(),
    )
}

/// Minimal PATH lookup (no external dep): first `dir/<name>` in `$PATH`
/// that exists and is a file.
fn which(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
}

fn rustc_host(rustc: &str) -> Result<String, String> {
    let out = capture_ok(rustc, &["-vV"])?;
    out.lines()
        .find_map(|l| l.strip_prefix("host: "))
        .map(|s| s.trim().to_string())
        .ok_or_else(|| "could not determine host triple from `rustc -vV`".to_string())
}

/// LLVM major version from `rustc -vV` output ("LLVM version: 20.1.6").
/// `None` when the line is missing or unparseable (be permissive: a
/// probe failure should not block measurement — an actual mismatch
/// still surfaces at merge time with the format-version hint).
fn llvm_major_from_vv(vv_output: &str) -> Option<u32> {
    let ver = vv_output
        .lines()
        .find_map(|l| l.trim().strip_prefix("LLVM version:"))?;
    ver.trim().split('.').next()?.parse().ok()
}

/// LLVM major version of an llvm tool binary, via `--version`
/// ("... LLVM version 20.1.6 ...").
fn llvm_major_of_tool(tool: &Path) -> Option<u32> {
    let out = Command::new(tool).arg("--version").output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let idx = text.find("LLVM version")?;
    let rest = text[idx + "LLVM version".len()..]
        .trim_start_matches(|c: char| c == ':' || c.is_whitespace());
    rest.split(|c: char| c == '.' || c.is_whitespace())
        .next()?
        .parse()
        .ok()
}

/// How to invoke a tool from the nightly toolchain. The `+nightly`
/// selector is a rustup-shim feature: it only works when PATH's
/// rustc/cargo ARE rustup's shims. In environments where another
/// toolchain shadows them (nix dev shells, distro packages), the
/// selector is passed through to the real compiler — which rejects it
/// as an input file — so the orchestrator falls back to invoking
/// rustup explicitly (`rustup run nightly <tool>`), which works
/// regardless of what's first on PATH.
#[derive(Clone, Copy, Debug)]
enum NightlySelector {
    /// PATH tools are rustup shims: `<tool> +nightly ...`.
    PlusArg,
    /// Explicit: `rustup run nightly <tool> ...`.
    RustupRun,
}

impl NightlySelector {
    /// A `Command` invoking `tool` from the nightly toolchain.
    fn command(self, tool: &str) -> Command {
        match self {
            NightlySelector::PlusArg => {
                let mut c = Command::new(tool);
                c.arg("+nightly");
                c
            }
            NightlySelector::RustupRun => {
                let mut c = Command::new("rustup");
                c.args(["run", "nightly", tool]);
                c
            }
        }
    }
}

/// A validated route to the nightly toolchain: how to spawn its cargo,
/// and the toolchain's own rustc binary. The rustc path is pinned via
/// the `RUSTC` env on the side build because cargo otherwise resolves
/// `rustc` from PATH — and in a shadowed-PATH environment (nix dev
/// shell) that is a stable non-rustup compiler which rejects the `-Z`
/// instrumentation flags.
struct NightlyToolchain {
    selector: NightlySelector,
    rustc: PathBuf,
    sysroot: PathBuf,
}

impl NightlyToolchain {
    /// Tools for the NIGHTLY tier. `.profraw` files are format-version-
    /// locked to the LLVM that emitted them, and nightly's LLVM is often
    /// newer than stable's — merging nightly-tier profraws with stable's
    /// llvm-profdata fails with "raw profile format version = N;
    /// expected version = M". Resolution order:
    ///
    ///  1. The nightly toolchain's OWN llvm-tools component (always
    ///     version-correct).
    ///  2. The active-tier tools, but only when nightly rustc's LLVM
    ///     major verifiably matches theirs (the common case when stable
    ///     and nightly track the same LLVM release).
    ///  3. Otherwise fail with the component-install hint.
    fn llvm_tools(&self, active: &LlvmTools) -> Result<LlvmTools, String> {
        if let Some((profdata, cov)) = llvm_tools_in_sysroot(&self.sysroot, &active.host) {
            return Ok(LlvmTools {
                profdata,
                cov,
                host: active.host.clone(),
            });
        }
        let nightly_major = self
            .selector
            .command("rustc")
            .arg("-vV")
            .output()
            .ok()
            .filter(|o| o.status.success())
            .and_then(|o| llvm_major_from_vv(&String::from_utf8_lossy(&o.stdout)));
        let tool_major = llvm_major_of_tool(&active.profdata);
        match (nightly_major, tool_major) {
            // Verified same LLVM major: the active tools can read
            // nightly's profraws.
            (Some(n), Some(t)) if n == t => Ok(LlvmTools {
                profdata: active.profdata.clone(),
                cov: active.cov.clone(),
                host: active.host.clone(),
            }),
            // Verified mismatch: the active tools would reject nightly's
            // profiles ("raw profile format version" error). The missing
            // piece is rustup's llvm-tools component on the nightly
            // toolchain — small, additive, and this orchestration is
            // already building on the user's behalf — so install it
            // rather than asking the user to. (Nightly is reachable via
            // rustup by construction: both probe selectors go through
            // it.) Falls back to an actionable error if the install
            // fails (offline, etc.).
            (Some(n), Some(t)) if n != t => {
                progress(&format!(
                    "verus_spec_check cov_fuzz: nightly rustc uses LLVM {n} but the \
                     available llvm-profdata is LLVM {t}; installing the \
                     version-matched `llvm-tools` component on the nightly \
                     toolchain ..."
                ));
                let install = Command::new("rustup")
                    .args(["component", "add", "llvm-tools", "--toolchain", "nightly"])
                    .output();
                let installed = matches!(&install, Ok(o) if o.status.success());
                if installed {
                    if let Some((profdata, cov)) =
                        llvm_tools_in_sysroot(&self.sysroot, &active.host)
                    {
                        return Ok(LlvmTools {
                            profdata,
                            cov,
                            host: active.host.clone(),
                        });
                    }
                }
                Err(format!(
                    "nightly rustc uses LLVM {n} but the available llvm-profdata is \
                     LLVM {t} — its profiles would be rejected (\"raw profile format \
                     version\" mismatch), and auto-installing the nightly llvm-tools \
                     component failed. Install manually: \
                     `rustup component add llvm-tools --toolchain nightly`"
                ))
            }
            // Probe inconclusive: proceed with the active tools; a real
            // mismatch still fails at merge time with the format-version
            // hint.
            _ => Ok(LlvmTools {
                profdata: active.profdata.clone(),
                cov: active.cov.clone(),
                host: active.host.clone(),
            }),
        }
    }
}

/// Probe for a usable nightly toolchain, returning the invocation style that
/// reached it plus its rustc binary. This tier does not require rust-src:
/// ordinary dependency crates can emit true branch records without rebuilding
/// the standard library.
fn nightly_toolchain_available() -> Result<NightlyToolchain, String> {
    const HOW: &str = "dependency branch coverage needs a nightly toolchain: \
                       `rustup toolchain install nightly`";
    let probe = |sel: NightlySelector| -> Option<String> {
        sel.command("rustc")
            .args(["--print", "sysroot"])
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    };
    let (selector, sysroot) = [NightlySelector::PlusArg, NightlySelector::RustupRun]
        .into_iter()
        .find_map(|sel| probe(sel).map(|s| (sel, s)))
        .ok_or_else(|| {
            format!(
                "no nightly toolchain found (neither `rustc +nightly` nor \
                 `rustup run nightly rustc` worked); {HOW}"
            )
        })?;
    let sysroot = PathBuf::from(&sysroot);
    let rustc = sysroot.join("bin/rustc");
    if !rustc.is_file() {
        return Err(format!(
            "nightly sysroot at {} has no bin/rustc; {HOW}",
            sysroot.display()
        ));
    }
    Ok(NightlyToolchain {
        selector,
        rustc,
        sysroot,
    })
}

/// The build-std escalation is reserved for std/core targets and additionally
/// requires nightly's rust-src component.
fn require_nightly_rust_src(nightly: &NightlyToolchain) -> Result<(), String> {
    let src = nightly.sysroot.join("lib/rustlib/src/rust/library");
    if src.exists() {
        Ok(())
    } else {
        Err("std/core targets need nightly rust-src: \
             `rustup component add rust-src --toolchain nightly`"
            .to_string())
    }
}

// ---------------------------------------------------------------------------
// Side build + profile collection
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Tier {
    /// Active toolchain, `-C instrument-coverage`: compatibility proxy.
    Stable,
    /// Nightly branch instrumentation for ordinary dependency crates.
    NightlyDependencies,
    /// Nightly branch instrumentation plus `-Z build-std` for std/core.
    NightlyBuildStd,
}

struct Profile {
    profdata: PathBuf,
    binary: PathBuf,
    tier: Tier,
}

struct SideBinary {
    binary: PathBuf,
    scratch: PathBuf,
    tier: Tier,
}

impl Tier {
    fn scratch_name(self) -> &'static str {
        match self {
            Tier::Stable => "verus-spec-check-covext",
            Tier::NightlyDependencies => "verus-spec-check-covext-nightly-deps",
            Tier::NightlyBuildStd => "verus-spec-check-covext-nightly-std",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Tier::Stable => "stable, regions",
            Tier::NightlyDependencies => "nightly dependencies, branches",
            Tier::NightlyBuildStd => "nightly build-std, branches",
        }
    }

    fn uses_nightly(self) -> bool {
        matches!(self, Tier::NightlyDependencies | Tier::NightlyBuildStd)
    }
}

/// Rebuild the crate's lib test binary instrumented, run the wrapper
/// harnesses, and merge the profile.
/// Root under which side-build scratch dirs and genome dirs live: the
/// user's target root (so one cache serves repeated runs). A relative
/// CARGO_TARGET_DIR is resolved against `crate_dir` — the same base the
/// child cargo (spawned with that cwd) resolves it against — so the
/// paths WE build (profdata, binary, genomes) and the paths cargo
/// writes agree even when this process's cwd differs.
fn scratch_base(crate_dir: &str) -> PathBuf {
    let base = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("target"));
    if base.is_absolute() {
        base
    } else {
        Path::new(crate_dir).join(base)
    }
}

/// Read a previously written side-binary manifest and return its
/// executable IF (a) `VERUS_SPEC_CHECK_COVEXT_REUSE_SIDE` explicitly opts into
/// cross-process reuse, (b) the manifest was written for exactly this
/// cache key (crate dir, tier, host, rustflags), and (c) the executable
/// still exists. The manifest cannot detect source edits since the
/// build — that is why reuse is opt-in rather than the default: a stale
/// side binary would silently measure old code, which violates the
/// fail-closed evidence rules. Without the env knob, cargo re-validates
/// (a no-op rebuild when nothing changed).
fn manifest_binary(manifest_path: &Path, cache_key: &str) -> Option<PathBuf> {
    let reuse = match std::env::var("VERUS_SPEC_CHECK_COVEXT_REUSE_SIDE") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    };
    if !reuse {
        return None;
    }
    let raw = std::fs::read_to_string(manifest_path).ok()?;
    let value: serde_json::Value = serde_json::from_str(&raw).ok()?;
    if value["cache_key"].as_str() != Some(cache_key) {
        return None;
    }
    let binary = PathBuf::from(value["binary"].as_str()?);
    binary.is_file().then_some(binary)
}

/// Record which executable the side build produced for `cache_key`, so a
/// later process can reuse it under `VERUS_SPEC_CHECK_COVEXT_REUSE_SIDE=1`.
/// Best-effort: a write failure only costs the next process a rebuild.
fn write_manifest(manifest_path: &Path, cache_key: &str, binary: &Path) {
    let value = serde_json::json!({
        "cache_key": cache_key,
        "binary": binary.to_string_lossy(),
    });
    let _ = std::fs::write(manifest_path, value.to_string());
}

fn prepare_side_binary(
    crate_dir: &str,
    tools: &LlvmTools,
    tier: Tier,
    nightly: Option<&NightlyToolchain>,
) -> Result<SideBinary, String> {
    prepare_side_binary_selected(crate_dir, tools, tier, nightly, None)
}

/// Like [`prepare_side_binary`], optionally restricted to a rescue selector
/// list (comma-separated compile selectors). A selected build compiles every
/// nonselected replay body to an early return, so its coverage map contains
/// only the selected targets' monomorphizations — small enough for
/// `llvm-cov export` where the all-target map SIGSEGVs LLVM.
fn prepare_side_binary_selected(
    crate_dir: &str,
    tools: &LlvmTools,
    tier: Tier,
    nightly: Option<&NightlyToolchain>,
    rescue_selectors: Option<&str>,
) -> Result<SideBinary, String> {
    // Scratch target dir: NOT the primary one (the RUSTFLAGS change
    // would thrash its fingerprints). Rescue shards get their own
    // selector-keyed scratch so they never overwrite the all-target
    // binary or its manifest.
    let scratch = match rescue_selectors {
        None => scratch_base(crate_dir).join(tier.scratch_name()),
        Some(selectors) => scratch_base(crate_dir).join(format!(
            "{}-rescue-{}",
            tier.scratch_name(),
            crate::cov_fuzz::covext_target_file_key(selectors)
        )),
    };
    std::fs::create_dir_all(&scratch).map_err(|e| format!("create {scratch:?}: {e}"))?;

    progress(&format!(
        "verus_spec_check cov_fuzz: preparing instrumented side profile ({}) under {} ...",
        tier.label(),
        scratch.display()
    ));

    // Note: setting RUSTFLAGS replaces any `[build] rustflags` from
    // .cargo/config.toml for this side build — acceptable for a
    // measurement build.
    //
    // CARGO_ENCODED_RUSTFLAGS takes PRECEDENCE over RUSTFLAGS when both
    // are set, so an inherited encoded value would silently drop the
    // instrumentation flag (yielding an uninstrumented profile and a
    // bogus "no records" escalation). Fold its contents into our flags
    // and remove it from the child env below.
    let mut rustflags = match std::env::var("CARGO_ENCODED_RUSTFLAGS") {
        Ok(encoded) => encoded.split('\x1f').collect::<Vec<_>>().join(" "),
        Err(_) => std::env::var("RUSTFLAGS").unwrap_or_default(),
    };
    rustflags.push_str(" -C instrument-coverage");
    if tier.uses_nightly() {
        rustflags.push_str(" -Z coverage-options=branch");
    }

    // Nightly side builds (dependency AND build-std tiers) route rustc
    // through covdriver in no-MIR-inline mode when available: every
    // caller crate then codegens its own instances of `#[inline]` fns,
    // so their coverage records exist instead of being erased by MIR
    // inlining — the root cause of the "no coverage records matched"
    // class. Degrades to the plain build (records lost as before,
    // MIR-manifest classification still applies) when covdriver cannot
    // be built.
    let covdriver = if tier.uses_nightly() {
        let nightly = nightly.expect("nightly tier requires a probed toolchain");
        let mut nightly_cargo = |tool: &str| nightly.selector.command(tool);
        match crate::cov_mir::covdriver_binary(
            &scratch_base(crate_dir).join("verus-spec-check-covext-mir"),
            &nightly.rustc,
            &mut nightly_cargo,
        ) {
            Ok(binary) => Some((binary, nightly.sysroot.clone())),
            Err(why) => {
                progress(&format!(
                    "verus_spec_check cov_fuzz: build-std side build runs WITHOUT \
                     no-MIR-inline (records of inlined std fns will be lost): {why}"
                ));
                None
            }
        }
    } else {
        None
    };

    let cache_key = format!(
        "{}|{}|{}|{}{}|rescue:{}",
        crate_dir,
        tier.scratch_name(),
        tools.host,
        rustflags.trim(),
        if covdriver.is_some() {
            "|no-mir-inline"
        } else {
            ""
        },
        rescue_selectors.unwrap_or("")
    );
    let manifest_path = scratch.join("side-binary.json");
    let cached_binary = side_binary_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(&cache_key)
        .filter(|path| path.is_file())
        .cloned();

    let binary = if let Some(binary) = cached_binary {
        progress(&format!(
            "verus_spec_check cov_fuzz: reusing instrumented side binary ({})",
            tier.label()
        ));
        binary
    } else if let Some(binary) = manifest_binary(&manifest_path, &cache_key) {
        // Cross-process reuse, explicitly opted into: the manifest
        // records which cache key the executable was built for, but NOT
        // whether sources changed since — that is the caller's promise.
        progress(&format!(
            "verus_spec_check cov_fuzz: reusing instrumented side binary from manifest ({}; \
             VERUS_SPEC_CHECK_COVEXT_REUSE_SIDE)",
            tier.label()
        ));
        side_binary_cache()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(cache_key, binary.clone());
        binary
    } else {
        progress(&format!(
            "verus_spec_check cov_fuzz: building instrumented side binary ({}) — \
             first run can take minutes",
            tier.label()
        ));
        // Every tier passes an explicit `--target <host>`: with an explicit
        // target, cargo applies RUSTFLAGS only to TARGET units, so host
        // artifacts (proc macros, build scripts) stay uninstrumented —
        // otherwise every rustc invocation that runs a proc macro would
        // drop stray `default.profraw` files into the crate dir.
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
        let mut cmd = match tier {
            Tier::Stable => {
                let mut c = Command::new(&cargo);
                c.args(["test", "--lib", "--no-run", "--message-format=json"]);
                c.args(["--target", &tools.host]);
                // Don't inherit an outer RUSTC pin (e.g. from a wrapping
                // build system); the active toolchain's default is what
                // this tier measures.
                c.env_remove("RUSTC");
                c
            }
            Tier::NightlyDependencies | Tier::NightlyBuildStd => {
                // Spawn nightly cargo via the selector style the probe
                // validated (rustup shim `+nightly`, or explicit `rustup
                // run nightly`) rather than the CARGO env binary (which is
                // pinned to the outer toolchain). Only the final std/core
                // escalation adds build-std; ordinary dependencies get true
                // branch records from a much smaller side build.
                let nightly = nightly.expect("nightly tier requires a probed toolchain");
                let mut c = nightly.selector.command("cargo");
                c.args(["test", "--lib", "--no-run", "--message-format=json"]);
                if tier == Tier::NightlyBuildStd {
                    c.args(["-Z", "build-std"]);
                }
                c.args(["--target", &tools.host]);
                c.env("RUSTC", &nightly.rustc);
                c
            }
        };
        if let Some((driver, sysroot)) = &covdriver {
            cmd.env("RUSTC_WRAPPER", driver)
                .env("VERUS_SPEC_CHECK_COVDRIVER_NO_MIR_INLINE", "1")
                .env("VERUS_SPEC_CHECK_COVDRIVER_SYSROOT", sysroot);
        }
        // Rescue selection travels as a compile-time env var read by the
        // generated replay tests through option_env!. Ensure an inherited
        // value never leaks into an all-target build.
        match rescue_selectors {
            Some(selectors) => {
                cmd.env("VERUS_SPEC_CHECK_COVEXT_RESCUE_SELECTORS", selectors);
            }
            None => {
                cmd.env_remove("VERUS_SPEC_CHECK_COVEXT_RESCUE_SELECTORS");
            }
        }
        let build_out = cmd
            .current_dir(crate_dir)
            .env("CARGO_TARGET_DIR", &scratch)
            .env("RUSTFLAGS", rustflags.trim())
            .env("VERUS_SPEC_CHECK_COV_FUZZ_EXT_INNER", "1")
            // See the RUSTFLAGS note above: the encoded variant would
            // override the flags we just assembled. RUSTC is handled
            // per-tier in the match above (Stable: un-inherit any outer
            // pin; Nightly: pin to the probed nightly toolchain's rustc).
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .output()
            .map_err(|e| format!("spawn cargo for side build: {e}"))?;
        if !build_out.status.success() {
            return Err(format!(
                "instrumented side build failed ({}, status {}) in `{}`:\n{}",
                tier.label(),
                build_out.status,
                crate_dir,
                side_build_diagnostics(&build_out.stdout, &build_out.stderr),
            ));
        }

        // The lib test executable, from cargo's JSON messages (robust
        // against target-dir layout differences, e.g. build-std's
        // `target/<triple>/` nesting).
        let stdout = String::from_utf8_lossy(&build_out.stdout);
        let mut binary: Option<PathBuf> = None;
        for line in stdout.lines() {
            let Ok(msg) = serde_json::from_str::<serde_json::Value>(line) else {
                continue;
            };
            if msg["reason"] != "compiler-artifact" {
                continue;
            }
            if msg["profile"]["test"] != true {
                continue;
            }
            let is_lib = msg["target"]["kind"]
                .as_array()
                .map(|ks| ks.iter().any(|k| k == "lib"))
                .unwrap_or(false);
            if !is_lib {
                continue;
            }
            if let Some(exe) = msg["executable"].as_str() {
                binary = Some(PathBuf::from(exe));
            }
        }
        let binary = binary.ok_or_else(|| {
            "side build produced no lib test executable (crate has no lib target?)".to_string()
        })?;
        write_manifest(&manifest_path, &cache_key, &binary);
        side_binary_cache()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(cache_key, binary.clone());
        binary
    };

    Ok(SideBinary {
        binary,
        scratch,
        tier,
    })
}

fn profile_replay(
    crate_dir: &str,
    tools: &LlvmTools,
    side: &SideBinary,
    target_id: &str,
    replay_test: &str,
    label: &str,
    genomes: &[Vec<u8>],
) -> Result<Profile, String> {
    if replay_test.is_empty() {
        return Err(format!("target `{target_id}` has no replay test identity"));
    }
    let run_identity = format!("{target_id}:{label}");
    let run_key = crate::cov_fuzz::covext_target_file_key(&run_identity);
    let run_dir = side
        .scratch
        .join(format!("vcheck-run-{}-{run_key}", std::process::id()));
    let result = profile_replay_in(
        crate_dir,
        tools,
        side,
        target_id,
        replay_test,
        genomes,
        &run_dir,
    );
    if result.is_err() {
        // A failed replay leaves no reusable evidence (the measurement is
        // invalidated fail-closed); drop the scratch dir instead of
        // leaking partial genomes/profiles onto disk.
        let _ = std::fs::remove_dir_all(&run_dir);
    }
    result
}

fn profile_replay_in(
    crate_dir: &str,
    tools: &LlvmTools,
    side: &SideBinary,
    target_id: &str,
    replay_test: &str,
    genomes: &[Vec<u8>],
    run_dir: &Path,
) -> Result<Profile, String> {
    // `module_path!()` includes the crate name, while libtest's displayed and
    // `--exact`-matchable test name starts at the first module. Strip exactly
    // that leading crate component; the completion marker still proves that
    // the selected replay body actually ran.
    let libtest_name = replay_test
        .split_once("::")
        .map(|(_, name)| name)
        .unwrap_or(replay_test);
    let _ = std::fs::remove_dir_all(run_dir);
    let genome_dir = run_dir.join("genomes");
    let profile_dir = run_dir.join("profiles");
    std::fs::create_dir_all(&genome_dir)
        .map_err(|e| format!("create isolated genome dir {genome_dir:?}: {e}"))?;
    std::fs::create_dir_all(&profile_dir)
        .map_err(|e| format!("create isolated profile dir {profile_dir:?}: {e}"))?;

    let genome_path = genome_dir.join(format!(
        "{}.genomes",
        crate::cov_fuzz::covext_target_file_key(target_id)
    ));
    let encoded = crate::cov_fuzz::encode_genomes(genomes)?;
    std::fs::write(&genome_path, encoded)
        .map_err(|e| format!("write isolated replay genomes {genome_path:?}: {e}"))?;
    let completion = run_dir.join("replay-complete");

    let run_out = Command::new(&side.binary)
        .arg(libtest_name)
        .arg("--exact")
        .current_dir(crate_dir)
        .env("LLVM_PROFILE_FILE", profile_dir.join("vcheck-%m-%p.profraw"))
        .env("VERUS_SPEC_CHECK_COVEXT_GENOME_DIR", &genome_dir)
        .env("VERUS_SPEC_CHECK_COVEXT_TARGET_ID", target_id)
        .env("VERUS_SPEC_CHECK_COVEXT_COMPLETION_FILE", &completion)
        .env("VERUS_SPEC_CHECK_COV_FUZZ_EXT_INNER", "1")
        .output()
        .map_err(|e| format!("run exact replay `{replay_test}`: {e}"))?;
    if !run_out.status.success() {
        let stderr = String::from_utf8_lossy(&run_out.stderr);
        let stdout = String::from_utf8_lossy(&run_out.stdout);
        return Err(format!(
            "isolated replay `{replay_test}` failed ({}):\n{}\n{}",
            run_out.status,
            tail(&stdout, 8),
            tail(&stderr, 12)
        ));
    }
    let completed = std::fs::read_to_string(&completion)
        .map_err(|e| format!("exact replay `{replay_test}` produced no completion marker: {e}"))?;
    if completed != target_id {
        return Err(format!(
            "exact replay completion mismatch: expected `{target_id}`, got `{completed}`"
        ));
    }

    let mut raws: Vec<PathBuf> = std::fs::read_dir(&profile_dir)
        .map_err(|e| format!("read isolated profile dir {profile_dir:?}: {e}"))?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .map(|ext| ext == "profraw")
                .unwrap_or(false)
        })
        .collect();
    raws.sort();
    if raws.is_empty() {
        return Err(format!(
            "isolated replay `{replay_test}` produced no .profraw files"
        ));
    }
    let profdata = run_dir.join("merged.profdata");
    let mut merge = Command::new(&tools.profdata);
    merge.args(["merge", "-sparse", "-o"]).arg(&profdata);
    for raw in &raws {
        merge.arg(raw);
    }
    let merge_out = merge
        .output()
        .map_err(|e| format!("spawn llvm-profdata for `{replay_test}`: {e}"))?;
    if !merge_out.status.success() {
        let stderr = String::from_utf8_lossy(&merge_out.stderr);
        return Err(format!(
            "llvm-profdata merge failed for isolated replay `{replay_test}`:\n{}",
            tail(&stderr, 12)
        ));
    }

    Ok(Profile {
        profdata,
        binary: side.binary.clone(),
        tier: side.tier,
    })
}

// ---------------------------------------------------------------------------
// Extraction: llvm-cov export -> per-target aggregation
// ---------------------------------------------------------------------------

/// Whether two source-file spellings name the same file, allowing one
/// to be a PATH-BOUNDARY suffix of the other (the manifest's diagnostic
/// strings and llvm-cov's filenames qualify paths differently).
/// `.../core/src/option.rs` ↔ `option.rs` agrees; `my_option.rs` does not.
fn files_agree(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    let suffix_of = |long: &str, short: &str| {
        long.len() > short.len()
            && long.ends_with(short)
            && matches!(long.as_bytes()[long.len() - short.len() - 1], b'/' | b'\\')
    };
    suffix_of(a, b) || suffix_of(b, a)
}

/// Witness each MIR branch arm through llvm-cov REGION counters: an
/// arm's anchor (its target block's start position, from the covdriver
/// manifest) is mapped to the SMALLEST code region containing it, and
/// the arm is witnessed iff that region's counter fired in any matched
/// instantiation. This is what makes `match`-based bodies
/// branch-accessible — llvm emits no "branches" records for them, but
/// every arm body is its own counted region.
///
/// Fail-closed: an anchor that maps to NO region aborts witnessing for
/// the whole target (the caller keeps proxy evidence and prints the
/// reason) — partial arm evidence is never presented as complete.
fn witness_arms(
    arm_spans: &[crate::cov_mir::MirArmSpan],
    region_hits: &BTreeMap<(String, u32, u32, u32, u32), bool>,
) -> Result<Vec<bool>, String> {
    let mut witnessed = Vec::with_capacity(arm_spans.len());
    for (index, arm) in arm_spans.iter().enumerate() {
        // Smallest containing region: fewest spanned lines, then
        // narrowest columns (single-line regions only — a multi-line
        // region's column span is not meaningful to compare).
        let mut best: Option<((u32, u32), bool)> = None;
        for ((file, l1, c1, l2, c2), hit) in region_hits {
            if !files_agree(file, &arm.file) {
                continue;
            }
            let after_start = (*l1, *c1) <= (arm.line, arm.col);
            let before_end = (arm.line, arm.col) <= (*l2, *c2);
            if !(after_start && before_end) {
                continue;
            }
            let size = (l2 - l1, if l2 == l1 { c2 - c1 } else { u32::MAX });
            if best.map(|(b, _)| size < b).unwrap_or(true) {
                best = Some((size, *hit));
            }
        }
        match best {
            Some((_, hit)) => witnessed.push(hit),
            None => {
                return Err(format!(
                    "arm {index} anchor {}:{}:{} maps to no llvm-cov region",
                    arm.file, arm.line, arm.col
                ));
            }
        }
    }
    Ok(witnessed)
}

/// Conservative arm witnessing for the `llvm-cov show` fallback. Region
/// display lines expose a start column (`^COUNT`) but no end span. Map each
/// MIR arm to the nearest region start at or before its anchor column on the
/// same line, requiring every arm to receive a DISTINCT counter. If no
/// sub-line marker exists, a whole-line counter is accepted only when that
/// source line belongs to exactly one arm. Any ambiguity fails closed.
fn witness_arms_by_show_counters(
    arm_spans: &[crate::cov_mir::MirArmSpan],
    line_hits: &BTreeMap<u32, bool>,
    region_start_hits: &BTreeMap<(u32, u32), bool>,
) -> Result<Vec<bool>, String> {
    let mut source_file: Option<&str> = None;
    let mut arm_lines: BTreeMap<u32, usize> = BTreeMap::new();
    for arm in arm_spans {
        *arm_lines.entry(arm.line).or_insert(0) += 1;
    }
    let mut used: BTreeSet<(u32, u32)> = BTreeSet::new();
    let mut witnessed = Vec::with_capacity(arm_spans.len());
    for (index, arm) in arm_spans.iter().enumerate() {
        if let Some(file) = source_file {
            if !files_agree(file, &arm.file) {
                return Err(format!(
                    "arm {index} comes from a different source file: {} vs {file}",
                    arm.file
                ));
            }
        } else {
            source_file = Some(&arm.file);
        }

        // Greatest displayed region-start column not after the MIR anchor.
        let region = region_start_hits
            .range((arm.line, 0)..=(arm.line, arm.col))
            .next_back()
            .map(|(key, hit)| (*key, *hit));
        let (key, hit) = if let Some(region) = region {
            region
        } else if arm_lines.get(&arm.line) == Some(&1) {
            let Some(hit) = line_hits.get(&arm.line) else {
                return Err(format!(
                    "arm {index} anchor {}:{}:{} has no coverage counter",
                    arm.file, arm.line, arm.col
                ));
            };
            // Column zero denotes the whole-line counter namespace.
            ((arm.line, 0), *hit)
        } else {
            return Err(format!(
                "arm {index} shares source line {} and has no distinct sub-line region counter",
                arm.line
            ));
        };
        if !used.insert(key) {
            return Err(format!(
                "arm {index} maps to the same show counter at {}:{} as another arm",
                key.0, key.1
            ));
        }
        witnessed.push(hit);
    }
    Ok(witnessed)
}

/// Extract one target's coverage from the profile. `Ok(None)` means no
/// function records matched (candidate for tier escalation).
/// `resolution`, when present, carries the target's MIR resolution:
/// complete arm-anchor sets drive [`witness_arms`] evidence; anything
/// less still annotates the measurement with the MIR arm denominator.
fn extract_target(
    tools: &LlvmTools,
    profile: &Profile,
    ext: &VcheckCovFuzzExternal,
    resolution: Option<&crate::cov_mir::MirResolution>,
) -> Result<Option<ExtMeasurement>, String> {
    let matcher =
        TargetMatcher::new_with_generic_type_params(ext.target_path, ext.generic_type_params);
    // Ask llvm-cov to pre-filter by the last path segment (regex over
    // MANGLED names — v0 manglings embed the plain fn name, so a
    // substring regex keeps the export small); precise matching happens
    // on the demangled names below.
    //
    // `--num-threads=1`: llvm-cov's parallel per-file summary
    // computation has crashed (SIGSEGV in `getInstantiationGroups`
    // under its thread pool) on larger binaries; single-threading it
    // costs little on a filtered export. The crash is FLAKY (the same
    // command on the same inputs succeeds on retry), so a failed
    // filtered export is retried and then falls back to an UNFILTERED
    // export (a different llvm-cov code path; bigger output, which the
    // demangled-name matching below filters anyway). Measurement
    // tooling flake shouldn't sink the report.
    let run_export = |name_regex: Option<String>| {
        let mut c = Command::new(&tools.cov);
        c.args(["export", "--num-threads=1", "--instr-profile"])
            .arg(&profile.profdata)
            .arg("--object")
            .arg(&profile.binary);
        if let Some(re) = name_regex {
            c.arg(format!("--name-regex={re}"));
        }
        c.output()
            .map_err(|e| format!("spawn llvm-cov export: {e}"))
    };
    let describe_failure = |label: &str, output: &std::process::Output| {
        format!("{label} exited {}", output.status)
    };
    let filter = Some(matcher.mangled_name_regex(&profile.binary));
    let mut failures = Vec::new();
    let mut export = run_export(filter.clone())?;
    if !export.status.success() {
        failures.push(describe_failure("filtered export", &export));
        export = run_export(filter)?;
    }
    if !export.status.success() {
        failures.push(describe_failure("filtered export retry", &export));
        export = run_export(None)?;
    }
    if !export.status.success() {
        failures.push(describe_failure("unfiltered export", &export));
        // `llvm-cov export`'s per-file summary computation SIGSEGVs on
        // some build-std coverage data (deterministically — observed on
        // the nightly-tier profile of a vstd-sized binary, crash in
        // `getInstantiationGroups` under its thread pool, LLVM bug).
        // `llvm-cov show` renders the same data fine, so fall back to
        // text extraction. The fallback retains the MIR resolution and
        // can witness only arms on distinct instrumented source lines.
        return extract_target_via_show(
            tools,
            profile,
            &matcher,
            resolution,
            failures.join("; "),
        );
    }
    let json: serde_json::Value = serde_json::from_slice(&export.stdout)
        .map_err(|e| format!("parse llvm-cov export JSON: {e}"))?;

    let functions = json["data"][0]["functions"]
        .as_array()
        .cloned()
        .unwrap_or_default();

    // Aggregate across instantiations, deduping regions/branches by
    // source span so N instantiations don't inflate the denominator.
    // A span counts as hit if ANY instantiation executed it.
    let mut region_hits: BTreeMap<(String, u32, u32, u32, u32), bool> = BTreeMap::new();
    let mut branch_arm_hits: BTreeMap<(String, u32, u32, u32, u32, u8), bool> = BTreeMap::new();
    let mut candidate_source_files: BTreeSet<String> = BTreeSet::new();
    let mut instantiations = 0u32;

    for f in &functions {
        let Some(mangled) = f["name"].as_str() else {
            continue;
        };
        let demangled = format!("{:#}", rustc_demangle::demangle(mangled));
        if !matcher.matches(&demangled) {
            continue;
        }
        instantiations += 1;
        let filenames: Vec<String> = f["filenames"]
            .as_array()
            .map(|a| {
                a.iter()
                    .map(|v| v.as_str().unwrap_or("").to_string())
                    .collect()
            })
            .unwrap_or_default();
        if let Some(source) = filenames.iter().find(|source| !source.is_empty()) {
            candidate_source_files.insert(source.clone());
        }
        let file_of = |id: u64| -> String {
            filenames
                .get(id as usize)
                .cloned()
                .unwrap_or_else(|| "?".to_string())
        };
        // Region record: [l1, c1, l2, c2, count, fileID, expandedFileID, kind]
        // kind 0 = code region (the only kind that counts).
        if let Some(regions) = f["regions"].as_array() {
            for r in regions {
                let Some(r) = r.as_array() else { continue };
                if r.len() < 8 {
                    continue;
                }
                let kind = r[7].as_u64().unwrap_or(0);
                if kind != 0 {
                    continue;
                }
                let key = (
                    file_of(r[5].as_u64().unwrap_or(0)),
                    r[0].as_u64().unwrap_or(0) as u32,
                    r[1].as_u64().unwrap_or(0) as u32,
                    r[2].as_u64().unwrap_or(0) as u32,
                    r[3].as_u64().unwrap_or(0) as u32,
                );
                let hit = r[4].as_u64().unwrap_or(0) > 0;
                let e = region_hits.entry(key).or_insert(false);
                *e = *e || hit;
            }
        }
        // Branch record: [l1, c1, l2, c2, trueCount, falseCount, fileID,
        // expandedFileID, kind]. Two arms per record.
        if let Some(branches) = f["branches"].as_array() {
            for b in branches {
                let Some(b) = b.as_array() else { continue };
                if b.len() < 9 {
                    continue;
                }
                let file = file_of(b[6].as_u64().unwrap_or(0));
                let span = (
                    b[0].as_u64().unwrap_or(0) as u32,
                    b[1].as_u64().unwrap_or(0) as u32,
                    b[2].as_u64().unwrap_or(0) as u32,
                    b[3].as_u64().unwrap_or(0) as u32,
                );
                for (arm, count_idx) in [(0u8, 4usize), (1u8, 5usize)] {
                    let key = (file.clone(), span.0, span.1, span.2, span.3, arm);
                    let hit = b[count_idx].as_u64().unwrap_or(0) > 0;
                    let e = branch_arm_hits.entry(key).or_insert(false);
                    *e = *e || hit;
                }
            }
        }
    }

    if instantiations == 0 {
        return Ok(None);
    }
    if candidate_source_files.len() > 1 {
        return Err(format!(
            "ambiguous coverage identity for `{}`: matched records from {}",
            ext.target_path,
            candidate_source_files
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    let regions_total = region_hits.len() as u32;
    let regions_hit = region_hits.values().filter(|h| **h).count() as u32;
    let mut branches_total = branch_arm_hits.len() as u32;
    let mut branches_hit = branch_arm_hits.values().filter(|h| **h).count() as u32;

    // Arm witnessing: when the MIR manifest supplied the target's
    // complete arm anchors, read each arm's region counter. Witnessed
    // evidence is PREFERRED over llvm's own branch records — the MIR
    // inventory is the authoritative arm denominator (llvm records
    // cover `if`/`&&`/`||` syntax only), and over region proxies.
    // A resolution WITHOUT a usable anchor set still annotates the row
    // with the MIR denominator, so a proxy percentage is always read
    // next to the arm count it failed to witness.
    let mut evidence = if branches_total > 0 {
        ExtEvidenceKind::BranchArms
    } else {
        ExtEvidenceKind::RegionsProxy
    };
    let mut arm_witness_note = None;
    let mut mir_arms = None;
    let mut witnessed_misses: Vec<(String, u32)> = Vec::new();
    if let Some(crate::cov_mir::MirResolution::Branches {
        arms, arm_spans, ..
    }) = resolution
    {
        mir_arms = Some(*arms);
        let fallback = match evidence {
            ExtEvidenceKind::BranchArms => "llvm branch",
            _ => "region proxy",
        };
        if !arm_spans.is_empty() && arm_spans.len() as u64 == *arms {
            match witness_arms(arm_spans, &region_hits) {
                Ok(witnessed) => {
                    evidence = ExtEvidenceKind::MirArmsWitnessed;
                    branches_total = witnessed.len() as u32;
                    branches_hit = witnessed.iter().filter(|w| **w).count() as u32;
                    for (arm, hit) in arm_spans.iter().zip(&witnessed) {
                        if !hit {
                            witnessed_misses.push((arm.file.clone(), arm.line));
                        }
                    }
                }
                Err(why) => {
                    arm_witness_note = Some(format!(
                        "arm witnessing unavailable ({why}); showing {fallback} evidence instead"
                    ));
                }
            }
        } else {
            arm_witness_note = Some(format!(
                "arm witnessing unavailable (manifest anchors cover {}/{arms} arms); \
                 showing {fallback} evidence instead",
                arm_spans.len()
            ));
        }
    }

    // Unreached listing: witnessed arm anchors when arm evidence stands,
    // else llvm branch arms, else regions.
    let mut unreached: BTreeSet<(String, u32)> = BTreeSet::new();
    if evidence == ExtEvidenceKind::MirArmsWitnessed {
        unreached.extend(witnessed_misses);
    } else if branches_total > 0 {
        for ((file, l1, ..), hit) in &branch_arm_hits {
            if !hit {
                unreached.insert((file.clone(), *l1));
            }
        }
    } else {
        for ((file, l1, ..), hit) in &region_hits {
            if !hit {
                unreached.insert((file.clone(), *l1));
            }
        }
    }
    const MAX_UNREACHED_LINES: usize = 10;
    let unreached: Vec<(String, u32)> = unreached.into_iter().take(MAX_UNREACHED_LINES).collect();
    let line_only_reason = matches!(
        evidence,
        ExtEvidenceKind::RegionsProxy | ExtEvidenceKind::LinesProxy
    )
    .then(|| {
        arm_witness_note.clone().unwrap_or_else(|| match resolution {
            Some(crate::cov_mir::MirResolution::Unresolved) => {
                "MIR target unresolved and LLVM emitted no branch records".to_string()
            }
            Some(crate::cov_mir::MirResolution::Ambiguous { candidates }) => format!(
                "MIR target resolution is ambiguous across {} candidates and LLVM emitted no branch records",
                candidates.len()
            ),
            Some(crate::cov_mir::MirResolution::Branchless { .. }) => {
                "MIR reported zero arms, but branchless classification was not applied".to_string()
            }
            Some(crate::cov_mir::MirResolution::Branches { arms, .. }) => format!(
                "MIR reports {arms} arms, but no complete arm-to-region mapping was available"
            ),
            None => "MIR manifest unavailable and LLVM emitted no branch records".to_string(),
        })
    });

    Ok(Some(ExtMeasurement {
        regions_total,
        regions_hit,
        branches_total,
        branches_hit,
        instantiations,
        tier: profile.tier.label(),
        evidence,
        backend: ExtExtractionBackend::Export,
        line_only_reason,
        unreached,
        arm_witness_note,
        mir_arms,
        clauses: Vec::new(),
        probes: Vec::new(),
    }))
}

/// Fallback extraction through `llvm-cov show` text output (used when
/// `export` crashes; see the call site). Output shape per matched
/// instantiation:
///
/// ```text
/// <mangled name>:
///   890|    256|        pub const fn checked_add(...) {
///   ------------------
///   |  Branch (898:16): [True: 106, False: 150]
///   ------------------
///   899|    106|                None
/// ```
///
/// Instrumented lines have a count field (possibly abbreviated, e.g.
/// `4.10k` — only zero/nonzero matters here); uninstrumented lines have
/// an empty one. Branch annotations carry `[True: n, False: m]` arm
/// counts or `[Folded - Ignored]` (skipped). Lines/arms are deduped by
/// line number across instantiations, hit if any instantiation hit
/// them. Coarser than export (line- instead of region-level, and no
/// source file attribution for the unreached list), hence the tier
/// label suffix.
fn extract_target_via_show(
    tools: &LlvmTools,
    profile: &Profile,
    matcher: &TargetMatcher,
    resolution: Option<&crate::cov_mir::MirResolution>,
    export_failure: String,
) -> Result<Option<ExtMeasurement>, String> {
    let show = Command::new(&tools.cov)
        .args(["show", "--num-threads=1", "--instr-profile"])
        .arg(&profile.profdata)
        .arg("--object")
        .arg(&profile.binary)
        .arg(format!(
            "--name-regex={}",
            matcher.mangled_name_regex(&profile.binary)
        ))
        .arg("--show-branches=count")
        .arg("--show-line-counts-or-regions")
        .arg("--show-regions")
        .arg("--show-expansions")
        .output()
        .map_err(|e| format!("spawn llvm-cov show: {e}"))?;
    if !show.status.success() {
        let stderr = String::from_utf8_lossy(&show.stderr);
        let head: String = stderr.lines().take(14).collect::<Vec<_>>().join("\n");
        return Err(format!(
            "llvm-cov export crashed and the `show` fallback failed too:\n{head}"
        ));
    }
    let text = String::from_utf8_lossy(&show.stdout);

    let mut line_hits: BTreeMap<u32, bool> = BTreeMap::new();
    let mut region_start_hits: BTreeMap<(u32, u32), bool> = BTreeMap::new();
    let mut branch_arm_hits: BTreeMap<(u32, u32, u8), bool> = BTreeMap::new();
    let mut matched_identities: BTreeSet<String> = BTreeSet::new();
    let mut instantiations = 0u32;
    let mut in_match = false;
    let mut current_source_line: Option<(u32, usize)> = None;

    for line in text.lines() {
        // Instantiation header: `<mangled>:` at column 0.
        if !line.starts_with(' ') && line.ends_with(':') && !line.contains('|') {
            let mangled = &line[..line.len() - 1];
            let demangled = format!("{:#}", rustc_demangle::demangle(mangled));
            in_match = matcher.matches(&demangled);
            current_source_line = None;
            if in_match {
                instantiations += 1;
                if let Some(identity) = matcher.canonical_match_identity(&demangled) {
                    matched_identities.insert(identity);
                }
            }
            continue;
        }
        if !in_match {
            continue;
        }

        // `--show-regions` annotates a source line with one or more
        // caret/count markers (`^0`, `^17`, `^4.10k`) aligned under the
        // source text. Preserve their start columns as distinct counters;
        // unlike whole-line counts, these can witness same-line MIR arms.
        if !line.contains('|') {
            if let Some((source_line, source_offset)) = current_source_line {
                for (pos, ch) in line.char_indices() {
                    if ch != '^' || pos < source_offset {
                        continue;
                    }
                    let token: String = line[pos + 1..]
                        .chars()
                        .take_while(|c| !c.is_whitespace() && *c != '^')
                        .collect();
                    if token.is_empty() {
                        continue;
                    }
                    let hit = token != "0" && !token.starts_with("0 ");
                    let col = (pos - source_offset + 1) as u32;
                    let entry = region_start_hits
                        .entry((source_line, col))
                        .or_insert(false);
                    *entry = *entry || hit;
                }
            }
        }
        let trimmed = line.trim_start();
        // Branch annotation: `|  Branch (L:C): [True: n, False: m]`.
        if let Some(rest) = trimmed.strip_prefix("|  Branch (") {
            let Some((coords, tail_part)) = rest.split_once("):") else {
                continue;
            };
            let Some((l, c)) = coords.split_once(':') else {
                continue;
            };
            let (Ok(l), Ok(c)) = (l.trim().parse::<u32>(), c.trim().parse::<u32>()) else {
                continue;
            };
            if tail_part.contains("Folded") {
                continue;
            }
            let parse_count = |key: &str| -> Option<u64> {
                let idx = tail_part.find(key)?;
                let after = &tail_part[idx + key.len()..];
                let digits: String = after
                    .trim_start()
                    .chars()
                    .take_while(|ch| ch.is_ascii_digit())
                    .collect();
                digits.parse::<u64>().ok()
            };
            if let (Some(t), Some(f)) = (parse_count("True:"), parse_count("False:")) {
                for (arm, count) in [(0u8, t), (1u8, f)] {
                    let e = branch_arm_hits.entry((l, c, arm)).or_insert(false);
                    *e = *e || count > 0;
                }
            }
            continue;
        }
        // Source line: `  NNN|  COUNT|source`. Uninstrumented lines
        // have an empty count field; abbreviated counts (`4.10k`) only
        // need zero/nonzero discrimination.
        let mut bars = line.match_indices('|');
        let _first_bar = bars.next();
        let source_offset = bars.next().map(|(index, _)| index + 1);
        let mut fields = line.splitn(3, '|');
        let (Some(no), Some(count), Some(_src)) = (fields.next(), fields.next(), fields.next())
        else {
            continue;
        };
        let Ok(no) = no.trim().parse::<u32>() else {
            continue;
        };
        let Some(source_offset) = source_offset else {
            continue;
        };
        current_source_line = Some((no, source_offset));
        let count = count.trim();
        if count.is_empty() {
            continue;
        }
        let hit = count != "0";
        let e = line_hits.entry(no).or_insert(false);
        *e = *e || hit;
    }

    if instantiations == 0 {
        return Ok(None);
    }
    if matched_identities.len() > 1 {
        return Err(format!(
            "ambiguous coverage identity for `{}` in llvm-cov show fallback: matched {}",
            matcher.last_seg,
            matched_identities
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    let regions_total = line_hits.len() as u32;
    let regions_hit = line_hits.values().filter(|h| **h).count() as u32;
    let mut branches_total = branch_arm_hits.len() as u32;
    let mut branches_hit = branch_arm_hits.values().filter(|h| **h).count() as u32;
    let mut evidence = if branches_total > 0 {
        ExtEvidenceKind::BranchArms
    } else {
        ExtEvidenceKind::LinesProxy
    };
    let mut arm_witness_note = None;
    let mut mir_arms = None;
    let mut witnessed_misses: Vec<(String, u32)> = Vec::new();

    match resolution {
        Some(crate::cov_mir::MirResolution::Branches {
            arms, arm_spans, ..
        }) => {
            mir_arms = Some(*arms);
            let fallback = if evidence == ExtEvidenceKind::BranchArms {
                "LLVM branch evidence"
            } else {
                "source-line evidence"
            };
            if !arm_spans.is_empty() && arm_spans.len() as u64 == *arms {
                match witness_arms_by_show_counters(
                    arm_spans,
                    &line_hits,
                    &region_start_hits,
                ) {
                    Ok(witnessed) => {
                        evidence = ExtEvidenceKind::MirArmsWitnessed;
                        branches_total = witnessed.len() as u32;
                        branches_hit = witnessed.iter().filter(|hit| **hit).count() as u32;
                        for (arm, hit) in arm_spans.iter().zip(&witnessed) {
                            if !hit {
                                witnessed_misses.push((arm.file.clone(), arm.line));
                            }
                        }
                    }
                    Err(why) => {
                        arm_witness_note = Some(format!(
                            "MIR arm witnessing from llvm-cov show unavailable ({why}); using {fallback}"
                        ));
                    }
                }
            } else {
                arm_witness_note = Some(format!(
                    "MIR arm witnessing from llvm-cov show unavailable (manifest anchors cover {}/{arms} arms); using {fallback}",
                    arm_spans.len()
                ));
            }
        }
        Some(crate::cov_mir::MirResolution::Ambiguous { candidates }) => {
            arm_witness_note = Some(format!(
                "MIR target resolution is ambiguous across {} candidates",
                candidates.len()
            ));
        }
        Some(crate::cov_mir::MirResolution::Unresolved) => {
            arm_witness_note = Some("MIR target resolution is unavailable".to_string());
        }
        Some(crate::cov_mir::MirResolution::Branchless { .. }) => {
            arm_witness_note = Some(
                "MIR reported zero arms, but branchless classification was not applied".to_string(),
            );
        }
        None => {
            arm_witness_note = Some("MIR manifest is unavailable".to_string());
        }
    }

    let mut unreached: BTreeSet<(String, u32)> = BTreeSet::new();
    if evidence == ExtEvidenceKind::MirArmsWitnessed {
        unreached.extend(witnessed_misses);
    } else if branches_total > 0 {
        for ((l, _c, _arm), hit) in &branch_arm_hits {
            if !hit {
                unreached.insert(("<target source>".to_string(), *l));
            }
        }
    } else {
        for (l, hit) in &line_hits {
            if !hit {
                unreached.insert(("<target source>".to_string(), *l));
            }
        }
    }
    let unreached: Vec<(String, u32)> = unreached.into_iter().take(10).collect();
    let line_only_reason = (evidence == ExtEvidenceKind::LinesProxy).then(|| {
        let witness_reason = arm_witness_note
            .clone()
            .unwrap_or_else(|| "LLVM emitted no branch records".to_string());
        format!("{export_failure}; {witness_reason}")
    });

    Ok(Some(ExtMeasurement {
        regions_total,
        regions_hit,
        branches_total,
        branches_hit,
        instantiations,
        tier: match profile.tier {
            Tier::Stable => "stable, lines via show",
            Tier::NightlyDependencies => "nightly dependencies, branches via show",
            Tier::NightlyBuildStd => "nightly build-std, branches via show",
        },
        evidence,
        backend: ExtExtractionBackend::Show,
        line_only_reason,
        unreached,
        arm_witness_note,
        mir_arms,
        clauses: Vec::new(),
        probes: Vec::new(),
    }))
}

/// Matches an assume_spec target path against demangled llvm-cov
/// function names. A demangled name matches when:
///  - it ends with `::<last segment>` (modulo a generic suffix, and
///    excluding `{closure}` records), and
///  - the path component immediately BEFORE the last segment — the
///    impl self type or parent module — agrees with the target's
///    (compared by normalized base name, so `Vec<u32>` ↔ `Vec` and
///    `<impl u32>` ↔ `u32`), and
///  - inherent targets reject trait-impl demanglings (`<u32 as
///    CheckedAdd>::checked_add` must not shadow `u32::checked_add`).
///
/// The self-segment comparison is what keeps lookalikes out: a bare
/// token scan would accept `NonZero<u32>::checked_add` for target
/// `u32::checked_add` (both contain "u32" and end in the segment).
///
/// Examples that must match:
///  - `u32::checked_add` ↔ `core::num::<impl u32>::checked_add`
///  - `<[u8]>::binary_search` ↔ `core::slice::<impl [u8]>::binary_search::<u8>`
///  - `Vec::<T>::clear` (T substituted) ↔ `alloc::vec::Vec<u32>::clear`
///  - `covext_dep::classify` ↔ `covext_dep::classify`
struct TargetMatcher {
    last_seg: String,
    self_pattern: Option<SelfPattern>,
    /// Final normalized trait-path segment for a qualified trait target.
    trait_base: Option<String>,
    require_inherent: bool,
}

/// A target self type after retaining only the distinctions needed for
/// coverage identity matching. Generic slices are structural patterns:
/// `<[T]>::method` must match each concrete slice monomorphization while
/// concrete `<[u8]>::method` targets remain exact.
enum SelfPattern {
    Exact(String),
    GenericSlice { canonical: String },
}

impl SelfPattern {
    fn from_target(component: &str, generic_type_params: &[&str]) -> Self {
        let normalized = normalize_self_component(component);
        let generic_slice = slice_element(&normalized)
            .is_some_and(|element| generic_type_params.iter().any(|param| element == *param));
        if generic_slice {
            Self::GenericSlice {
                canonical: normalized,
            }
        } else {
            Self::Exact(normalized)
        }
    }

    fn matches(&self, component: &str) -> bool {
        let normalized = normalize_self_component(component);
        match self {
            Self::Exact(want) => normalized == *want,
            Self::GenericSlice { .. } => slice_element(&normalized).is_some(),
        }
    }

    fn canonical_component(&self, component: &str) -> String {
        match self {
            Self::Exact(_) => normalize_self_component(component),
            Self::GenericSlice { canonical } => canonical.clone(),
        }
    }
}

/// Return the element text for a slice self type, rejecting an array.
/// Only a semicolon at the outer element level denotes an array, so a
/// slice of arrays (`[[u8; 4]]`) remains a slice.
fn slice_element(component: &str) -> Option<&str> {
    let inner = component.strip_prefix('[')?.strip_suffix(']')?;
    let mut depth = 0usize;
    for ch in inner.chars() {
        match ch {
            '<' | '[' | '(' | '{' => depth += 1,
            '>' | ']' | ')' | '}' => depth = depth.saturating_sub(1),
            ';' if depth == 0 => return None,
            _ => {}
        }
    }
    Some(inner)
}

/// Normalize a path component to its comparable base: strip an
/// `<impl ...>` / `<...>` wrapper and whitespace, reduce a
/// path-qualified type to its final segment (v0-demangled records
/// spell ADT self types fully qualified: `<core::option::Option<u64>>`
/// must compare as `Option`), and truncate generic arguments
/// (`Vec<u32>` -> `Vec`) — except for slice/tuple/array self types
/// (`[u8]`, `(A, B)`), which keep their full bracketed text.
fn normalize_self_component(comp: &str) -> String {
    let mut s = comp.trim().to_string();
    if s.starts_with('<') && s.ends_with('>') {
        s = s[1..s.len() - 1].trim().to_string();
    }
    if let Some(rest) = s.strip_prefix("impl ") {
        s = rest.trim().to_string();
    }
    if let Some((self_ty, _trait_path)) = s.split_once(" as ") {
        s = self_ty.trim().to_string();
    }
    s.retain(|c| c != ' ');
    if s.starts_with('[') || s.starts_with('(') {
        return s;
    }
    // `::<...>` is a turbofish on the preceding self type, not a path
    // separator followed by an anonymous component. Canonicalize only this
    // boundary so qualified vstd targets such as `BTreeMap::<K,V,A>` retain
    // the `BTreeMap` base while ordinary module paths stay distinct.
    s = s.replace("::<", "<");
    // Final path segment at bracket depth zero, then strip generics:
    // `core::option::Option<u64>` -> `Option<u64>` -> `Option`.
    let last = last_path_component(&s).to_string();
    match last.find('<') {
        Some(pos) => last[..pos].to_string(),
        None => last,
    }
}

/// Whether two trait paths (whitespace already removed) agree, allowing
/// different qualification levels: the shorter spelling must equal the
/// SEGMENT SUFFIX of the longer (`Clone` ↔ `core::clone::Clone`, but
/// `example::Checked` ✗ `other::Checked`). Generic args on the final
/// segment are ignored.
fn trait_paths_agree(a: &str, b: &str) -> bool {
    let segs = |s: &str| -> Vec<String> {
        s.split("::")
            .filter(|seg| !seg.is_empty())
            .map(|seg| seg.split('<').next().unwrap_or(seg).to_string())
            .collect()
    };
    let a = segs(a);
    let b = segs(b);
    if a.is_empty() || b.is_empty() {
        return false;
    }
    let (short, long) = if a.len() <= b.len() {
        (&a, &b)
    } else {
        (&b, &a)
    };
    long[long.len() - short.len()..] == short[..]
}

/// Split off the last `::`-separated component of a path prefix,
/// respecting nesting (`<>`/`[]`/`()`), so
/// `core::num::<impl u32>` -> `<impl u32>` and
/// `alloc::vec::Vec<u32>` -> `Vec<u32>`.
fn last_path_component(prefix: &str) -> &str {
    let bytes = prefix.as_bytes();
    let mut depth = 0i32;
    let mut i = bytes.len();
    while i >= 2 {
        let c = bytes[i - 1] as char;
        match c {
            '>' | ']' | ')' => depth += 1,
            '<' | '[' | '(' => depth -= 1,
            ':' if depth == 0 && bytes[i - 2] == b':' => {
                return &prefix[i..];
            }
            _ => {}
        }
        i -= 1;
    }
    prefix
}

impl TargetMatcher {
    #[cfg(test)]
    fn new(target_path: &str) -> Self {
        Self::new_with_generic_type_params(target_path, &[])
    }

    /// Keep build-std `llvm-cov` queries narrow enough to avoid every
    /// same-named function in the dependency graph. Generic slice methods
    /// are constrained to the v0-mangled `core::slice` namespace and exact
    /// encoded method length/name; precise self-type matching still happens
    /// after demangling. Do not require the consuming crate as a suffix:
    /// v0 can encode it as a back-reference (for example `split_atB4_`).
    fn mangled_name_regex(&self, _binary: &Path) -> String {
        if matches!(self.self_pattern, Some(SelfPattern::GenericSlice { .. })) {
            return format!(
                ".*4core5slice.*[^0-9]{}{}.*",
                self.last_seg.len(),
                regex_escape(&self.last_seg),
            );
        }
        format!(".*{}.*", regex_escape(&self.last_seg))
    }

    fn new_with_generic_type_params(target_path: &str, generic_type_params: &[&str]) -> Self {
        let require_inherent = !target_path.contains(" as ");
        // Qualified-self form `<[u8]>::binary_search`: the self type is
        // the bracketed prefix.
        if let Some(rest) = target_path.strip_prefix('<') {
            if let Some(close) = rest.rfind(">::") {
                let inner = rest[..close].trim();
                let (self_txt, trait_txt) = match inner.split_once(" as ") {
                    Some((self_ty, trait_path)) => (self_ty, Some(trait_path)),
                    None => (inner, None),
                };
                let tail = &rest[close + 3..];
                let last_seg = tail.split("::").next().unwrap_or(tail).trim().to_string();
                let trait_base = trait_txt.map(|path| path.trim().replace(' ', ""));
                return TargetMatcher {
                    last_seg,
                    self_pattern: Some(SelfPattern::from_target(self_txt, generic_type_params)),
                    trait_base,
                    require_inherent,
                };
            }
        }
        // Ordinary path: drop `<...>` groups, split on `::`; the last
        // segment is the fn, the one before it the self/parent.
        let mut cleaned = String::new();
        let mut depth = 0usize;
        for ch in target_path.chars() {
            match ch {
                '<' => depth += 1,
                '>' => depth = depth.saturating_sub(1),
                _ if depth == 0 => cleaned.push(ch),
                _ => {}
            }
        }
        let segs: Vec<&str> = cleaned
            .split("::")
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .collect();
        let last_seg = segs.last().map(|s| s.to_string()).unwrap_or_default();
        let self_pattern = if segs.len() >= 2 {
            Some(SelfPattern::from_target(
                segs[segs.len() - 2],
                generic_type_params,
            ))
        } else {
            None
        };
        TargetMatcher {
            last_seg,
            self_pattern,
            trait_base: None,
            require_inherent,
        }
    }

    fn canonical_match_identity(&self, demangled: &str) -> Option<String> {
        if !self.matches(demangled) {
            return None;
        }
        let needle = format!("::{}", self.last_seg);
        let pos = demangled.rfind(&needle)?;
        let prefix = &demangled[..pos];
        let component = last_path_component(prefix);
        let parent = &prefix[..prefix.len().saturating_sub(component.len())];
        let self_component = self
            .self_pattern
            .as_ref()
            .map(|pattern| pattern.canonical_component(component))
            .unwrap_or_else(|| normalize_self_component(component));
        let normalized_component = if let Some(want_trait) = &self.trait_base {
            format!("<{self_component} as {want_trait}>")
        } else {
            self_component
        };
        Some(format!("{parent}{normalized_component}::{}", self.last_seg))
    }

    fn matches(&self, demangled: &str) -> bool {
        if self.last_seg.is_empty() {
            return false;
        }
        // The demangled name must contain `::<last_seg>` at the end or
        // followed only by a generic suffix (`::<u8>`). Closure records
        // inside the target fn are excluded (their regions overlap the
        // fn's own span anyway).
        let needle = format!("::{}", self.last_seg);
        let Some(pos) = demangled.rfind(&needle) else {
            return false;
        };
        let after = &demangled[pos + needle.len()..];
        let suffix_ok = after.is_empty() || after.starts_with("::<") || after.starts_with('<');
        if !suffix_ok {
            return false;
        }
        if after.contains("{closure") {
            return false;
        }
        if self.require_inherent && demangled.contains(" as ") {
            return false;
        }
        let impl_component = last_path_component(&demangled[..pos]);
        if let Some(want_trait) = &self.trait_base {
            let inner = impl_component
                .trim()
                .strip_prefix('<')
                .and_then(|value| value.strip_suffix('>'))
                .unwrap_or(impl_component);
            let Some((_self_ty, trait_path)) = inner.split_once(" as ") else {
                return false;
            };
            // The two sides may spell the trait at different
            // qualification levels (`Clone` vs `core::clone::Clone`):
            // compare by SEGMENT SUFFIX — the shorter spelling must
            // match the tail of the longer segment-for-segment, so
            // `example::Checked` still rejects `other::Checked`.
            let got_trait = trait_path.trim().replace(' ', "");
            if !trait_paths_agree(want_trait, &got_trait) {
                return false;
            }
        }
        match &self.self_pattern {
            None => true,
            Some(pattern) => pattern.matches(impl_component),
        }
    }
}

#[cfg(test)]
mod generic_self_pattern_tests {
    use super::*;

    #[test]
    fn generic_slice_matches_concrete_monomorphizations() {
        let matcher = TargetMatcher::new_with_generic_type_params("<[T]>::split_at_mut", &["T"]);
        assert!(matcher.matches("core::slice::<impl [u64]>::split_at_mut"));
        let real_v0 = format!(
            "{:#}",
            rustc_demangle::demangle(
                "_RNvMNtCs9MQHkwYPobK_4core5sliceSm12split_at_mutCs2M3t1OOTdHu_4vstd"
            )
        );
        assert!(matcher.matches(&real_v0), "demangled identity: {real_v0}");
        assert!(matcher.matches("core::slice::<impl [alloc::boxed::Box<u64>]>::split_at_mut"));
        assert!(matcher.matches("core::slice::<impl [[u8; 4]]>::split_at_mut"));
        assert!(!matcher.matches("core::slice::<impl [u64; 4]>::split_at_mut"));
        assert!(!matcher.matches("alloc::vec::Vec<u64>::split_at_mut"));
    }

    #[test]
    fn generic_slice_instances_share_a_canonical_identity() {
        let matcher = TargetMatcher::new_with_generic_type_params("<[T]>::split_at_mut", &["T"]);
        assert_eq!(
            matcher.canonical_match_identity("core::slice::<impl [u64]>::split_at_mut"),
            matcher.canonical_match_identity(
                "core::slice::<impl [alloc::boxed::Box<u64>]>::split_at_mut"
            ),
        );
    }

    #[test]
    fn concrete_slice_targets_remain_exact() {
        let matcher = TargetMatcher::new("<[u8]>::binary_search");
        assert!(matcher.matches("core::slice::<impl [u8]>::binary_search"));
        assert!(!matcher.matches("core::slice::<impl [u16]>::binary_search"));
    }
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

fn capture_ok(bin: &str, args: &[&str]) -> Result<String, String> {
    let out = Command::new(bin)
        .args(args)
        .output()
        .map_err(|e| format!("spawn {bin}: {e}"))?;
    if !out.status.success() {
        return Err(format!("{bin} {args:?} failed"));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

fn regex_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if !c.is_alphanumeric() && c != '_' {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

fn side_build_diagnostics(stdout: &[u8], stderr: &[u8]) -> String {
    let stdout = String::from_utf8_lossy(stdout);
    let stderr = String::from_utf8_lossy(stderr);
    let mut rendered = Vec::new();
    let mut raw_stdout = Vec::new();

    for line in stdout.lines() {
        match serde_json::from_str::<serde_json::Value>(line) {
            Ok(message) if message["reason"] == "compiler-message" => {
                if let Some(diagnostic) = message["message"]["rendered"].as_str() {
                    rendered.push(diagnostic.trim_end().to_string());
                } else if let Some(diagnostic) = message["message"]["message"].as_str() {
                    rendered.push(diagnostic.to_string());
                }
            }
            Err(_) if !line.trim().is_empty() => raw_stdout.push(line),
            _ => {}
        }
    }

    let details = if !rendered.is_empty() {
        // Cargo's JSON stream carries rustc diagnostics on stdout. Keep a
        // bounded tail so a crate with many cascading errors does not flood
        // the coverage report while still preserving rendered spans/notes.
        tail(&rendered.join("\n"), 80)
    } else {
        // Resolver/toolchain failures may occur before Cargo emits any
        // compiler-message objects. Preserve non-JSON stdout and stderr as
        // the fallback rather than collapsing them to a generic build error.
        let mut fallback = Vec::new();
        if !raw_stdout.is_empty() {
            fallback.push(format!(
                "cargo stdout:\n{}",
                tail(&raw_stdout.join("\n"), 20)
            ));
        }
        if !stderr.trim().is_empty() {
            fallback.push(format!("cargo stderr:\n{}", tail(&stderr, 20)));
        }
        if fallback.is_empty() {
            "cargo emitted no diagnostic output".to_string()
        } else {
            fallback.join("\n")
        }
    };

    // Defused: this reason is embedded in test output that downstream
    // tooling greps for build-failure markers.
    crate::cov_mir::sanitize_compiler_output(&details)
}

fn tail(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}

/// Crate-internal accessors for the `cov_mir` manifest pass (same
/// scratch root and progress/tail conventions as the side builds).
pub(crate) fn scratch_base_of(crate_dir: &str) -> PathBuf {
    scratch_base(crate_dir)
}

pub(crate) fn tail_of(s: &str, n: usize) -> String {
    tail(s, n)
}

/// Progress note to the controlling terminal (same convention as the
/// report itself): visible inline under plain `cargo test`, routed to
/// stderr in quiet mode.
pub(crate) fn progress(msg: &str) {
    #[cfg(unix)]
    if !crate::cov_fuzz::quiet_requested() {
        use std::io::Write;
        if let Ok(mut tty) = std::fs::OpenOptions::new().write(true).open("/dev/tty") {
            let _ = writeln!(tty, "{msg}");
            return;
        }
    }
    eprintln!("{msg}");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// LLVM major extraction from `rustc -vV` and from a tool's
    /// `--version` text — the inputs the nightly-tier version-match
    /// probe compares.
    #[test]
    fn llvm_major_parsers() {
        let vv = "rustc 1.98.0-nightly (b30f3df3b 2026-06-11)\n\
                  binary: rustc\n\
                  host: aarch64-apple-darwin\n\
                  release: 1.98.0-nightly\n\
                  LLVM version: 21.1.2\n";
        assert_eq!(llvm_major_from_vv(vv), Some(21));
        assert_eq!(llvm_major_from_vv("no llvm line here"), None);
        // Tool-output shape: "Apple LLVM version 20.1.6\n  optimized build".
        // (llvm_major_of_tool shells out; its text parsing is the same
        // find-"LLVM version"-then-major logic, exercised via the vv
        // parser above and the mismatch e2e behavior.)
    }

    /// std/core/alloc-origin targets route straight to build-std; the
    /// exact path shapes come from the vstd annotations (primitives,
    /// qualified-self slices/traits, std containers, explicit crate
    /// roots).
    #[test]
    fn std_origin_routing_recognizes_vstd_target_shapes() {
        for path in [
            "u32::checked_add",
            "i128::wrapping_mul",
            "char::len_utf8",
            "bool::clone",
            "core::mem::swap::<T>",
            "core::intrinsics::likely",
            "std::vec::Vec::<T>::new",
            "alloc::boxed::Box::<T>::new",
            "Vec::<T,A>::push",
            "VecDeque::<T,A>::pop_front",
            "Option::<T>::is_some",
            "Result::<T,E>::unwrap",
            "BTreeMap::<Key,Value>::new",
            "HashSet::<Key>::new",
            "Rc::<T>::new",
            "Arc::<T>::new",
            "String::clear",
            "<[T]>::first",
            "<i8 as Clone>::clone",
            "<Vec<T,A> as core::ops::Deref>::deref",
            "<BTreeMap<K,V> as core::default::Default>::default",
            "<HashMap<K,V,S,> as core::default::Default>::default",
        ] {
            assert!(
                target_is_std_origin(path),
                "expected std origin for `{path}`"
            );
        }
    }

    /// Dependency-crate targets must NOT be routed to build-std first —
    /// the dependency tier is much cheaper and produces true branch
    /// records for them.
    #[test]
    fn dependency_targets_are_not_std_origin() {
        for path in [
            "covext_dep::classify",
            "my_crate::module::helper",
            "some_dep::Widget::step",
            "<some_dep::Widget as Clone>::clone",
        ] {
            assert!(
                !target_is_std_origin(path),
                "expected dependency origin for `{path}`"
            );
        }
    }

    /// v0-demangled records spell ADT self types PATH-QUALIFIED
    /// (`<core::option::Option<u64>>::is_some`); the matcher must
    /// reduce them to the base name the target spells (`Option`).
    /// This was the second half of why Option/Vec records never
    /// matched even when instantiated.
    #[test]
    fn matcher_handles_v0_path_qualified_self() {
        let m = TargetMatcher::new("Option::<T>::is_some");
        assert!(m.matches("<core::option::Option<u64>>::is_some"));
        assert!(m.matches("<core::option::Option<u32>>::is_some"));
        // Lookalike self types must still be rejected.
        assert!(!m.matches("<core::result::Result<u64, u8>>::is_some"));

        let m = TargetMatcher::new("Vec::<T,A>::pop");
        assert!(m.matches("<alloc::vec::Vec<u64, alloc::alloc::Global>>::pop"));
        assert!(!m.matches("<alloc::collections::vec_deque::VecDeque<u64>>::pop"));

        // Trait impls in v0 form: `<alloc::vec::Vec<u64> as
        // core::ops::deref::Deref>::deref`.
        let m = TargetMatcher::new("<Vec<T,A> as core::ops::Deref>::deref");
        assert!(
            m.matches("<alloc::vec::Vec<u64, alloc::alloc::Global> as core::ops::Deref>::deref")
        );

        // Trait spelled short on the target side, fully qualified in
        // the record; compared by final segment, disambiguated by the
        // self base.
        let m = TargetMatcher::new("<i8 as Clone>::clone");
        assert!(m.matches("<i8 as core::clone::Clone>::clone"));
        assert!(!m.matches("<i16 as core::clone::Clone>::clone"));
        assert!(!m.matches("<i8 as core::default::Default>::clone"));
    }

    #[test]
    fn matcher_handles_primitive_inherent_impl() {
        let m = TargetMatcher::new("u32::checked_add");
        assert!(m.matches("core::num::<impl u32>::checked_add"));
        assert!(m.matches("<u32>::checked_add"));
        assert!(!m.matches("core::num::<impl u32>::checked_add_unsigned"));
        assert!(!m.matches("core::num::<impl u64>::checked_add"));
        assert!(!m.matches("compiler_builtins::int_traits::Int::checked_add"));
        // A dependency crate's TRAIT impl over the same self type must
        // not shadow the inherent std target (the num-traits false
        // positive that blocked tier escalation).
        assert!(!m.matches("<u32 as num_traits::ops::checked::CheckedAdd>::checked_add"));
        // Same-name methods on OTHER self types (the NonZero false
        // positive: 12 instantiations matched via a bare `u32` token).
        assert!(!m.matches("core::num::nonzero::NonZero<u32>::checked_add"));
        assert!(!m.matches("core::num::nonzero::<impl NonZero<u32>>::checked_add"));
        assert!(!m.matches("core::num::saturating::Saturating<u32>::checked_add"));
    }

    #[test]
    fn matcher_handles_qualified_slice_self() {
        let m = TargetMatcher::new("<[u8]>::binary_search");
        assert!(m.matches("core::slice::<impl [u8]>::binary_search"));
        assert!(m.matches("core::slice::<impl [u8]>::binary_search::<u8>"));
        assert!(!m.matches("core::slice::<impl [u8]>::binary_search_by"));
        assert!(!m.matches("core::slice::<impl [u16]>::binary_search"));
        assert!(!m.matches("alloc::collections::vec_deque::VecDeque<u8>::binary_search"));
        // Closure records inside the target are excluded.
        assert!(!m.matches("core::slice::<impl [u8]>::binary_search::{closure#0}"));
    }

    #[test]
    fn matcher_compares_self_base_ignoring_generic_args() {
        let m = TargetMatcher::new("Vec::<T>::clear");
        // `T` is monomorphized away: `Vec<u32>` still matches base `Vec`.
        assert!(m.matches("alloc::vec::Vec<u32>::clear"));
        assert!(!m.matches("std::collections::HashMap<u32, u32>::clear"));
        assert!(!m.matches("alloc::collections::vec_deque::VecDeque<u32>::clear"));
    }

    #[test]
    fn matcher_handles_free_fn_in_dep_crate() {
        let m = TargetMatcher::new("covext_dep::classify");
        assert!(m.matches("covext_dep::classify"));
        assert!(!m.matches("other_crate::classify"));
        assert!(!m.matches("covext_dep::nested::classify_all"));
    }

    /// Arm witnessing maps each MIR arm anchor to the SMALLEST llvm-cov
    /// region containing it and reads that region's counter.
    #[test]
    fn witness_arms_reads_smallest_containing_region() {
        use crate::cov_mir::MirArmSpan;
        let file = "library/core/src/option.rs".to_string();
        let mut regions = BTreeMap::new();
        // Whole-fn region (hit — the fn was entered).
        regions.insert((file.clone(), 640u32, 5u32, 650u32, 6u32), true);
        // Arm 0's region: hit.
        regions.insert((file.clone(), 643, 9, 643, 15), true);
        // Arm 1's region: NOT hit.
        regions.insert((file.clone(), 645, 9, 645, 14), false);
        let arms = [
            MirArmSpan {
                file: "/Users/x/rustlib/src/rust/library/core/src/option.rs".to_string(),
                line: 643,
                col: 9,
            },
            MirArmSpan {
                file: "/Users/x/rustlib/src/rust/library/core/src/option.rs".to_string(),
                line: 645,
                col: 10,
            },
        ];
        let witnessed = witness_arms(&arms, &regions).expect("maps");
        // Arm 1 must read ITS region (miss), not the enclosing hit
        // whole-fn region.
        assert_eq!(witnessed, vec![true, false]);
    }

    /// An anchor mapping to NO region fails the whole witnessing —
    /// partial arm evidence is never presented as complete.
    #[test]
    fn witness_arms_fails_closed_on_unmapped_anchor() {
        use crate::cov_mir::MirArmSpan;
        let mut regions = BTreeMap::new();
        regions.insert(("a.rs".to_string(), 1u32, 1u32, 2u32, 1u32), true);
        let arms = [MirArmSpan {
            file: "a.rs".to_string(),
            line: 99,
            col: 1,
        }];
        let err = witness_arms(&arms, &regions).expect_err("must fail closed");
        assert!(err.contains("maps to no llvm-cov region"), "{err}");
    }

    /// File agreement requires a PATH-BOUNDARY suffix, not substring.
    #[test]
    fn file_agreement_is_path_boundary_safe() {
        assert!(files_agree("a/b/option.rs", "option.rs"));
        assert!(files_agree("option.rs", "a/b/option.rs"));
        assert!(files_agree("x.rs", "x.rs"));
        assert!(!files_agree("my_option.rs", "option.rs"));
        assert!(!files_agree("a/b/my_option.rs", "option.rs"));
    }

    /// Witnessed arm evidence is threshold-eligible, same as llvm arms.
    #[test]
    fn witnessed_arms_satisfy_branch_pct() {
        let m = ExtMeasurement {
            regions_total: 8,
            regions_hit: 8,
            branches_total: 3,
            branches_hit: 3,
            instantiations: 1,
            tier: "nightly build-std, branches",
            evidence: ExtEvidenceKind::MirArmsWitnessed,
            backend: ExtExtractionBackend::Export,
            line_only_reason: None,
            unreached: Vec::new(),
            arm_witness_note: None,
            mir_arms: Some(3),
            clauses: Vec::new(),
            probes: Vec::new(),
        };
        assert_eq!(m.branch_pct(), Some(100));
        assert_eq!(m.observed_pct(), Some(100));
    }

    #[test]
    fn branch_threshold_rejects_proxies() {
        let m = ExtMeasurement {
            regions_total: 4,
            regions_hit: 4,
            branches_total: 4,
            branches_hit: 2,
            instantiations: 1,
            tier: "nightly, branches",
            evidence: ExtEvidenceKind::BranchArms,
            backend: ExtExtractionBackend::Export,
            line_only_reason: None,
            unreached: Vec::new(),
            arm_witness_note: None,
            mir_arms: None,
            clauses: Vec::new(),
            probes: Vec::new(),
        };
        assert_eq!(m.branch_pct(), Some(50));
        let proxy = ExtMeasurement {
            branches_total: 0,
            branches_hit: 0,
            evidence: ExtEvidenceKind::RegionsProxy,
            ..m
        };
        assert_eq!(proxy.observed_pct(), Some(100));
        assert_eq!(proxy.branch_pct(), None);
    }
}

#[cfg(test)]
mod matcher_tests {
    use super::*;

    #[test]
    fn matcher_distinguishes_trait_and_inherent_methods() {
        let trait_target = TargetMatcher::new("<u32 as example::Checked>::checked");
        assert!(trait_target.matches("<u32 as example::Checked>::checked"));
        assert!(!trait_target.matches("<u32>::checked"));
        assert!(!trait_target.matches("<u32 as other::Checked>::checked"));

        let inherent = TargetMatcher::new("u32::checked");
        assert!(inherent.matches("<u32>::checked"));
        assert!(!inherent.matches("<u32 as example::Checked>::checked"));
    }

    #[test]
    fn canonical_identity_collapses_generic_instantiations() {
        let matcher = TargetMatcher::new("Vec::<T>::clear");
        assert_eq!(
            matcher.canonical_match_identity("alloc::vec::Vec<u8>::clear"),
            matcher.canonical_match_identity("alloc::vec::Vec<u32>::clear")
        );
    }

    #[test]
    fn canonical_identity_preserves_distinct_parent_paths() {
        let matcher = TargetMatcher::new("covext_dep::classify");
        let first = matcher
            .canonical_match_identity("first::covext_dep::classify")
            .expect("first candidate");
        let second = matcher
            .canonical_match_identity("second::covext_dep::classify")
            .expect("second candidate");
        assert_ne!(first, second);
    }
}
