//! MIR branch-manifest resolution for external `#[vcheck_cov_fuzz]` targets.
//!
//! The `verus-spec-check-covdriver` binary (source/covdriver) compiles the
//! crate graph — including core/alloc/std via `-Z build-std` — as a
//! plain `cargo check` and records, for every function whose def-path
//! ends in a requested needle, its MIR `SwitchInt` branch-arm inventory.
//! This module builds/drives that pass and matches
//! `assume_specification` target paths against the recorded def-paths.
//!
//! ## Why
//!
//! llvm-cov identity is reconstructed AFTER codegen, where inlining
//! erases whole function records; def-paths exist BEFORE codegen, by
//! construction. The immediate classification:
//!
//! - a target that resolves to a def with ZERO branch terminators is
//!   **branchless** — there is nothing for branch coverage to measure,
//!   and reporting it "unavailable" (a strict failure) was false
//!   accounting (`<i8 as Clone>::clone`, `Vec::new`, `default`, ...);
//! - a target that resolves WITH branch arms but has no llvm-cov record
//!   stays fail-closed unavailable, now with the honest reason: the
//!   arms exist, the LLVM tier lost them;
//! - a target that does not resolve stays fail-closed with a precise
//!   "no def-path match" reason.
//!
//! ## Def-path grammar (validated against the pinned nightly)
//!
//! ```text
//! num::<impl i64>::checked_add                     primitive inherent
//! slice::<impl [T]>::first                         slice inherent
//! vec::Vec::<T, A>::push                           container inherent
//! <vec::Vec<T, A> as core::ops::Deref>::deref      trait impl (as-form)
//! clone::impls::<impl clone::Clone for i8>::clone  trait impl (for-form)
//! mem::swap                                        free fn
//! ```
//!
//! Target paths (from `assume_specification`) look like:
//!
//! ```text
//! <i64>::checked_add     u8::trailing_zeros     Vec::<T,A>::push
//! <i8 as Clone>::clone   <[T]>::first           core::mem::swap::<T>
//! ```
//!
//! Matching is a component-wise suffix comparison of normalized path
//! components (generic args stripped, slice/tuple element types erased,
//! trait tags compared by final trait-path segment). Fail-closed:
//! ambiguity is reported, never guessed through.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

// ---------------------------------------------------------------------------
// Data model
// ---------------------------------------------------------------------------

/// Source anchor of one branch arm: the start position of the arm's
/// target-block span. The consumer maps it against llvm-cov REGION
/// records (each match arm's body is its own counted region) to
/// witness whether the arm executed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirArmSpan {
    pub file: String,
    pub line: u32,
    pub col: u32,
}

impl MirArmSpan {
    /// Parse a rustc diagnostic span string:
    /// `path/to/file.rs:5:8: 5:15` (file, start line:col, end line:col).
    /// Only the START anchor matters for region containment.
    pub(crate) fn parse(s: &str) -> Option<MirArmSpan> {
        // Split off the trailing " l2:c2" end position first.
        let start_part = match s.rfind(": ") {
            Some(pos) => &s[..pos],
            None => s,
        };
        // start_part = "path:line:col" — split from the right (paths
        // may contain colons only on non-unix; good enough here).
        let mut it = start_part.rsplitn(3, ':');
        let col: u32 = it.next()?.trim().parse().ok()?;
        let line: u32 = it.next()?.trim().parse().ok()?;
        let file = it.next()?.trim().to_string();
        if file.is_empty() {
            return None;
        }
        Some(MirArmSpan { file, line, col })
    }
}

/// One function the covdriver inventoried.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirEntry {
    /// `<crate>::<def_path>` — e.g. `core::num::<impl i64>::checked_add`.
    pub full_path: String,
    /// Total `SwitchInt` successor edges in `optimized_mir` (the MIR
    /// codegen consumes), excluding unreachable `otherwise` edges of
    /// exhaustive matches. Zero means branchless in the artifact.
    pub branch_arms: u64,
    /// One anchor per arm, ordered (switch order, successor order).
    /// Empty when the manifest predates the arm-span format (the
    /// cache key prevents that) or spans failed to parse.
    pub arm_spans: Vec<MirArmSpan>,
}

/// Outcome of resolving one target path against the manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MirResolution {
    /// Resolved to exactly one def (or several that agree) with zero
    /// branch arms: nothing for branch coverage to measure.
    Branchless { def_path: String },
    /// Resolved with a non-empty arm inventory.
    Branches {
        def_path: String,
        arms: u64,
        arm_spans: Vec<MirArmSpan>,
    },
    /// More than one def matched and they disagree — fail closed.
    Ambiguous { candidates: Vec<String> },
    /// No def-path in the manifest matches the target.
    Unresolved,
}

// ---------------------------------------------------------------------------
// Path normalization + matching
// ---------------------------------------------------------------------------

/// A normalized path component: the comparable base name plus an
/// optional trait tag (final segment of the trait path) for trait-impl
/// components. Inherent and trait components never match each other.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Component {
    base: String,
    trait_tag: Option<String>,
}

/// Split a path on `::` at bracket depth zero (`<>`/`[]`/`()`).
fn split_components(path: &str) -> Vec<&str> {
    let bytes = path.as_bytes();
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] as char {
            '<' | '[' | '(' => depth += 1,
            '>' | ']' | ')' => depth -= 1,
            ':' if depth == 0 && i + 1 < bytes.len() && bytes[i + 1] == b':' => {
                out.push(path[start..i].trim());
                start = i + 2;
                i += 1;
            }
            _ => {}
        }
        i += 1;
    }
    out.push(path[start..].trim());
    out.into_iter().filter(|s| !s.is_empty()).collect()
}

/// Base name of a type expression: last path segment, generic args
/// stripped; slice/array and tuple types erase their element types
/// (`[T]` and `[u8]` both compare as `[_]`).
fn type_base(ty: &str) -> String {
    let ty = ty.trim();
    if ty.starts_with('[') {
        return "[_]".to_string();
    }
    if ty.starts_with('(') {
        return "(_)".to_string();
    }
    // In a type expression, `::<...>` is a turbofish attached to the
    // preceding type name, not a path component. Canonicalizing only that
    // boundary keeps ordinary module separators intact while making vstd
    // spellings such as `BTreeMap::<K, V, A>` compare as `BTreeMap`.
    let canonical = ty.replace("::<", "<");
    let last = split_components(&canonical)
        .into_iter()
        .next_back()
        .unwrap_or(&canonical)
        .to_string();
    let mut base = last;
    if let Some(pos) = base.find('<') {
        base.truncate(pos);
    }
    base.trim().to_string()
}

/// Final segment of a trait path (`core::ops::Deref` -> `Deref`).
/// Trait tags are compared by this segment because the two sides spell
/// traits differently (`Clone` vs `clone::Clone` vs `core::clone::Clone`).
fn trait_tag(trait_path: &str) -> String {
    type_base(trait_path)
}

/// Normalize one raw component. `is_first` distinguishes a target
/// path's leading qualified-self (`<i64>::checked_add`) from an
/// interior pure-generic-args segment (`Vec::<T, A>::push`), which is
/// skipped entirely (`None`).
fn normalize_component(raw: &str, is_first: bool) -> Option<Component> {
    let raw = raw.trim();
    if let Some(inner) = raw.strip_prefix('<').and_then(|r| r.strip_suffix('>')) {
        let inner = inner.trim();
        // `<impl Trait for Type>` / `<impl Type>` (def-path impl form).
        if let Some(rest) = inner.strip_prefix("impl ") {
            return Some(match rest.split_once(" for ") {
                Some((trait_path, self_ty)) => Component {
                    base: type_base(self_ty),
                    trait_tag: Some(trait_tag(trait_path)),
                },
                None => Component {
                    base: type_base(rest),
                    trait_tag: None,
                },
            });
        }
        // `<Type as Trait>` (qualified form, both sides use it).
        if let Some((self_ty, trait_path)) = inner.split_once(" as ") {
            return Some(Component {
                base: type_base(self_ty),
                trait_tag: Some(trait_tag(trait_path)),
            });
        }
        // Leading `<Type>`: a target path's qualified self.
        if is_first {
            return Some(Component {
                base: type_base(inner),
                trait_tag: None,
            });
        }
        // Interior `<T, A>`: generic arguments — not a path component.
        return None;
    }
    Some(Component {
        base: type_base(raw),
        trait_tag: None,
    })
}

/// Normalize a whole path into comparable components (generic-args
/// segments dropped).
fn normalize_path(path: &str) -> Vec<Component> {
    let raw = split_components(path);
    let mut out = Vec::with_capacity(raw.len());
    for (i, comp) in raw.iter().enumerate() {
        if let Some(c) = normalize_component(comp, i == 0) {
            out.push(c);
        }
    }
    out
}

/// Whether `entry_path` matches `target_path`: every normalized target
/// component must equal the corresponding entry component, aligned at
/// the end. The target is the shorter spelling (`u8::trailing_zeros`),
/// the entry the fully-qualified one (`core::num::<impl u8>::trailing_zeros`).
fn entry_matches(target: &[Component], entry_path: &str) -> bool {
    if target.is_empty() {
        return false;
    }
    let entry = normalize_path(entry_path);
    if entry.len() < target.len() {
        return false;
    }
    let offset = entry.len() - target.len();
    target
        .iter()
        .zip(&entry[offset..])
        .all(|(want, got)| want == got)
}

/// Resolve one target path against the manifest entries.
pub(crate) fn resolve(target_path: &str, entries: &[MirEntry]) -> MirResolution {
    let target = normalize_path(target_path);
    let matches: Vec<&MirEntry> = entries
        .iter()
        .filter(|e| entry_matches(&target, &e.full_path))
        .collect();
    match matches.as_slice() {
        [] => MirResolution::Unresolved,
        [one] => single(one),
        many => {
            // Several defs matched (e.g. one per monomorphization-free
            // duplicate across the graph). Agreement lets us classify;
            // disagreement is reported, never guessed through.
            let all_branchless = many.iter().all(|e| e.branch_arms == 0);
            let all_branchy = many.iter().all(|e| e.branch_arms > 0);
            if all_branchless {
                single(many[0])
            } else if all_branchy {
                // Report the widest inventory (fail-closed direction:
                // more arms unmeasured, not fewer).
                let widest = many
                    .iter()
                    .max_by_key(|e| e.branch_arms)
                    .expect("non-empty");
                single(widest)
            } else {
                MirResolution::Ambiguous {
                    candidates: many.iter().map(|e| e.full_path.clone()).collect(),
                }
            }
        }
    }
}

fn single(entry: &MirEntry) -> MirResolution {
    if entry.branch_arms == 0 {
        MirResolution::Branchless {
            def_path: entry.full_path.clone(),
        }
    } else {
        MirResolution::Branches {
            def_path: entry.full_path.clone(),
            arms: entry.branch_arms,
            arm_spans: entry.arm_spans.clone(),
        }
    }
}

/// Final path segment of a target path — the covdriver needle.
pub(crate) fn needle_of(target_path: &str) -> Option<String> {
    normalize_path(target_path).pop().map(|c| c.base)
}

// ---------------------------------------------------------------------------
// Orchestration: build covdriver, run the analysis pass, load fragments
// ---------------------------------------------------------------------------

/// Whether `VERUS_SPEC_CHECK_COVEXT_MIR=0` disables the manifest pass (targets
/// keep their plain LLVM-tier reasons).
fn mir_disabled() -> bool {
    matches!(std::env::var("VERUS_SPEC_CHECK_COVEXT_MIR"), Ok(v) if v == "0")
}

/// Defuse compiler diagnostics before embedding them in OUR diagnostic
/// strings: downstream tooling (including this repo's own fixture
/// harness) greps combined test output for build-failure markers
/// (`could not compile`, `error[...]`), and a verbatim quoted child
/// build error makes a perfectly healthy test run look like a fixture
/// build failure.
pub(crate) fn sanitize_compiler_output(s: &str) -> String {
    s.replace("error[", "error(")
        .replace("could not compile", "could not build")
}

/// Stable hash of the needle set — keys the manifest cache: cargo's
/// incremental check reruns rustc only for changed crates, so a changed
/// needle set must get a fresh target dir (otherwise cached crates
/// would silently emit no fragments for the new needles).
fn needles_key(needles: &BTreeSet<String>) -> String {
    // The "v3" salt keys the manifest FORMAT and orphans every keyed
    // dir written before the cold-rebuild rule below (regenerations
    // over a warm cargo cache produced silently incomplete manifests —
    // fragments exist only for crates rustc actually recompiled).
    let joined = needles
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join("\n");
    crate::cov_fuzz::covext_target_file_key(&format!("v3-arm-spans\n{joined}"))
}

/// Content the completion stamp must carry: a fingerprint of the DRIVER
/// that wrote the fragments. Mtime comparison is not enough — a stamp
/// and a rebuilt driver can share a timestamp (observed at
/// minute-granularity), silently validating fragments from an older
/// driver version.
fn driver_fingerprint(driver: &Path) -> String {
    let meta = driver.metadata().ok();
    let len = meta.as_ref().map(|m| m.len()).unwrap_or(0);
    let mtime = meta
        .and_then(|m| m.modified().ok())
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    format!("driver:{len}:{mtime}")
}

/// Build (once) and locate the covdriver binary. The sources live next
/// to this crate in the verus-spec-check checkout — resolvable for path-dep
/// consumers (the vstd overlay); a registry consumer degrades with an
/// explanatory reason.
pub(crate) fn covdriver_binary(
    scratch: &Path,
    nightly_rustc: &Path,
    nightly_cargo: &mut dyn FnMut(&str) -> Command,
) -> Result<PathBuf, String> {
    let covdriver_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../covdriver");
    if !covdriver_dir.join("Cargo.toml").is_file() {
        return Err(format!(
            "covdriver sources not found at {} (MIR manifests need the \
             verus-spec-check checkout)",
            covdriver_dir.display()
        ));
    }
    let target_dir = scratch.join("covdriver-build");
    let binary = target_dir.join("debug/verus-spec-check-covdriver");
    // ALWAYS build: cargo's incremental no-op costs ~a second, while an
    // exists-check would silently keep serving a STALE driver after its
    // sources change — which then writes old-format manifest fragments
    // under a fresh stamp (observed: fragments without arm spans).
    if !binary.is_file() {
        crate::cov_fuzz_ext::progress(
            "verus_spec_check cov_fuzz: building the MIR manifest driver (nightly + \
             rustc-dev) — first run only",
        );
    }
    let out = nightly_cargo("cargo")
        .args(["build", "--manifest-path"])
        .arg(covdriver_dir.join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", &target_dir)
        // The driver builds against rustc_private on the NIGHTLY
        // toolchain; inherited pins/flags from the outer build are for
        // the outer toolchain. RUSTC is PINNED to the probed nightly's
        // own compiler: `rustup run nightly cargo` otherwise resolves
        // `rustc` from PATH, and in shadowed-PATH environments (nix dev
        // shells, wrapper setups) that is a STABLE compiler which
        // rejects `#![feature(rustc_private)]` (E0554).
        .env("RUSTC", nightly_rustc)
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTC_WRAPPER")
        .output()
        .map_err(|e| format!("spawn nightly cargo for covdriver: {e}"))?;
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        return Err(format!(
            "covdriver build failed (needs the nightly `rustc-dev` component: \
             `rustup component add rustc-dev --toolchain nightly`):\n{}",
            sanitize_compiler_output(&crate::cov_fuzz_ext::tail_of(&stderr, 10))
        ));
    }
    if binary.is_file() {
        Ok(binary)
    } else {
        Err("covdriver build produced no binary".to_string())
    }
}

/// Produce (or reuse) the MIR manifest for `crate_dir` covering
/// `needles`, and load its entries. The analysis pass is one
/// `cargo check -Z build-std` with covdriver as `RUSTC_WRAPPER`; its
/// fragments are cached under a needle-set-keyed directory and stamped
/// on completion, so repeated audits skip the pass entirely.
pub(crate) fn mir_entries(
    crate_dir: &str,
    host: &str,
    nightly_rustc: &Path,
    nightly_sysroot: &Path,
    nightly_cargo: &mut dyn FnMut(&str) -> Command,
    needles: &BTreeSet<String>,
) -> Result<Vec<MirEntry>, String> {
    if mir_disabled() {
        return Err("disabled via VERUS_SPEC_CHECK_COVEXT_MIR=0".to_string());
    }
    if needles.is_empty() {
        return Err("no needles derived from target paths".to_string());
    }
    let scratch = crate::cov_fuzz_ext::scratch_base_of(crate_dir).join("verus-spec-check-covext-mir");
    let key = needles_key(needles);
    let keyed = scratch.join(&key);
    let out_dir = keyed.join("manifests");
    let stamp = keyed.join("manifest-complete.stamp");

    // The driver is (re)built first so the stamp can be validated
    // against it: the stamp records the exact driver fingerprint that
    // wrote the fragments, and fragments from any OTHER driver build
    // are regenerated rather than trusted (they may predate the current
    // manifest format).
    let driver = covdriver_binary(&scratch, nightly_rustc, nightly_cargo)?;
    let expected_stamp = driver_fingerprint(&driver);
    let stamp_is_fresh = std::fs::read_to_string(&stamp)
        .map(|content| content == expected_stamp)
        .unwrap_or(false);

    // Opt-in scratch pruning (`VERUS_SPEC_CHECK_COV_PRUNE=1`): remove SIBLING
    // keyed dirs whose stamp does not match the current driver
    // fingerprint — stale needle sets and old driver versions, each
    // ~1 GiB of reproducible cargo cache. Opt-in because concurrent
    // report processes may legitimately be using a different needle
    // set; the audit script (a single campaign process) enables it.
    if matches!(std::env::var("VERUS_SPEC_CHECK_COV_PRUNE"), Ok(v) if !v.is_empty() && v != "0") {
        if let Ok(dir) = std::fs::read_dir(&scratch) {
            for item in dir.flatten() {
                let path = item.path();
                if !path.is_dir() || path == keyed || path.ends_with("covdriver-build") {
                    continue;
                }
                let sibling_stamp = path.join("manifest-complete.stamp");
                let fresh = std::fs::read_to_string(&sibling_stamp)
                    .map(|content| content == expected_stamp)
                    .unwrap_or(false);
                if !fresh {
                    crate::cov_fuzz_ext::progress(&format!(
                        "verus_spec_check cov_fuzz: pruning stale MIR scratch {}",
                        path.display()
                    ));
                    let _ = std::fs::remove_dir_all(&path);
                }
            }
        }
    }

    if !stamp_is_fresh {
        let _ = std::fs::remove_dir_all(&out_dir);
        let _ = std::fs::remove_file(&stamp);
        // The keyed CARGO TARGET DIR must go too: fragments are emitted
        // only when rustc actually RUNS for a crate, and an incremental
        // re-check skips every unchanged crate — regenerating fragments
        // over a warm cache silently yields a manifest missing
        // core/alloc/std (observed). Full recheck costs minutes, but a
        // silently incomplete manifest mis-resolves every std target.
        let _ = std::fs::remove_dir_all(keyed.join("target"));
        std::fs::create_dir_all(&out_dir).map_err(|e| format!("create {out_dir:?}: {e}"))?;
        let needles_file = keyed.join("needles.txt");
        let joined = needles
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(&needles_file, joined)
            .map_err(|e| format!("write {needles_file:?}: {e}"))?;

        crate::cov_fuzz_ext::progress(
            "verus_spec_check cov_fuzz: building the MIR branch manifest \
             (cargo check -Z build-std under covdriver) — cached per needle set",
        );
        let out = nightly_cargo("cargo")
            .args(["check", "--lib", "-Z", "build-std", "--target", host])
            .current_dir(crate_dir)
            .env("CARGO_TARGET_DIR", keyed.join("target"))
            .env("RUSTC_WRAPPER", &driver)
            .env("VERUS_SPEC_CHECK_COVDRIVER_OUT", &out_dir)
            .env("VERUS_SPEC_CHECK_COVDRIVER_NEEDLES", &needles_file)
            .env("VERUS_SPEC_CHECK_COVDRIVER_SYSROOT", nightly_sysroot)
            // The wrapper IS the nightly compiler; outer pins would
            // fight it (same rationale as the instrumented side builds).
            .env_remove("RUSTC")
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env("VERUS_SPEC_CHECK_COV_FUZZ_EXT_INNER", "1")
            .output()
            .map_err(|e| format!("spawn nightly cargo for the MIR manifest pass: {e}"))?;
        if !out.status.success() {
            let stderr = String::from_utf8_lossy(&out.stderr);
            return Err(format!(
                "MIR manifest pass failed:\n{}",
                sanitize_compiler_output(&crate::cov_fuzz_ext::tail_of(&stderr, 12))
            ));
        }
        std::fs::write(&stamp, &expected_stamp).map_err(|e| format!("write {stamp:?}: {e}"))?;
    }

    load_entries(&out_dir)
}

/// Parse every manifest fragment in `out_dir`. Fail-closed: a malformed
/// fragment is an error, not a silent skip — a truncated manifest must
/// not quietly reclassify targets.
fn load_entries(out_dir: &Path) -> Result<Vec<MirEntry>, String> {
    let mut entries = Vec::new();
    let dir = std::fs::read_dir(out_dir).map_err(|e| format!("read {out_dir:?}: {e}"))?;
    for item in dir {
        let path = item.map_err(|e| format!("read {out_dir:?}: {e}"))?.path();
        if path.extension().map(|e| e != "json").unwrap_or(true) {
            continue;
        }
        let text = std::fs::read_to_string(&path).map_err(|e| format!("read {path:?}: {e}"))?;
        let value: serde_json::Value = serde_json::from_str(&text)
            .map_err(|e| format!("malformed manifest fragment {path:?}: {e}"))?;
        let crate_name = value["crate"]
            .as_str()
            .ok_or_else(|| format!("manifest fragment {path:?} missing `crate`"))?;
        let list = value["entries"]
            .as_array()
            .ok_or_else(|| format!("manifest fragment {path:?} missing `entries`"))?;
        for entry in list {
            let def_path = entry["def_path"]
                .as_str()
                .ok_or_else(|| format!("manifest fragment {path:?} entry missing `def_path`"))?;
            let arms = entry["branch_arms"]
                .as_u64()
                .ok_or_else(|| format!("manifest fragment {path:?} entry missing `branch_arms`"))?;
            // Flatten per-switch arm spans in order. Parse failures are
            // fail-closed at the CONSUMER (arm witnessing requires
            // exactly `arms` parsed spans), not silently dropped here.
            let mut arm_spans = Vec::new();
            if let Some(switches) = entry["switches"].as_array() {
                for switch in switches {
                    if let Some(spans) = switch["arm_spans"].as_array() {
                        for span in spans {
                            if let Some(parsed) = span.as_str().and_then(MirArmSpan::parse) {
                                arm_spans.push(parsed);
                            }
                        }
                    }
                }
            }
            entries.push(MirEntry {
                full_path: format!("{crate_name}::{def_path}"),
                branch_arms: arms,
                arm_spans,
            });
        }
    }
    if entries.is_empty() {
        return Err(format!(
            "MIR manifest at {} contains no entries",
            out_dir.display()
        ));
    }
    Ok(entries)
}

// ---------------------------------------------------------------------------
// Tests: matching against def-path shapes captured from the pinned
// nightly (the covdriver smoke fixtures) and the vstd target spellings
// from the campaign logs.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(full_path: &str, arms: u64) -> MirEntry {
        MirEntry {
            full_path: full_path.to_string(),
            branch_arms: arms,
            arm_spans: Vec::new(),
        }
    }

    #[test]
    fn arm_span_parsing_handles_diagnostic_strings() {
        let s = MirArmSpan::parse(
            "/Users/x/.rustup/lib/rustlib/src/rust/library/core/src/option.rs:643:9: 643:15",
        )
        .expect("parses");
        assert_eq!(s.line, 643);
        assert_eq!(s.col, 9);
        assert!(s.file.ends_with("core/src/option.rs"));
        // Relative path form.
        let s = MirArmSpan::parse("src/lib.rs:5:8: 5:15").expect("parses");
        assert_eq!((s.line, s.col), (5, 8));
        assert_eq!(s.file, "src/lib.rs");
        // Garbage stays None.
        assert!(MirArmSpan::parse("no-span-here").is_none());
        assert!(MirArmSpan::parse("").is_none());
    }

    /// The manifest corpus: real def-path shapes observed from the
    /// covdriver build-std smoke run.
    fn corpus() -> Vec<MirEntry> {
        vec![
            entry("core::num::<impl i64>::checked_add", 2),
            entry("core::num::<impl i8>::checked_add", 2),
            entry("core::num::nonzero::NonZero::<u8>::checked_add", 3),
            entry("core::clone::impls::<impl clone::Clone for i8>::clone", 0),
            entry("core::clone::impls::<impl clone::Clone for i64>::clone", 0),
            entry(
                "core::num::imp::bignum::<impl clone::Clone for Big32x40>::clone",
                0,
            ),
            entry("core::option::Option::<T>::is_some", 3),
            entry("core::mem::swap", 0),
            entry("core::slice::<impl [T]>::first", 2),
            entry("alloc::vec::Vec::<T>::new", 0),
            entry("alloc::vec::Vec::<T, A>::push", 4),
            entry("alloc::vec::Vec::<T, A>::is_empty", 0),
            entry("alloc::<vec::Vec<T, A> as core::ops::Deref>::deref", 0),
            entry("alloc::<vec::Vec<T> as core::default::Default>::default", 0),
            entry("alloc::raw_vec::RawVec::<T>::new", 0),
            entry("alloc::rc::Rc::<T>::new", 0),
            entry("alloc::sync::Arc::<T>::new", 2),
            entry("core::char::methods::<impl char>::len_utf8", 4),
            entry("std::collections::hash::map::HashMap::<K, V>::new", 0),
        ]
    }

    #[test]
    fn primitive_clone_resolves_branchless() {
        assert_eq!(
            resolve("<i8 as Clone>::clone", &corpus()),
            MirResolution::Branchless {
                def_path: "core::clone::impls::<impl clone::Clone for i8>::clone".into()
            }
        );
        assert_eq!(
            resolve("<i64 as Clone>::clone", &corpus()),
            MirResolution::Branchless {
                def_path: "core::clone::impls::<impl clone::Clone for i64>::clone".into()
            }
        );
    }

    #[test]
    fn qualified_primitive_inherent_resolves_and_rejects_lookalikes() {
        // `<i64>::checked_add` must match the primitive inherent impl,
        // NOT `NonZero::<u8>::checked_add`.
        assert_eq!(
            resolve("<i64>::checked_add", &corpus()),
            MirResolution::Branches {
                def_path: "core::num::<impl i64>::checked_add".into(),
                arms: 2,
                arm_spans: vec![]
            }
        );
    }

    #[test]
    fn container_paths_resolve() {
        assert_eq!(
            resolve("Vec::<T,A>::push", &corpus()),
            MirResolution::Branches {
                def_path: "alloc::vec::Vec::<T, A>::push".into(),
                arms: 4,
                arm_spans: vec![]
            }
        );
        // `Vec::<T>::new` must match `vec::Vec`, not `raw_vec::RawVec`.
        assert_eq!(
            resolve("Vec::<T>::new", &corpus()),
            MirResolution::Branchless {
                def_path: "alloc::vec::Vec::<T>::new".into()
            }
        );
        assert_eq!(
            resolve("Rc::<T>::new", &corpus()),
            MirResolution::Branchless {
                def_path: "alloc::rc::Rc::<T>::new".into()
            }
        );
        assert_eq!(
            resolve("Arc::<T>::new", &corpus()),
            MirResolution::Branches {
                def_path: "alloc::sync::Arc::<T>::new".into(),
                arms: 2,
                arm_spans: vec![]
            }
        );
        assert_eq!(
            resolve("HashMap::<Key,Value>::new", &corpus()),
            MirResolution::Branchless {
                def_path: "std::collections::hash::map::HashMap::<K, V>::new".into()
            }
        );
    }

    #[test]
    fn trait_impls_resolve_and_kinds_do_not_cross() {
        assert_eq!(
            resolve("<Vec<T,A> as core::ops::Deref>::deref", &corpus()),
            MirResolution::Branchless {
                def_path: "alloc::<vec::Vec<T, A> as core::ops::Deref>::deref".into()
            }
        );
        assert_eq!(
            resolve("<Vec<T> as core::default::Default>::default", &corpus()),
            MirResolution::Branchless {
                def_path: "alloc::<vec::Vec<T> as core::default::Default>::default".into()
            }
        );
        // An inherent target must not match a trait-impl def.
        assert_eq!(resolve("i8::clone", &corpus()), MirResolution::Unresolved);
    }

    #[test]
    fn slices_free_fns_and_char_resolve() {
        assert_eq!(
            resolve("<[T]>::first", &corpus()),
            MirResolution::Branches {
                def_path: "core::slice::<impl [T]>::first".into(),
                arms: 2,
                arm_spans: vec![]
            }
        );
        assert_eq!(
            resolve("core::mem::swap::<T>", &corpus()),
            MirResolution::Branchless {
                def_path: "core::mem::swap".into()
            }
        );
        assert_eq!(
            resolve("Option::<T>::is_some", &corpus()),
            MirResolution::Branches {
                def_path: "core::option::Option::<T>::is_some".into(),
                arms: 3,
                arm_spans: vec![]
            }
        );
        assert_eq!(
            resolve("char::len_utf8", &corpus()),
            MirResolution::Branches {
                def_path: "core::char::methods::<impl char>::len_utf8".into(),
                arms: 4,
                arm_spans: vec![]
            }
        );
    }

    #[test]
    fn unknown_targets_stay_unresolved() {
        assert_eq!(
            resolve("BTreeMap::<Key,Value>::new", &corpus()),
            MirResolution::Unresolved
        );
        assert_eq!(resolve("", &corpus()), MirResolution::Unresolved);
    }

    #[test]
    fn disagreeing_duplicates_are_ambiguous() {
        let entries = vec![entry("a::Widget::step", 0), entry("b::Widget::step", 3)];
        let MirResolution::Ambiguous { candidates } = resolve("Widget::step", &entries) else {
            panic!("disagreeing duplicates must be ambiguous");
        };
        assert_eq!(candidates.len(), 2);
        // Agreeing branchy duplicates resolve to the widest inventory.
        let agree = vec![entry("a::Widget::step", 2), entry("b::Widget::step", 3)];
        assert_eq!(
            resolve("Widget::step", &agree),
            MirResolution::Branches {
                def_path: "b::Widget::step".into(),
                arms: 3,
                arm_spans: vec![]
            }
        );
    }

    #[test]
    fn needles_are_final_segments() {
        assert_eq!(needle_of("Vec::<T,A>::push").as_deref(), Some("push"));
        assert_eq!(needle_of("<i8 as Clone>::clone").as_deref(), Some("clone"));
        assert_eq!(needle_of("core::mem::swap::<T>").as_deref(), Some("swap"));
        assert_eq!(needle_of("<[T]>::first").as_deref(), Some("first"));
    }
}
