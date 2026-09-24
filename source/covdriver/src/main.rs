//! `verus-spec-check-covdriver`: a `RUSTC_WRAPPER` that behaves exactly like
//! rustc while additionally emitting a MIR BRANCH MANIFEST for the
//! crates it compiles.
//!
//! ## Why this exists
//!
//! External `#[vcheck_cov_fuzz]` targets (`assume_specification` wrappers
//! over std/core/dependency functions) are currently identified by
//! matching demangled function names in `llvm-cov` output — evidence
//! reconstructed AFTER codegen, where inlining routinely erases the
//! function record entirely (`Option::is_some`, `Vec::push`, primitive
//! `Clone::clone` all vanished in the vstd audit). This driver reads
//! the same functions BEFORE codegen, where they still exist:
//!
//! - resolves each function by compiler def-path (survives inlining,
//!   generics, and monomorphization by construction);
//! - enumerates its MIR branch terminators (`SwitchInt`) into a stable
//!   arm inventory with source spans;
//! - classifies zero-terminator bodies as BRANCHLESS — the class of
//!   false "unavailable" strict failures (`<i8 as Clone>::clone`,
//!   `Vec::new`, `default`) that have nothing to measure.
//!
//! The manifest is consumed by `verus_spec_check_runtime::cov_fuzz_ext` to
//! classify targets; measurement itself still comes from the
//! instrumented side profiles.
//!
//! ## Protocol
//!
//! Invoked by cargo as `RUSTC_WRAPPER`: `covdriver <real-rustc> <args...>`.
//! It drops the real-rustc argument and runs `rustc_driver` in process
//! (the driver IS this toolchain's rustc). Plain behavior is exactly
//! rustc's; the manifest callback only does work when both env knobs
//! are present:
//!
//! - `VERUS_SPEC_CHECK_COVDRIVER_OUT`      — directory manifest fragments are
//!   written into (one JSON file per analyzed crate);
//! - `VERUS_SPEC_CHECK_COVDRIVER_NEEDLES`  — file listing final-path-segment
//!   needles (one per line, e.g. `push`, `checked_add`); only defs whose
//!   def-path ends in a needle are inventoried, keeping fragments small.
//!   Precise target matching happens in the consumer.
//! - `VERUS_SPEC_CHECK_COVDRIVER_SYSROOT`  — appended as `--sysroot` when the
//!   invocation has none (this binary does not live in the toolchain,
//!   so rustc's own sysroot inference would fail).
//!
//! Proc-macro crates and build scripts are skipped (their MIR is host
//! plumbing, never a measured target).
//!
//! ## Arm inventory semantics
//!
//! Arms are enumerated from `optimized_mir` — the same MIR codegen
//! consumes — so the denominator is "branch arms in the artifact", not
//! "branch-looking syntax in the source". A body whose branches were
//! optimized away IS branchless for coverage purposes: there is nothing
//! left to reach. Each `SwitchInt` contributes `all_targets().len()`
//! arms (the `otherwise` edge included).
//!
//! ## No-MIR-inline mode (`VERUS_SPEC_CHECK_COVDRIVER_NO_MIR_INLINE=1`)
//!
//! The instrumented side builds lose llvm-cov function records to MIR
//! inlining: a matched std function inlined at every call site is never
//! codegened standalone, so `-C instrument-coverage` has no record to
//! attribute its execution to — the root cause of every
//! "no coverage records matched" strict failure on branchy targets.
//! In this mode the driver appends `-Z inline-mir=no` to every
//! compilation EXCEPT `compiler_builtins`, so each caller crate
//! codegens its own instance of the callee with its own coverage
//! mapping (side builds run at opt-level 0, so LLVM does not re-lose
//! them).
//!
//! Why a per-crate flag and not `InlineAttr::Never` via a
//! `codegen_fn_attrs` override: forcing `never` is ENCODED into the
//! callee crate's metadata, and `compiler_builtins` — which must not
//! call upstream monomorphizations — then fails to compile ("cannot
//! call functions through upstream monomorphizations") because it can
//! no longer MIR-inline `core`'s integer helpers. `-Z inline-mir=no`
//! is a CONSUMER-side pass toggle: nothing changes in metadata, and
//! `compiler_builtins` keeps its default (inlining) behavior.
//!
//! Semantics note: this changes PERFORMANCE of the measured build, not
//! behavior — the same trade `-C instrument-coverage` already makes.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::path::{Path, PathBuf};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty::TyCtxt;

struct CovManifest {
    out_dir: Option<PathBuf>,
    needles: Vec<String>,
}

impl Callbacks for CovManifest {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if let Some(out_dir) = &self.out_dir {
            if !self.needles.is_empty() {
                emit_manifest(tcx, out_dir, &self.needles);
            }
        }
        Compilation::Continue
    }
}

/// The `--crate-name` value of this invocation, if present.
fn crate_name_arg(args: &[String]) -> Option<&str> {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--crate-name" {
            return iter.next().map(String::as_str);
        }
        if let Some(name) = arg.strip_prefix("--crate-name=") {
            return Some(name);
        }
    }
    None
}

/// Final path segment of a def-path string, generic args stripped:
/// `alloc::vec::Vec::<T, A>::push` -> `push`,
/// `<alloc::vec::Vec<T, A> as Deref>::deref` -> `deref`.
fn last_segment(def_path: &str) -> &str {
    let tail = def_path.rsplit("::").next().unwrap_or(def_path);
    tail.split('<').next().unwrap_or(tail).trim_end_matches('>')
}

fn emit_manifest(tcx: TyCtxt<'_>, out_dir: &Path, needles: &[String]) {
    // Never inventory host plumbing.
    if tcx
        .crate_types()
        .iter()
        .any(|t| matches!(t, rustc_session::config::CrateType::ProcMacro))
    {
        return;
    }
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    if crate_name.as_str().starts_with("build_script") {
        return;
    }

    let mut entries: Vec<serde_json::Value> = Vec::new();
    for local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let def_path = tcx.def_path_str(def_id);
        if !needles.iter().any(|n| last_segment(&def_path) == n) {
            continue;
        }
        if !tcx.is_mir_available(def_id) {
            continue;
        }
        let body = tcx.optimized_mir(def_id);
        let source_map = tcx.sess.source_map();
        let mut arms: Vec<serde_json::Value> = Vec::new();
        let mut arm_count: u64 = 0;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let Some(terminator) = &data.terminator else {
                continue;
            };
            let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind else {
                continue;
            };
            // Per-arm TARGET spans: the span of each successor block's
            // first statement (or its terminator when statement-less).
            // These are the anchors the consumer maps against llvm-cov
            // REGION records to witness arm execution — match-based
            // bodies get no llvm "branches" records, but every arm body
            // is its own counted region.
            //
            // An `otherwise` edge into a bare `unreachable` block (the
            // lowering of an exhaustive match's impossible default) is
            // NOT a real arm: it cannot execute by construction, so it
            // is excluded from both the arm count and the spans —
            // counting it would make every exhaustive match one arm
            // short forever.
            let arm_spans: Vec<String> = targets
                .all_targets()
                .iter()
                .filter(|&&succ| {
                    let target_block = &body.basic_blocks[succ];
                    !(target_block.statements.is_empty()
                        && matches!(
                            target_block.terminator.as_ref().map(|t| &t.kind),
                            Some(TerminatorKind::Unreachable)
                        ))
                })
                .map(|&succ| {
                    let target_block = &body.basic_blocks[succ];
                    let span = target_block
                        .statements
                        .first()
                        .map(|s| s.source_info.span)
                        .or_else(|| {
                            target_block
                                .terminator
                                .as_ref()
                                .map(|t| t.source_info.span)
                        })
                        .unwrap_or(terminator.source_info.span);
                    source_map.span_to_diagnostic_string(span)
                })
                .collect();
            let successors = arm_spans.len() as u64;
            arm_count += successors;
            arms.push(serde_json::json!({
                "block": block.as_u32(),
                "successors": successors,
                "span": source_map.span_to_diagnostic_string(terminator.source_info.span),
                "arm_spans": arm_spans,
            }));
        }
        entries.push(serde_json::json!({
            "def_path": def_path,
            "branch_arms": arm_count,
            "branchless": arm_count == 0,
            "switches": arms,
        }));
    }
    if entries.is_empty() {
        return;
    }

    let fragment = serde_json::json!({
        "crate": crate_name.as_str(),
        "entries": entries,
    });
    // One fragment per (crate, stable id): distinct versions of one
    // crate name in the graph write distinct files.
    let stable_id = tcx.stable_crate_id(rustc_hir::def_id::LOCAL_CRATE);
    let file = out_dir.join(format!(
        "{}-{:016x}.json",
        crate_name.as_str(),
        stable_id.as_u64(),
    ));
    let _ = std::fs::create_dir_all(out_dir);
    let _ = std::fs::write(&file, fragment.to_string());
}

fn read_needles(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path)
        .map(|text| {
            text.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .map(str::to_string)
                .collect()
        })
        .unwrap_or_default()
}

fn main() -> std::process::ExitCode {
    let mut args: Vec<String> = std::env::args().collect();
    // RUSTC_WRAPPER protocol: argv[1] is the real rustc path; drop it —
    // rustc_driver below IS this toolchain's rustc.
    if args.len() > 1 {
        let arg1 = Path::new(&args[1]);
        if arg1
            .file_stem()
            .map(|s| s == "rustc" || s.to_string_lossy().starts_with("rustc"))
            .unwrap_or(false)
        {
            args.remove(1);
        }
    }
    // This binary does not live in the toolchain, so rustc's sysroot
    // inference (relative to the executable) fails; the orchestrator
    // provides the toolchain sysroot explicitly.
    let has_sysroot = args
        .iter()
        .any(|a| a == "--sysroot" || a.starts_with("--sysroot="));
    if !has_sysroot {
        if let Ok(sysroot) = std::env::var("VERUS_SPEC_CHECK_COVDRIVER_SYSROOT") {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }
    }

    // No-MIR-inline mode: keep matched (and all other) fns codegened as
    // per-crate instances so their coverage records survive. Never
    // applied to `compiler_builtins`, which REQUIRES MIR inlining of
    // core's helpers (see module docs).
    let no_mir_inline = matches!(
        std::env::var("VERUS_SPEC_CHECK_COVDRIVER_NO_MIR_INLINE"),
        Ok(v) if !v.is_empty() && v != "0"
    );
    if no_mir_inline && crate_name_arg(&args) != Some("compiler_builtins") {
        args.push("-Zinline-mir=no".to_string());
    }

    let out_dir = std::env::var_os("VERUS_SPEC_CHECK_COVDRIVER_OUT").map(PathBuf::from);
    let needles = std::env::var_os("VERUS_SPEC_CHECK_COVDRIVER_NEEDLES")
        .map(|p| read_needles(Path::new(&p)))
        .unwrap_or_default();
    let mut callbacks = CovManifest { out_dir, needles };

    rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callbacks))
}
