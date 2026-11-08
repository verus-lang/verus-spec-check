# CI and Release automation

Verus has [many releases](https://github.com/verus-lang/verus/releases), and
Verus-verified projects tend to adopt a specific version and stick with it for some time
before bumping. Hence, there should be a compatible version of `verus-spec-check` for each version
of Verus. Verus cuts a release from its CI at the end of every week, and the CI of `verus-spec-check`
is designed to follow and cut an associated release with the same version name.

To make usage easier, `verus-spec-check` packs the associated Verus version as a binary using a Nix flake.

## Model

The release has two independent upstream versions because Verus can publish a new binary
without publishing a new vstd crate:

- `flake.nix`'s `verusVersion` is the release identity. Its date determines the
  `verus-<date>` tag.
- `workspace.package.version` and the dependency manifests use the newest complete
  `vstd`/`verus_builtin_macros` crates.io line no newer than that Verus release. This
  line can retain an older date when vstd did not change.

Tags are the primary release artifact. Every crate in `verus-spec-check` is packaged under the
selected Verus binary's tag.

## Workflows

| Workflow | Trigger | Does |
|---|---|---|
| `ci.yml` | push to `main` / PR / manual | **tiered.** push+manual: quick checks (overlay reproducibility, pin consistency, workspace build, unit tests, snippet-suite harness tier). PR: the above plus the heavy Verus work (fetch pinned Verus, snippet-suite verify tier, and `tools/check_git_install.sh`, which installs the PR commit as a git dependency the way the README describes). Docs-only PRs skip the heavy tier |
| `update.yml` | Mon+Tue cron, manual | `sync-verus.sh latest` -> opens a PR for the newest Verus binary, independently retaining or updating the vstd line |
| `release.yml` | manual, or push to `main` touching root `Cargo.toml` or `flake.nix` | if the Verus binary date isn't tagged yet, tag `verus-<date>`, move `latest`, create a GitHub release |
| `backfill.yml` | manual (version input) | sync to an older same-date Verus/vstd line, validate, and tag `verus-<date>` |

Flow: `update.yml` opens a bump PR -> CI validates it -> merge -> `release.yml`
tags it. No auto-merge.

## What validates what

The end-to-end gate is `source/vcheck_test` (`cargo test -p verus_spec_check_test`): each
feature is an inline code snippet with its expected outcome declared next to it
(`=> HarnessOutcome::Pass { harnesses: n }`, `=> FailsHarness`, `=> Verifies`),
in the style of verus's own `rust_verify_test`. Cases share one target dir per
mode, so the heavy dependencies (vstd, verus_syn) compile once instead of once
per case.

Two tiers, matching CI:

```bash
cargo test -p verus_spec_check_test -- --skip verify_   # harness only; no Verus needed
nix develop --command cargo test -p verus_spec_check_test   # + the verify_* cases
```

CI no longer sweeps the example crates. Those sweeps rebuilt the whole
dependency stack once per example (one target dir each, which is what was
OOM-killing the runner), and every feature they covered is now a snippet case.
`examples/` is documentation you can run by hand — see `examples/README.md`.
To sweep them locally, `tools/run_examples.sh` (harnesses) and
`tools/verify_examples.sh` (Verus verification) take optional example names
and default to all when given none.

## Scripts (`tools/release/`)

- `sync-verus.sh <crate-version|latest>`: the orchestrator. In `latest` mode,
  selects the newest Verus binary first, then the newest complete vstd/macros
  line on or before its date. It re-syncs the overlay and dependency pins only
  when that crate line changes, and always bumps the flake when the selected
  binary changes. Explicit versions retain same-date backfill behavior. Exit 3
  = no-op.
- `overlay-resync.sh <version>`: rebuilds `source/builtin_macros_overlay` with respect
  to the `contrib::hooks` seam. The manifest is derived from upstream's own `Cargo.toml`.
- `overlay-regen-patches.sh <version>`: designed to fix the deltas on the overlay after
  upstream for `source/builtin_macros_overlay` is broken, and a hand-fix is applied
- `flake-bump.sh |latest|--date|--`: updates `flake.nix`'s `verusVersion` and pre-fetches
   per-arch zip hashes, similar to the behavior of [verus-flake](https://github.com/JakeGinesin/verus-flake/blob/master/flake.nix)

## When the weekly PR is red

verus-spec-check uses upstream's `vstd` and `exec_spec` as-is, and the overlay's
`src/` is stock upstream (the `contrib::hooks` seam is upstream, so no patches
apply). The usual red case is upstream changing the exec_spec or vstd API that
the generated harness code relies on. For example, 2026-11-01 replaced
`ExecSpecEq` with `ObeysDeepEq` and stopped deriving `Debug` on `Exec*` types.
To fix, on the PR branch:

1. Fix `source/expand` (or `source/engine` and the other split crates) so the
   generated code compiles against the new upstream.
2. If the expansion changed, regenerate the snapshots with
   `UPDATE_VCHECK_SNAPSHOTS=1 cargo test -p verus_spec_check_engine --test expansion_snapshots`
   and review the diff.
3. Commit and push. CI will re-validate.

If the overlay reproducibility step fails instead, `overlay-resync.sh` prints
the reason. Reconcile it by hand in the script or the overlay. Don't run
`overlay-regen-patches.sh` against a seam-era release: it would delete the
`resync/` assets that pre-seam lines use.

The other red case is `verus_syn` AST drift breaking the engine. Same idea, fix
`source/engine` (and the split crates) on the branch.

Also, Verus's Rust version bumps need to be manually accounted for.

## Forked Helpers

Two files in `source/syntax/src/` (the `verus_spec_check_syntax` crate) are
forks of Verus internals. They MUST stay roughly in sync with their
upstream source.

When Verus releases a new `verus_syn` version that vcheck pins to:

1. Diff Verus's `syntax.rs::Vstd` against ours. Apply changes.
2. Diff Verus's `lib.rs::vstd_kind()` and `VstdKind` against ours.
   Apply changes.

## Known gotchas

- `[patch.crates-io]` only fires for crates.io entries: if your
  project path-deps a Verus crate (e.g. `vstd = { path = ... }`), the
  patch is silently skipped. Use registry deps in user projects.
