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
| `ci.yml` | push to `main` / PR / manual | **tiered.** push+manual: quick checks (overlay reproducibility, pin consistency, workspace build, engine tests, snippet-suite harness tier). PR: the above plus the heavy Verus work (fetch pinned Verus, snippet-suite verify tier, crates.io-only packaging path). Docs-only PRs skip the heavy tier |
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

Almost always upstream drifted a file the overlay patches (the resync step in
CI fails). To fix, on the PR branch:

1. Run `tools/release/overlay-resync.sh <new-version>`; note which patch failed.
2. Hand-edit `source/builtin_macros_overlay/src` so it compiles against the new
   upstream.
3. `tools/release/overlay-regen-patches.sh <new-version>` to rebuild the assets
4. Commit and push. CI will re-validate

The other red case is `verus_syn` AST drift breaking the engine. Same idea, fix
`source/engine` (and the split crates) on the branch.

Also, Verus's Rust version bumps need to be manually accounted for.

## If `vstd::contrib::exec_spec/*` changed

Diff the old and new vstd source for `contrib/exec_spec/`:

```bash
diff -r ~/.cargo/registry/src/*/vstd-0.0.0-OLD-DATE/contrib/exec_spec \
        ~/.cargo/registry/src/*/vstd-0.0.0-NEW-DATE/contrib/exec_spec
```

If there are changes, port them into `source/vstd_ext/src/exec_spec/`. The
import-pattern rewrites stay the same:

- `crate::contrib::exec_spec::*` -> `crate::exec_spec::*`
- `crate::prelude::*` -> `vstd::prelude::*`
- `crate::multiset::*` -> `vstd::multiset::*`
- `crate::group_vstd_default` -> `vstd::group_vstd_default`
- `crate::std_specs::hash::*` -> `vstd::std_specs::hash::*`

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
