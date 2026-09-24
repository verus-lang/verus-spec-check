#!/usr/bin/env bash
# overlay-resync.sh <verus_builtin_macros-version>
#
# Re-syncs source/builtin_macros_overlay against a target upstream
# `verus_builtin_macros` release, applying the verus-spec-check overlay delta.
#
# The overlay is a surgical fork of stock `verus_builtin_macros`. The delta is:
#   - DELETE  src/contrib/exec_spec.rs      (engine logic lives externally)
#   - ADD     src/contrib/hooks.rs          (the contrib-hooks seam; verbatim)
#   - PATCH   src/lib.rs, src/contrib/mod.rs, src/rustdoc.rs
#   - REPLACE Cargo.toml                     (rendered from a template)
#   - (root files build.rs + contrib_hooks_provider.rs are overlay-owned and
#      untouched by this script.)
# re-running this script against the
# already-synced version produces a byte-identical tree.
#
# Requires: cargo, patch, standard coreutils. Intended to run on Linux CI or
# macOS dev.
set -euo pipefail

VERSION="${1:?usage: overlay-resync.sh <verus_builtin_macros-version>}"

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
# OVERLAY_DIR lets check_overlay.sh render into a scratch copy.
OVERLAY="${OVERLAY_DIR:-$REPO_ROOT/source/builtin_macros_overlay}"
RESYNC="$OVERLAY/resync"

if [ ! -d "$RESYNC" ]; then
  echo "FATAL: resync assets not found at $RESYNC" >&2
  exit 1
fi

echo "== overlay resync -> verus_builtin_macros $VERSION =="

# 1. Fetch pristine upstream source into the cargo registry cache.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cat > "$WORK/Cargo.toml" <<EOF
[package]
name = "fetch_bm"
version = "0.0.1"
edition = "2021"
[dependencies]
verus_builtin_macros = "=$VERSION"
[lib]
path = "src/lib.rs"
[workspace]
EOF
mkdir -p "$WORK/src"
touch "$WORK/src/lib.rs"
echo "-- fetching verus_builtin_macros=$VERSION"
( cd "$WORK" && cargo fetch --quiet )

# Locate the pristine source in the registry cache.
PRISTINE=""
for d in "$HOME"/.cargo/registry/src/*/"verus_builtin_macros-$VERSION"; do
  [ -d "$d" ] && PRISTINE="$d"
done
if [ -z "$PRISTINE" ]; then
  echo "FATAL: could not locate pristine verus_builtin_macros-$VERSION in registry cache" >&2
  exit 1
fi
echo "-- pristine source: $PRISTINE"

# 2. Replace the overlay src/ with pristine upstream src/.
rm -rf "$OVERLAY/src"
cp -r "$PRISTINE/src" "$OVERLAY/src"

# Seam detection: Verus releases from 2026-07-27 onward ship the
# `contrib::hooks` seam in stock verus_builtin_macros (hooks.rs, the
# `contrib-hooks` feature, and the preprocess calls in contrib/mod.rs are all
# upstream now — hooks.rs is byte-identical to what this overlay used to add).
# When the seam is upstream, the overlay needs NO contrib/ changes at all:
#   - don't add hooks.rs        (stock already has it)
#   - don't patch mod.rs        (stock already calls the hooks)
#   - don't delete exec_spec.rs (stock mod.rs declares it; it's dead code here
#     since lib.rs redirects the exec_spec entry points to the engine, but
#     removing it would force a mod.rs patch for no benefit)
# For pre-seam releases (2026-06-14 and older, incl. backfills) the seam
# assets below are still applied. Do NOT regen-away the seam assets while
# pre-seam lines remain supported.
SEAM_UPSTREAM=0
if [ -f "$PRISTINE/src/contrib/hooks.rs" ]; then
  SEAM_UPSTREAM=1
  echo "-- upstream ships the contrib::hooks seam; skipping seam-related delta"
fi

# 3. Delete the files the overlay drops (manifest-driven; comments/blank ok).
if [ -f "$RESYNC/manifest.txt" ]; then
  while IFS= read -r rel; do
    case "$rel" in ''|\#*) continue ;; esac
    if [ "$SEAM_UPSTREAM" -eq 1 ] && [ "$rel" = "src/contrib/exec_spec.rs" ]; then
      echo "-- keeping stock $rel (seam upstream; stock mod.rs declares it)"
      continue
    fi
    rm -f "$OVERLAY/$rel"
  done < "$RESYNC/manifest.txt"
fi

# 4. Copy overlay-owned added files in verbatim (files/ mirrors the crate
#    root). Skip any file pristine upstream already ships byte-identically
#    (e.g. hooks.rs once the seam is upstream); if upstream ships a DIFFERENT
#    version of a file we add, that's a conflict a human must resolve.
if [ -d "$RESYNC/files" ]; then
  while IFS= read -r f; do
    rel="${f#"$RESYNC/files/"}"
    if [ -f "$PRISTINE/$rel" ]; then
      if diff -q "$f" "$PRISTINE/$rel" >/dev/null 2>&1; then
        echo "-- skipping add of $rel (identical file is upstream now)"
        continue
      else
        echo "FATAL: upstream now ships $rel but it differs from our copy." >&2
        echo "       Upstream took ownership of this file and diverged;" >&2
        echo "       reconcile by hand and regenerate the assets." >&2
        exit 2
      fi
    fi
    mkdir -p "$OVERLAY/$(dirname "$rel")"
    cp "$f" "$OVERLAY/$rel"
  done < <(find "$RESYNC/files" -type f)
fi

# 5. Apply the patches against the freshly-copied upstream files.
#    --forward makes a re-run a no-op instead of prompting; any reject is a
#    hard failure so upstream drift surfaces loudly for a human.
for p in "$RESYNC/patches"/*.patch; do
  if [ "$SEAM_UPSTREAM" -eq 1 ] && [ "$(basename "$p")" = "src__contrib__mod.rs.patch" ]; then
    echo "-- skipping $(basename "$p") (seam upstream; stock mod.rs already calls hooks)"
    continue
  fi
  echo "-- applying $(basename "$p")"
  if ! patch -p1 --forward --no-backup-if-mismatch -d "$OVERLAY" < "$p"; then
    echo "FATAL: patch $(basename "$p") did not apply cleanly." >&2
    echo "       Upstream $VERSION changed a file the overlay patches." >&2
    echo "       Re-apply the delta by hand and regenerate the patch." >&2
    exit 2
  fi
done
# patch may leave .orig/.rej files behind on fuzz; fail if any .rej exist.
if find "$OVERLAY/src" -name '*.rej' | grep -q .; then
  echo "FATAL: reject files present after patching; overlay delta needs manual merge." >&2
  exit 2
fi
find "$OVERLAY/src" -name '*.orig' -delete

# 6. Derive the overlay Cargo.toml from upstream's own (normalized) manifest.
#    Taking upstream's manifest verbatim means new upstream dependencies
#    (e.g. convert_case, added 2026-07-27) and pin changes flow in
#    automatically — a hand-maintained template silently freezes one
#    version's dep list and breaks on the next. The overlay's delta is
#    exactly three mechanical edits:
#      a) build = "build.rs"        (wires VERUS_CONTRIB_HOOKS_FILE for the
#                                    contrib-hooks provider; overlay-owned)
#      b) ensure `contrib-hooks` feature exists (pre-seam upstreams lack it;
#                                    hooks.rs is gated on this feature)
#      c) append verus_spec_check_engine path-dep + standalone [workspace]
{
  echo "# THIS FILE IS DERIVED from upstream verus_builtin_macros $VERSION's"
  echo "# manifest by tools/release/overlay-resync.sh. Do not edit by hand:"
  echo "# re-run the resync. Overlay delta: build.rs wiring, the"
  echo "# contrib-hooks feature (if pre-seam), verus_spec_check_engine dep, [workspace]."
  cat "$PRISTINE/Cargo.toml"
} > "$OVERLAY/Cargo.toml"

# a) enable the overlay's build.rs (normalized manifests carry `build = false`).
perl -i -pe 's/^build = false$/build = "build.rs"/' "$OVERLAY/Cargo.toml"
if ! grep -q '^build = "build.rs"' "$OVERLAY/Cargo.toml"; then
  echo "FATAL: could not wire build.rs into the derived manifest" >&2
  exit 1
fi

# b) ensure the contrib-hooks feature exists (hooks.rs is feature-gated).
if ! grep -qE '^contrib-hooks\s*=' "$OVERLAY/Cargo.toml"; then
  if grep -q '^\[features\]' "$OVERLAY/Cargo.toml"; then
    perl -i -pe 's/^\[features\]$/[features]\ncontrib-hooks = []/' "$OVERLAY/Cargo.toml"
  else
    printf '\n[features]\ncontrib-hooks = []\n' >> "$OVERLAY/Cargo.toml"
  fi
fi

# c) the engine dep, dead_code suppression, and standalone-workspace marker.
cat >> "$OVERLAY/Cargo.toml" <<'EOF'

# --- verus-spec-check overlay additions (see header) -------------------------------
# The external engine. vcheck entry points and the contrib-hooks provider
# delegate here.
[dependencies.verus_spec_check_engine]
path = "../engine"

# On seam-era upstreams the stock contrib/exec_spec.rs is kept but
# unreachable (lib.rs redirects the exec_spec entry points to the engine),
# so dead_code would fire ~44 warnings on every downstream `cargo test`.
# Scoped to dead_code only; harmless on pre-seam lines where the file is
# deleted. Dead-code hygiene for the mirrored upstream code is upstream's
# concern.
[lints.rust]
dead_code = "allow"

# Standalone — not a member of the verus-spec-check workspace (its package name
# `verus_builtin_macros` would collide with the stock crate in the lockfile).
[workspace]
EOF

SYN_PIN="$(grep -A1 '\[dependencies.verus_syn\]' "$OVERLAY/Cargo.toml" | grep version | head -1 | tr -d ' "' )"
echo "== overlay resync complete: $VERSION (verus_syn ${SYN_PIN:-unknown}) =="
