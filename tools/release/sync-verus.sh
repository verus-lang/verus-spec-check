#!/usr/bin/env bash
# sync-verus.sh <crate-version | latest> [--skip-flake]
#
# Syncs the whole verus-spec-check workspace to a Verus binary release and its most
# recent compatible crates.io line. Verus can publish a new binary without
# publishing a new vstd, so these are intentionally independent:
#   - the Verus binary version determines the verus-spec-check release/tag date;
#   - the vstd version determines workspace, overlay, and dependency pins.
#
# In `latest` mode, the newest GitHub release is selected first, followed by
# the newest complete vstd + verus_builtin_macros pair whose date is not newer
# than that release. An explicit crate version keeps the historical/backfill
# behavior and selects the Verus binary release with the same date.
#
# Exit codes: 0 = synced (tree changed), 3 = no-op (both selected pins already
# current / an explicit crate pair is incomplete), non-zero otherwise = failure.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

CRATES_API="https://crates.io/api/v1/crates"
GITHUB_RELEASES_API="https://api.github.com/repos/verus-lang/verus/releases"
UA="verus-spec-check-ci"

SKIP_FLAKE=0
ARG=""
for a in "$@"; do
  case "$a" in
    --skip-flake) SKIP_FLAKE=1 ;;
    *) ARG="$a" ;;
  esac
done
[ -n "$ARG" ] || { echo "usage: sync-verus.sh <crate-version | latest> [--skip-flake]" >&2; exit 1; }

emit() { [ -n "${GITHUB_OUTPUT:-}" ] && echo "$1" >>"$GITHUB_OUTPUT"; return 0; }

crate_has_version() {
  local crate="$1" ver="$2"
  curl -fsSL --max-time 20 -H "User-Agent: $UA" "$CRATES_API/$crate/versions?per_page=100" \
    | jq -e --arg v "$ver" '.versions[] | select(.num==$v and (.yanked|not))' >/dev/null 2>&1
}

vstd_versions_newest_first() {
  curl -fsSL --max-time 20 -H "User-Agent: $UA" "$CRATES_API/vstd/versions?per_page=100" \
    | jq -r '.versions[] | select(.yanked|not) | .num' \
    | grep -E '^0\.0\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]+$' \
    | sort -r
}

latest_complete_crate_version() {
  local max_date="$1" candidate candidate_date
  while IFS= read -r candidate; do
    candidate_date="${candidate#0.0.0-}"
    candidate_date="${candidate_date%-*}"
    [[ "$candidate_date" > "$max_date" ]] && continue
    if crate_has_version verus_builtin_macros "$candidate"; then
      echo "$candidate"
      return 0
    fi
  done < <(vstd_versions_newest_first)
  return 1
}

latest_verus_version() {
  curl -fsSL --max-time 20 -H "User-Agent: $UA" "$GITHUB_RELEASES_API/latest" \
    | jq -r '.tag_name // empty' | sed 's|^release/||'
}

verus_version_for_date() {
  local date="$1" dotted
  dotted="0.$(echo "$date" | tr '-' '.')."
  curl -fsSL --max-time 20 -H "User-Agent: $UA" "$GITHUB_RELEASES_API?per_page=100" \
    | jq -r '.[].tag_name' | sed 's|^release/||' \
    | grep -F "$dotted" | head -1
}

dep_req() {
  local crate="$1" ver="$2" dep="$3"
  curl -fsSL --max-time 20 -H "User-Agent: $UA" "$CRATES_API/$crate/$ver/dependencies" \
    | jq -r --arg d "$dep" '.dependencies[] | select(.crate_id==$d) | .req' | head -1 \
    | sed 's/^=//'
}

# Resolve the Verus binary and vstd line independently.
if [ "$ARG" = "latest" ]; then
  VERUS_VERSION="$(latest_verus_version)"
  echo "$VERUS_VERSION" | grep -qE '^0\.[0-9]{4}\.[0-9]{2}\.[0-9]{2}\..+$' \
    || { echo "FATAL: could not resolve the latest Verus binary release" >&2; exit 1; }
  VERUS_DATE="$(echo "$VERUS_VERSION" | sed -E 's/^0\.([0-9]{4})\.([0-9]{2})\.([0-9]{2})\..*/\1-\2-\3/')"
  CRATE_VER="$(latest_complete_crate_version "$VERUS_DATE")" \
    || { echo "FATAL: no complete vstd/macros release exists on or before $VERUS_DATE" >&2; exit 1; }
else
  CRATE_VER="$ARG"
  echo "$CRATE_VER" | grep -qE '^0\.0\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]+$' \
    || { echo "FATAL: '$CRATE_VER' is not a valid crate version (0.0.0-YYYY-MM-DD-NNNN)" >&2; exit 1; }
  VERUS_DATE="$(echo "$CRATE_VER" | sed -E 's/0\.0\.0-([0-9]{4}-[0-9]{2}-[0-9]{2})-.*/\1/')"
  VERUS_VERSION="$(verus_version_for_date "$VERUS_DATE")"
  [ -n "$VERUS_VERSION" ] \
    || { echo "FATAL: no Verus binary release exists for $VERUS_DATE" >&2; exit 1; }
fi

echo "== sync-verus target =="
echo "  Verus binary -> $VERUS_VERSION"
echo "  vstd line    -> $CRATE_VER"

# An explicit version may name a split/incomplete publish. In latest mode the
# search above skips incomplete pairs and retains the previous complete line.
for c in vstd verus_builtin_macros; do
  if ! crate_has_version "$c" "$CRATE_VER"; then
    echo "NO-OP: $c $CRATE_VER not on crates.io yet (split publish?). Retry later." >&2
    emit "synced=false"
    exit 3
  fi
done

OLD_MAIN="$(awk '/^vstd *=/{ if (match($0,/"=[^"]+"/)) { print substr($0,RSTART+2,RLENGTH-3); exit } }' source/vstd_ext/Cargo.toml)"
OLD_VERUS="$(grep -oE 'verusVersion = "[^"]*";' flake.nix | head -1 | sed -E 's/verusVersion = "([^"]*)";/\1/')"
echo "current Verus binary: ${OLD_VERUS:-<none>}"
echo "current vstd line:    ${OLD_MAIN:-<none>}"

if [ "$OLD_MAIN" = "$CRATE_VER" ] \
   && { [ "$SKIP_FLAKE" -eq 1 ] || [ "$OLD_VERUS" = "$VERUS_VERSION" ]; }; then
  echo "NO-OP: selected Verus binary and vstd line are already pinned"
  emit "synced=false"
  exit 3
fi

# Only dependency changes require an overlay resync and manifest rewrites. A
# binary-only Verus release should change only flake.nix.
if [ "$OLD_MAIN" != "$CRATE_VER" ]; then
  SYN_VER="$(dep_req verus_builtin_macros "$CRATE_VER" verus_syn)"
  BUILTIN_VER="$(dep_req vstd "$CRATE_VER" verus_builtin)"
  [ -n "$SYN_VER" ] && [ -n "$BUILTIN_VER" ] \
    || { echo "FATAL: could not read verus_syn / verus_builtin pins from crates.io" >&2; exit 1; }
  echo "  verus_syn     -> =$SYN_VER"
  echo "  verus_builtin -> =$BUILTIN_VER"

  echo
  bash tools/release/overlay-resync.sh "$CRATE_VER"

  echo
  echo "== bumping workspace pins $OLD_MAIN -> $CRATE_VER =="
  perl -0777 -i -pe "s/(\[workspace\.package\].*?\nversion = )\"[^\"]*\"/\$1\"$CRATE_VER\"/s" Cargo.toml
  SYN_VER="$SYN_VER" perl -i -pe 's|(verus_syn = \{ version = ")=[^"]+(")|$1=$ENV{SYN_VER}$2|' Cargo.toml

  if [ -n "$OLD_MAIN" ]; then
    FILES=(source/vstd_ext/Cargo.toml README.md)
    while IFS= read -r f; do FILES+=("$f"); done < <(find examples -name Cargo.toml)
    for f in "${FILES[@]}"; do
      [ -f "$f" ] || continue
      OLD_MAIN="$OLD_MAIN" CRATE_VER="$CRATE_VER" \
        perl -i -pe 's/\Q$ENV{OLD_MAIN}\E/$ENV{CRATE_VER}/g' "$f"
    done
  fi

  CRATE_VER="$CRATE_VER" \
    perl -i -pe 's/0\.0\.0-\d{4}-\d{2}-\d{2}-\d{4}/$ENV{CRATE_VER}/g' README.md
  BUILTIN_VER="$BUILTIN_VER" perl -i -pe 's|(verus_builtin = ")=[^"]+(")|$1=$ENV{BUILTIN_VER}$2|' source/vstd_ext/Cargo.toml
else
  echo "vstd line unchanged; skipping dependency and overlay updates"
fi

if [ "$SKIP_FLAKE" -eq 0 ]; then
  echo
  bash tools/release/flake-bump.sh --version "$VERUS_VERSION"
else
  echo "(--skip-flake: leaving flake.nix untouched)"
fi

echo
if command -v zsh >/dev/null 2>&1; then
  zsh tools/check_versions.sh
else
  echo "(zsh not available; skipping check_versions.sh — CI runs it)"
fi

echo
echo "== sync-verus complete: Verus $VERUS_VERSION with vstd $CRATE_VER =="
emit "synced=true"
emit "verus_version=$VERUS_VERSION"
emit "verus_date=$VERUS_DATE"
emit "vstd_version=$CRATE_VER"
emit "previous_verus=$OLD_VERUS"
emit "previous_vstd=$OLD_MAIN"
# Backward-compatible output names for callers that consume explicit backfills.
emit "crate_version=$CRATE_VER"
emit "date=$VERUS_DATE"
emit "previous=$OLD_MAIN"
