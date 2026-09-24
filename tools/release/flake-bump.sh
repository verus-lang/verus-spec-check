#!/usr/bin/env bash
# flake-bump.sh [--date YYYY-MM-DD | --version X.YYYY.MM.DD.hash | latest]
#
# Updates flake.nix's `verusVersion` and the `srcHashes` entry to a target
# Verus *binary* release, and `z3Version` + its source hash to whatever that
# release's source/tools/get-z3.sh expects. Note this is the binary release tag format
# (e.g. 0.2026.06.14.4ea7d0f), which differs from the crates.io version
# string (0.0.0-2026-06-14-0213); they share only the date.
#
# Modes:
#   latest                 pick the newest GitHub release
#   --version X.Y.Z.hash   use an exact binary version string
#   --date YYYY-MM-DD       find the GitHub release whose tag matches that date
#
# Requires: curl, jq, nix (nix-prefetch-url, nix hash). Intended for CI
# (ubuntu + nix) or a dev machine with nix.
set -euo pipefail

REPO="verus-lang/verus"
FLAKE="$(cd "$(dirname "$0")/../.." && pwd)/flake.nix"

emit() { [ -n "${GITHUB_OUTPUT:-}" ] && echo "$1" >>"$GITHUB_OUTPUT"; return 0; }

resolve_version() {
  local mode="$1" arg="${2:-}"
  case "$mode" in
    latest)
      curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" \
        | jq -r .tag_name | sed 's|^release/||'
      ;;
    --version)
      echo "$arg"
      ;;
    --date)
      # Date form in the tag is 0.YYYY.MM.DD.hash (dots). Convert the
      # YYYY-MM-DD arg and grep the releases list for a matching tag.
      local dotted; dotted="0.$(echo "$arg" | tr '-' '.')."
      curl -fsSL "https://api.github.com/repos/${REPO}/releases?per_page=100" \
        | jq -r '.[].tag_name' | sed 's|^release/||' \
        | grep -F "$dotted" | head -1
      ;;
    *)
      echo "usage: flake-bump.sh [latest | --version X | --date YYYY-MM-DD]" >&2
      exit 1
      ;;
  esac
}

MODE="${1:?usage: flake-bump.sh [latest | --version X | --date YYYY-MM-DD]}"
VERSION="$(resolve_version "$MODE" "${2:-}")"
if [ -z "$VERSION" ]; then
  echo "FATAL: could not resolve a Verus binary release for '$MODE ${2:-}'." >&2
  exit 1
fi

CURRENT="$(grep -oE 'verusVersion = "[^"]*";' "$FLAKE" | head -1 \
             | sed -E 's/verusVersion = "([^"]*)";/\1/')"
CURRENT_Z3="$(grep -oE '^\s*z3Version = "[^"]*";' "$FLAKE" | head -1 \
             | sed -E 's/.*"([^"]*)".*/\1/')"
echo "current flake verusVersion: $CURRENT"
echo "target  flake verusVersion: $VERSION"

# The z3 rust_verify expects lives in upstream's get-z3.sh at the release
# commit (last dot-separated field of the version). Try the tag first, then
# the short sha, across the paths the script has lived at.
fetch_get_z3() {
  local refs=( "refs/tags/release/${VERSION}" "${VERSION##*.}" )
  local paths=( "source/tools/get-z3.sh" "tools/get-z3.sh" )
  local ref path out
  for ref in "${refs[@]}"; do
    for path in "${paths[@]}"; do
      if out=$(curl -fsSL "https://raw.githubusercontent.com/${REPO}/${ref}/${path}" 2>/dev/null); then
        printf '%s' "$out"
        return 0
      fi
    done
  done
  return 1
}

parse_z3_version() {
  local script="$1" v
  v=$(printf '%s' "$script" \
        | grep -iEo 'z3[_-]?version[[:space:]]*=[[:space:]]*"?[0-9]+(\.[0-9]+)+' \
        | grep -oE '[0-9]+(\.[0-9]+)+' | head -1)
  [ -n "$v" ] || v=$(printf '%s' "$script" \
        | grep -oE '\bz3-[0-9]+(\.[0-9]+)+' | sed 's/^z3-//' | head -1)
  [ -n "$v" ] || return 1
  printf '%s\n' "$v"
}

if ! GET_Z3="$(fetch_get_z3)"; then
  echo "FATAL: could not fetch get-z3.sh for ${VERSION}; has it moved?" >&2
  exit 1
fi
if ! Z3_VERSION="$(parse_z3_version "$GET_Z3")"; then
  echo "FATAL: could not parse a z3 version out of get-z3.sh; has its format changed?" >&2
  exit 1
fi
echo "current flake z3Version:    $CURRENT_Z3"
echo "target  flake z3Version:    $Z3_VERSION"

if [ "$CURRENT" = "$VERSION" ] && [ "$CURRENT_Z3" = "$Z3_VERSION" ]; then
  echo "flake already at $VERSION (z3 $Z3_VERSION)"
  emit "flake_updated=false"
  exit 0
fi

get_hash() {
  local arch="$1"
  local url="https://github.com/${REPO}/releases/download/release%2F${VERSION}/verus-${VERSION}-${arch}.zip"
  nix hash convert --hash-algo sha256 --to sri "$(nix-prefetch-url --unpack "$url")"
}

get_z3_hash() {
  local url="https://github.com/Z3Prover/z3/archive/refs/tags/z3-${1}.tar.gz"
  nix hash convert --hash-algo sha256 --to sri "$(nix-prefetch-url --unpack "$url")"
}

if [ "$CURRENT" != "$VERSION" ]; then
  echo "prefetching release hashes (this pulls the release zips)..."
  H_LINUX="$(get_hash x86-linux)"
  H_ARM_MAC="$(get_hash arm64-macos)"
  H_X86_MAC="$(get_hash x86-macos)"

  # Replace the version string everywhere (covers both the `verusVersion`
  # line and the `srcHashes` map key, which share the same string), then set
  # the three per-platform hash values INSIDE the target version's srcHashes
  # block only -- the flake carries entries for other pinned versions (e.g.
  # extraVerusVersions like verus-0308) whose hashes must not be touched.
  # perl -i for BSD/GNU portability.
  perl -i -pe "s/\Q$CURRENT\E/$VERSION/g" "$FLAKE"
  VERSION="$VERSION" H_LINUX="$H_LINUX" H_ARM_MAC="$H_ARM_MAC" H_X86_MAC="$H_X86_MAC" \
  perl -0777 -i -pe '
    s{("\Q$ENV{VERSION}\E"\s*=\s*\{.*?\};)}{
      my $b = $1;
      $b =~ s/("x86-linux"\s*=\s*)"[^"]*";/$1"$ENV{H_LINUX}";/;
      $b =~ s/("arm64-macos"\s*=\s*)"[^"]*";/$1"$ENV{H_ARM_MAC}";/;
      $b =~ s/("x86-macos"\s*=\s*)"[^"]*";/$1"$ENV{H_X86_MAC}";/;
      $b;
    }se' "$FLAKE"
  echo "Updated flake.nix: $CURRENT -> $VERSION"
fi

if [ "$CURRENT_Z3" != "$Z3_VERSION" ]; then
  echo "prefetching z3 ${Z3_VERSION} source hash..."
  Z3_HASH="$(get_z3_hash "$Z3_VERSION")"
  Z3_VERSION="$Z3_VERSION" perl -i -pe \
    's|^(\s*)z3Version = "[^"]*";|$1z3Version = "$ENV{Z3_VERSION}";|' "$FLAKE"
  # slurp mode, scoped to the z3 fetchFromGitHub block
  Z3_HASH="$Z3_HASH" perl -0777 -i -pe \
    's|(repo = "z3";.*?hash = ")[^"]*(")|$1$ENV{Z3_HASH}$2|s' "$FLAKE"
  echo "Updated flake.nix z3: $CURRENT_Z3 -> $Z3_VERSION"
  emit "z3_updated=true"
fi

emit "flake_updated=true"
emit "flake_version=${VERSION}"
emit "flake_previous=${CURRENT}"
emit "z3_version=${Z3_VERSION}"
emit "z3_previous=${CURRENT_Z3}"
