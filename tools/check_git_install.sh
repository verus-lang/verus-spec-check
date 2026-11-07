#!/usr/bin/env bash
set -euo pipefail

usage="usage: check_git_install.sh [--verify] <git-url> <rev>"
VERIFY=0
ARGS=()
for a in "$@"; do
  case "$a" in
    --verify) VERIFY=1 ;;
    *) ARGS+=("$a") ;;
  esac
done
[ "${#ARGS[@]}" -eq 2 ] || { echo "$usage" >&2; exit 1; }
URL="${ARGS[0]}"
REV="${ARGS[1]}"

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PIN=$(awk -F'"' '/^vstd *= *"=/ { print substr($2, 2); exit }' "$REPO_ROOT/source/vstd_ext/Cargo.toml")
[ -n "$PIN" ] || { echo "FATAL: no vstd pin in source/vstd_ext/Cargo.toml" >&2; exit 1; }

WORK="${GIT_INSTALL_DIR:-$(mktemp -d)}"
mkdir -p "$WORK/src"
cat > "$WORK/Cargo.toml" <<EOF
[package]
name = "git_install_check"
version = "0.0.0"
edition = "2021"

[lib]
path = "src/lib.rs"

[dependencies]
vstd = "=$PIN"
verus_spec_check = { git = "$URL", rev = "$REV" }
verus_spec_check_vstd_ext = { git = "$URL", rev = "$REV" }

[package.metadata.verus]
verify = true

[patch.crates-io]
verus_builtin_macros = { git = "$URL", rev = "$REV" }

[workspace]
EOF
cat > "$WORK/src/lib.rs" <<'EOF'
use verus_spec_check::*;
use vstd::prelude::*;

verus! {

#[vcheck]
fn safe_double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == x * 2,
{
    x + x
}

fn midpoint(a: u32, b: u32) -> (m: u32)
    requires a <= b,
{
    let m = a + (b - a) / 2;
    #[vcheck] assert(a <= m && m <= b);
    m
}

}
EOF

echo "== git install check: $URL @ $REV (vstd =$PIN) in $WORK =="
if ! (cd "$WORK" && cargo test --lib) > "$WORK/test.log" 2>&1; then
  echo "FAIL  cargo test failed:"
  tail -40 "$WORK/test.log" | sed 's/^/      /'
  exit 1
fi
harnesses=$(grep -cE '^test __verus_spec_check[^ ]* \.\.\. ok$' "$WORK/test.log" || true)
if [ "$harnesses" -lt 2 ]; then
  echo "FAIL  expected 2 vcheck harnesses to run, found $harnesses:"
  grep -E '^test |test result' "$WORK/test.log" | sed 's/^/      /'
  exit 1
fi
echo "OK    cargo test ran $harnesses vcheck harnesses"

if [ "$VERIFY" -eq 1 ]; then
  if ! (cd "$WORK" && cargo verus focus) > "$WORK/verify.log" 2>&1; then
    echo "FAIL  cargo verus focus failed:"
    tail -40 "$WORK/verify.log" | sed 's/^/      /'
    exit 1
  fi
  echo "OK    $(grep -oE 'verification results:: [0-9]+ verified, [0-9]+ errors' "$WORK/verify.log" | tail -1)"
fi
