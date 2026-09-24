#!/usr/bin/env bash
# Verus-level validation sweep for the examples crate. Must 
# be in a nix devshell for this to work properly, e.g.:
#   nix develop --command bash tools/verify_examples.sh
#   nix develop --command bash tools/verify_examples.sh assert
#
# With no args every example is swept; otherwise only the named ones.
# Examples without `verify = true` are skipped automatically.
#
# The engine's own verify gate is now the `verify_*` cases in
# source/vcheck_test (`cargo test -p verus_spec_check_test`), which cover each
# feature as an inline snippet.
set +e
cd "$(dirname "$0")/.."

NOT_VERIFY_CLEAN=(
  # known-broken (TODO: fix and remove)
  readme
)
is_excluded() {
  local n=$1
  for e in "${NOT_VERIFY_CLEAN[@]}"; do [ "$e" = "$n" ] && return 0; done
  return 1
}

CARGO_BIN=${CARGO:-cargo}
PASS=0
FAIL=0
SKIP=0
FAILED_LIST=()

out=$( (cd source/vstd_ext && "$CARGO_BIN" verus focus) 2>&1 )
rc=$?
if [ $rc -eq 0 ]; then
  v=$(echo "$out" | grep -oE 'verification results:: [0-9]+ verified' | grep -oE '[0-9]+' | head -1)
  echo "PASS vstd_ext (${v:-cached} verified)"
  PASS=$((PASS+1))
else
  echo "FAIL vstd_ext (exit $rc)"
  FAIL=$((FAIL+1))
  FAILED_LIST+=(vstd_ext)
  echo "$out" | tail -12 | sed 's/^/    /'
fi

# With no args, sweep every example; otherwise only the named ones.
if [ "$#" -gt 0 ]; then
  DIRS=()
  for n in "$@"; do
    if [ -f "examples/$n/Cargo.toml" ]; then
      DIRS+=("examples/$n/")
    else
      echo "FAIL $n (no such example: examples/$n/Cargo.toml not found)"
      FAIL=$((FAIL+1))
      FAILED_LIST+=("$n")
    fi
  done
else
  DIRS=(examples/*/)
fi

for d in "${DIRS[@]}"; do
  name=$(basename "$d")
  [ ! -f "$d/Cargo.toml" ] && continue
  # Only examples that opt into verification.
  grep -qE '^\s*verify\s*=\s*true' "$d/Cargo.toml" || continue
  if is_excluded "$name"; then
    echo "SKIP $name (not verify-clean by design)"
    SKIP=$((SKIP+1))
    continue
  fi

  out=$( (cd "$d" && "$CARGO_BIN" verus focus) 2>&1 )
  rc=$?

  if [ $rc -eq 0 ]; then
    v=$(echo "$out" | grep -oE 'verification results:: [0-9]+ verified' | grep -oE '[0-9]+' | head -1)
    echo "PASS $name (${v:-cached} verified)"
    PASS=$((PASS+1))
  else
    echo "FAIL $name (exit $rc)"
    FAIL=$((FAIL+1))
    FAILED_LIST+=("$name")
    echo "$out" | tail -12 | sed 's/^/    /'
  fi
done

echo
echo "Summary: $PASS pass, $FAIL fail, $SKIP skipped"
if [ $FAIL -gt 0 ]; then
  echo "Verify failures: ${FAILED_LIST[*]}"
  exit 1
fi
exit 0
