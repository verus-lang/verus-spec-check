#!/bin/zsh
# Run examples and report pass/fail.
#
# Uses `cargo test` (no --lib) so the script exercises both lib
# tests and any integration/doctests an example might add.
#
#   zsh tools/run_examples.sh                  # every example
#   zsh tools/run_examples.sh assert           # only the named ones
#
# The engine's own end-to-end gate is `cargo test -p verus_spec_check_test`
# (source/vcheck_test), which covers each feature as an inline snippet with
# a declared expected outcome. 
#
# The examples remaining here are documentation-facing.
#
# Run from anywhere: `zsh tools/run_examples.sh` or `bash tools/run_examples.sh`.
set +e
cd "$(dirname "$0")/.."

# Examples that are EXPECTED to fail `cargo test`. These are soundness
# fixtures: crates whose `#[vcheck]`-labeled specs are known-unsound, so a
# failing harness is the correct (asserted) outcome. An entry here that
# PASSES is reported as a failure of the sweep — it means the detector
# regressed and no longer catches the bad spec.
#
# Currently empty: the unsound higher-order fixtures moved to
# source/vcheck_test/tests/higher_order.rs, where the expectation is stated
# per case as `=> HarnessOutcome::FailsHarness` instead of by name here.
# The mechanism is kept for any future example-level fixture.
EXPECTED_FAIL=()

is_expected_fail() {
  local n=$1
  for e in "${EXPECTED_FAIL[@]}"; do
    [ "$e" = "$n" ] && return 0
  done
  return 1
}

PASS=0
FAIL=0
FAILED_LIST=()

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
  # Skip non-example entries (README.md etc.)
  [ ! -f "$d/Cargo.toml" ] && continue
  out=$(${CARGO:-cargo} test --manifest-path "$d/Cargo.toml" 2>&1)
  if is_expected_fail "$name"; then
    if echo "$out" | grep -qE 'could not compile|^error\['; then
      # Build error: the fixture must BUILD and fail at test time.
      echo "FAIL $name (expected test failures, got build error)"
      FAIL=$((FAIL+1))
      FAILED_LIST+=("$name")
      echo "$out" | tail -10 | sed 's/^/    /'
    elif echo "$out" | grep -q 'FAILED'; then
      echo "XFAIL $name (unsound-spec fixture failed as expected)"
      PASS=$((PASS+1))
    else
      echo "FAIL $name (unsound-spec fixture PASSED — detector regression)"
      FAIL=$((FAIL+1))
      FAILED_LIST+=("$name")
    fi
    continue
  fi
  if echo "$out" | grep -qE '^error|FAILED'; then
    echo "FAIL $name"
    FAIL=$((FAIL+1))
    FAILED_LIST+=("$name")
    echo "$out" | tail -10 | sed 's/^/    /'
    continue
  fi
  lib_count=$(echo "$out" | awk '
    /^running [0-9]+ tests?$/ { if (got==0) { match($0, /[0-9]+/); n=substr($0, RSTART, RLENGTH); got=1 } }
    END { print n }')
  # A compiling example with ZERO harness tests is a silent regression:
  # it usually means `#[vcheck]` folding didn't run (e.g. the crate is
  # missing the direct `verus_builtin_macros` dep that enables the
  # overlay's `contrib-hooks` feature), so `#[vcheck]` resolved to the
  # no-op attribute macro and nothing was generated.
  if [ "${lib_count:-0}" -eq 0 ]; then
    echo "FAIL $name (0 tests ran — #[vcheck] harness generation silently produced nothing)"
    FAIL=$((FAIL+1))
    FAILED_LIST+=("$name")
    continue
  fi
  echo "PASS $name ($lib_count tests)"
  PASS=$((PASS+1))
done
echo
echo "Summary: $PASS pass, $FAIL fail"
if [ $FAIL -gt 0 ]; then
  echo "Failures: ${FAILED_LIST[@]}"
  exit 1
fi
exit 0
