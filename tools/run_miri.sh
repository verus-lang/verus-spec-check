#!/usr/bin/env bash
# Run the vstd vcheck harnesses under Miri, from the current directory.
#
# Miri interprets each instruction, so per-case cost is ~100x slower than
# native. Default PROPTEST_CASES to a low value to keep wall time
# bounded; raise it manually if you want stronger coverage:
#
#     PROPTEST_CASES=32 bash tools/run_miri.sh
#
# Pass-through args land on `cargo miri test`, so you can filter:
#
#     bash tools/run_miri.sh std_specs::num
#
# Requires:
#   rustup component add --toolchain nightly miri rust-src
set -euo pipefail

PROPTEST_CASES=${PROPTEST_CASES:-8} \
MIRIFLAGS="${MIRIFLAGS:--Zmiri-disable-isolation}" \
  cargo +nightly miri test \
    --lib \
    --no-fail-fast \
    "$@"
