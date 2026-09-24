#!/bin/zsh
# check_versions.sh
#
# Asserts that all crates in this workspace pin the same Verus
# version. Drift between (engine, vstd_ext, overlay, examples)
# manifests as cryptic dual-instance errors at user level
# ("expected `verus_syn::Item`, got `verus_syn::Item`"), so we
# check eagerly and surface drift as a clear script failure.
#
# Run from the repo root: `bash tools/check_versions.sh`.
#
# What "the Verus version" means here:
#   * `verus_syn`             pinned to the line dated YYYY-MM-DD-NNNN
#   * `verus_builtin_macros`  same date
#   * `verus_prettyplease`    same date
#   * `verus_builtin`         pinned to a usually-older date (Verus
#                             only bumps it occasionally, so it
#                             diverges; we track it but don't enforce
#                             same-date as the others)
#   * `vstd`                  same date as verus_builtin_macros
#
# We extract the pinned version per crate and assert all the
# "same-date" group declarations match. If they don't, print the
# differing files and exit nonzero.

set -e
cd "$(dirname "$0")/.."

# Files that pin verus_syn / verus_builtin_macros / verus_prettyplease /
# vstd. The same-date group must be coherent across these. Engine
# crates inherit verus_syn from the root [workspace.dependencies].
FILES=(
    "Cargo.toml"
    "source/vstd_ext/Cargo.toml"
    "source/builtin_macros_overlay/Cargo.toml"
    examples/*/Cargo.toml
)

# Crates whose version must match across all files (if declared).
SAME_DATE_CRATES=(
    "verus_syn"
    "verus_builtin_macros"
    "verus_prettyplease"
    "vstd"
)

# Also tracked but allowed to diverge in date (Verus's own pin shape):
INDEPENDENT_CRATES=(
    "verus_builtin"
)

# Returns the pinned version for a (file, crate) pair. Looks for
# `<crate> = "=X"`, `<crate> = { version = "=X", ... }`, or the table
# form `[dependencies.<crate>]` + `version = "=X"`. Empty if the crate
# isn't declared in that file.
get_version() {
    local file=$1
    local crate=$2
    awk -v c="$crate" '
        function pin(line) {
            if (match(line, /"=[^"]+"/)) {
                print substr(line, RSTART+2, RLENGTH-3)
                exit
            }
        }
        $0 ~ "^"c" *=" { pin($0) }
        $0 ~ "^\\[(dev-|build-)?dependencies\\."c"\\]" { intable = 1; next }
        intable && /^\[/ { intable = 0 }
        intable && /^version *=/ { pin($0) }
    ' "$file"
}

errors=0

# Per same-date crate, collect (file, version) tuples and check
# they all agree.
for crate in "${SAME_DATE_CRATES[@]}"; do
    declare -A versions=()
    for file in "${FILES[@]}"; do
        if [ ! -f "$file" ]; then
            continue
        fi
        v=$(get_version "$file" "$crate")
        if [ -z "$v" ]; then
            continue
        fi
        versions[$file]=$v
    done

    # Find the unique version values for this crate.
    typeset -aU unique_versions=()
    for file in "${(@k)versions}"; do
        unique_versions+=(${versions[$file]})
    done

    if [ ${#unique_versions[@]} -gt 1 ]; then
        echo "FAIL  $crate has multiple pinned versions:"
        for file in "${(@k)versions}"; do
            echo "        $file: ${versions[$file]}"
        done
        errors=$((errors+1))
    elif [ ${#unique_versions[@]} -eq 1 ]; then
        echo "OK    $crate -> ${unique_versions[1]}"
    fi
done

# Independent crates: just print what we find for visibility.
for crate in "${INDEPENDENT_CRATES[@]}"; do
    declare -A versions=()
    for file in "${FILES[@]}"; do
        if [ ! -f "$file" ]; then
            continue
        fi
        v=$(get_version "$file" "$crate")
        if [ -z "$v" ]; then
            continue
        fi
        versions[$file]=$v
    done

    typeset -aU unique_versions=()
    for file in "${(@k)versions}"; do
        unique_versions+=(${versions[$file]})
    done

    if [ ${#unique_versions[@]} -gt 1 ]; then
        echo "INFO  $crate has multiple pinned versions (allowed, but unusual):"
        for file in "${(@k)versions}"; do
            echo "        $file: ${versions[$file]}"
        done
    elif [ ${#unique_versions[@]} -eq 1 ]; then
        echo "OK    $crate -> ${unique_versions[1]}"
    fi
done

# README quick-start snippet: every version-shaped string must match the
# main pin (sync-verus.sh bumps them; this catches manual edits and any
# release cycle where the bump missed prose/comments), and the snippet
# must keep the direct `verus_builtin_macros` dep with contrib-hooks —
# without that line `#[vcheck]` compiles away in a user's project and the
# quick start silently produces 0 property tests.
main_pin=$(get_version "source/vstd_ext/Cargo.toml" "vstd")
if [ -n "$main_pin" ] && [ -f README.md ]; then
    readme_drift=$(grep -oE '0\.0\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4}' README.md \
        | sort -u | grep -v "^${main_pin}$" || true)
    if [ -n "$readme_drift" ]; then
        echo "FAIL  README.md references stale version(s):"
        echo "$readme_drift" | sed 's/^/        /'
        echo "        expected: $main_pin (run tools/release/sync-verus.sh)"
        errors=$((errors+1))
    else
        echo "OK    README.md versions -> $main_pin"
    fi
    if grep -q 'verus_builtin_macros = { version = "=' README.md \
        && grep -q 'features = \["contrib-hooks"\]' README.md; then
        echo "OK    README.md quick start declares verus_builtin_macros + contrib-hooks"
    else
        echo "FAIL  README.md quick start is missing the direct verus_builtin_macros"
        echo "        dep with features = [\"contrib-hooks\"] — without it #[vcheck]"
        echo "        compiles away (see examples/readme/Cargo.toml)."
        errors=$((errors+1))
    fi
fi

echo
if [ $errors -gt 0 ]; then
    echo "Version drift detected. $errors crate(s) have inconsistent pins."
    echo "Bump them all to the same date together, then re-run."
    exit 1
fi

echo "All version pins consistent."
exit 0
