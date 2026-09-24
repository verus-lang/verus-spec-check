#!/bin/zsh
# check_overlay.sh [verus_builtin_macros-version]
#
# Asserts source/builtin_macros_overlay is byte-identical to what
# tools/release/overlay-resync.sh produces from the pinned stock
# upstream plus the resync/ delta assets (patches/, files/,
# manifest.txt). Same gate CI runs, minus the working-tree mutation:
# the resync renders into a scratch copy of the overlay and the result
# is diffed against the real one.
#
# Upstream is the pristine crates.io source of the pinned version, so
# the check does not depend on a local Verus checkout. The version
# defaults to the verus_builtin_macros pin in source/vstd_ext/Cargo.toml;
# pass one explicitly to preview drift against a new release before
# bumping the pins.
#
# Run from the repo root: `zsh tools/check_overlay.sh`.
# Requires: cargo (fetches the upstream crate), patch, tar, diff.

set -e
cd "$(dirname "$0")/.."

OVERLAY="source/builtin_macros_overlay"
PIN=$(awk -F'"' '/^verus_builtin_macros *= *"=/ { print substr($2, 2); exit }' source/vstd_ext/Cargo.toml)
VERSION="${1:-$PIN}"

if [ -z "$VERSION" ]; then
    echo "FATAL: no verus_builtin_macros pin found in source/vstd_ext/Cargo.toml"
    exit 1
fi
if [ ! -d "$OVERLAY/resync" ]; then
    echo "FATAL: $OVERLAY/resync assets not found"
    exit 1
fi

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# Scratch copy, minus build output. Writable even when the source tree
# is a read-only nix store path (`nix run .#check`).
mkdir -p "$WORK/overlay"
tar -C "$OVERLAY" --exclude=./target -cf - . | tar -C "$WORK/overlay" -xf -
chmod -R u+w "$WORK/overlay"

echo "== overlay drift check: verus_builtin_macros $VERSION =="
if ! OVERLAY_DIR="$WORK/overlay" bash tools/release/overlay-resync.sh "$VERSION" > "$WORK/resync.log" 2>&1; then
    echo "FAIL  overlay-resync.sh cannot rebuild the overlay from upstream $VERSION:"
    tail -15 "$WORK/resync.log" | sed 's/^/        /'
    echo
    echo "      Upstream changed a file the resync assets patch or add."
    echo "      Re-apply the delta by hand and regenerate resync/ (see .github/workflows/README.md)."
    exit 1
fi
grep -E '^(--|==) ' "$WORK/resync.log" | sed 's/^/      /'

# Comment and blank lines in Cargo.toml carry no build meaning.
strip_comments() {
    grep -vE '^[[:space:]]*(#|$)' "$1" || true
}

drift=()
while IFS= read -r line; do
    [ -n "$line" ] && drift+=("$line")
done < <(diff -rq --exclude=target --exclude=Cargo.toml "$WORK/overlay" "$OVERLAY" \
            | sed -E "s#$WORK/overlay/##; s#^Files ([^ ]+) and .*#\1#; s#^Only in $OVERLAY/?([^:]*): (.*)#\1/\2 (only in overlay)#; s#^Only in ([^:]*): (.*)#\1/\2 (missing from overlay)#" \
            | sed -E 's#^/##')
if ! diff -q <(strip_comments "$WORK/overlay/Cargo.toml") <(strip_comments "$OVERLAY/Cargo.toml") > /dev/null; then
    drift+=("Cargo.toml")
fi

echo
if [ ${#drift[@]} -eq 0 ]; then
    echo "OK    overlay matches upstream $VERSION + resync delta."
    exit 0
fi

echo "FAIL  ${#drift[@]} path(s) differ from what overlay-resync.sh $VERSION produces:"
for f in "${drift[@]}"; do
    echo "        $f"
done
echo
echo "      Hand edits to the overlay are lost on the next resync. Either run"
echo "      tools/release/overlay-resync.sh $VERSION to regenerate the overlay, or"
echo "      move the intended change into resync/ (patches/, files/, manifest.txt)."
exit 1
