#!/usr/bin/env python3
"""Scan vstd for assume_specification and external_body fns that lack #[vcheck].

Usage: VSTD_ROOT=/path/to/verus/source/vstd python3 tools/scan_vcheck.py
"""
import os, re, sys

ROOT = os.environ.get("VSTD_ROOT", "")

VCHECK = "#[vcheck"

def scan_file(path):
    with open(path) as f:
        lines = f.readlines()
    n = len(lines)
    out = []
    i = 0
    while i < n:
        ls = lines[i].rstrip()
        kind = None
        ident = None
        if "pub assume_specification" in ls or "assume_specification[" in ls:
            kind = "assume_specification"
            ident = ls.strip()
        elif "#[verifier::external_body]" in ls:
            # Walk forward up to 15 lines past attributes/comments to find
            # the actual fn signature line.
            for j in range(i + 1, min(i + 16, n)):
                nxt = lines[j].rstrip()
                stripped = nxt.lstrip()
                if (
                    not stripped
                    or stripped.startswith("//")
                    or stripped.startswith("#[")
                ):
                    continue
                m = re.match(r"(pub\s+(\([^)]+\)\s+)?)?(unsafe\s+)?(exec\s+)?fn\s+(\w+)", stripped)
                if m:
                    kind = "fn external_body"
                    ident = stripped
                else:
                    # It's external_body on something other than a fn (struct,
                    # impl, etc.). Skip: not a #[vcheck] candidate.
                    kind = None
                    ident = None
                break
        if kind is not None:
            has_vcheck = False
            # Look back up to 10 lines for #[vcheck]
            for k in range(max(0, i - 10), i):
                if VCHECK in lines[k]:
                    has_vcheck = True
                    break
            out.append((i + 1, kind, has_vcheck, ident))
        i += 1
    return out


def main():
    if not os.path.isdir(ROOT):
        sys.exit("scan_vcheck.py: set VSTD_ROOT to a vstd source directory")
    rows = []
    for dirpath, _, files in os.walk(ROOT):
        if "/target/" in dirpath:
            continue
        for fn in files:
            if not fn.endswith(".rs"):
                continue
            p = os.path.join(dirpath, fn)
            for line, kind, has_vcheck, ident in scan_file(p):
                rows.append((p, line, kind, has_vcheck, ident))
    by_kind_status = {}
    for r in rows:
        path, line, kind, has_vcheck, ident = r
        key = (kind, has_vcheck)
        by_kind_status.setdefault(key, []).append(r)

    print("# Summary\n")
    for (kind, has_vcheck), entries in sorted(by_kind_status.items()):
        status = "HAS_VCHECK" if has_vcheck else "no_vcheck"
        print(f"\n## {kind} — {status} ({len(entries)})\n")
        for p, line, _, _, ident in entries:
            rel = p.replace(ROOT + "/", "")
            shown = ident[:140] if ident else ""
            print(f"  {rel}:{line}  {shown}")


if __name__ == "__main__":
    main()
