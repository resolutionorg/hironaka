#!/usr/bin/env python3
"""Header and module-docstring check.

Every `.lean` file under `Hironaka/` and `HironakaExamples/` (the root modules `Hironaka.lean` and
`HironakaExamples.lean` excepted) must begin with exactly the five-line copyright block of `scripts/header.txt`,
followed by imports and a module docstring `/-! # Title ... -/` whose first line starts with `# `.
Usage: scripts/check_header.py [--fix]   (`--fix` rewrites a differing copyright block in place when the file
starts with a `/- ... -/` block of at most eight lines; it never touches anything else). Exit 1 with a list of
offenders.
"""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIBS = ["Hironaka", "HironakaExamples"]
HDR = open(os.path.join(ROOT, "scripts", "header.txt"), encoding="utf-8").read().rstrip("\n").split("\n")
assert len(HDR) == 5 and HDR[0] == "/-" and HDR[4] == "-/"

def files():
    for lib in LIBS:
        for dp, _, fs in os.walk(os.path.join(ROOT, lib)):
            for fn in sorted(fs):
                if fn.endswith(".lean"):
                    yield os.path.join(dp, fn)

def main(argv):
    fix = "--fix" in argv
    bad = []
    for p in files():
        rel = os.path.relpath(p, ROOT)
        text = open(p, encoding="utf-8").read()
        lines = text.split("\n")
        if lines[:5] != HDR:
            if fix and lines and lines[0].strip() == "/-":
                # replace the leading block comment (at most eight lines) by the header
                end = next((i for i in range(1, min(9, len(lines))) if lines[i].strip() == "-/"), None)
                if end is not None:
                    lines = HDR + lines[end + 1:]
                    open(p, "w", encoding="utf-8").write("\n".join(lines))
                    text = "\n".join(lines)
            if lines[:5] != HDR:
                bad.append(f"{rel}: copyright block differs from scripts/header.txt"); continue
        body = "\n".join(lines[5:])
        m = re.search(r"/-!\s*\n?\s*(#[^\n]*)", body)
        if not m or not m.group(1).startswith("# "):
            bad.append(f"{rel}: missing module docstring `/-! # Title ... -/`")
    if bad:
        print("\n".join(bad)); return 1
    print("check_header: ok"); return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
