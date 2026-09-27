#!/usr/bin/env python3
"""Fail unless every theorem in Axioms.lean / AxiomsLink.lean uses only the
standard axioms (propext, Classical.choice, Quot.sound).

Security-package twin of proofs/doubledeal/check_axioms.py. Two files because
the Mathlib side and the Link 2 side cannot share one environment. Run after
`lake build` in proofs/doubledeal/security.
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PKG = Path(__file__).resolve().parent
FILES = ["Axioms.lean", "AxiomsLink.lean"]


def audit(fname: str) -> int:
    src = (PKG / fname).read_text()
    expected = re.findall(r"^#print axioms\s+(\S+)", src, flags=re.M)
    proc = subprocess.run(["lake", "env", "lean", fname], cwd=PKG,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {fname} did not elaborate cleanly", file=sys.stderr)
        return len(expected) or 1
    seen = {}
    for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        seen[name] = {a.strip() for a in axs.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", out):
        seen[name] = set()
    bad = 0
    for name in expected:
        if name not in seen:
            print(f"check_axioms: no axiom report for {name}", file=sys.stderr)
            bad += 1
        elif seen[name] - ALLOWED:
            print(f"FAIL {name}: uses {sorted(seen[name] - ALLOWED)}", file=sys.stderr)
            bad += 1
        else:
            print(f"ok {name}: {sorted(seen[name])}")
    print(f"check_axioms: {fname}: {len(expected) - bad}/{len(expected)} clean")
    return bad


def main() -> int:
    bad = sum(audit(f) for f in FILES)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
