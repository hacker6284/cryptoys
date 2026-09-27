#!/usr/bin/env python3
"""Fail unless every theorem in lean/Axioms.lean uses only the standard axioms.

Runs `lake env lean Axioms.lean` in proofs/doubledeal/lean (after `lake build`)
and parses the `#print axioms` output. Allowed: propext, Classical.choice,
Quot.sound. Anything else (sorryAx, Lean.ofReduceBool, a user axiom) fails, as
does a Lean error or a theorem listed in Axioms.lean that printed nothing.
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_DIR = Path(__file__).resolve().parent / "lean"


def main() -> int:
    src = (LEAN_DIR / "Axioms.lean").read_text()
    expected = re.findall(r"^#print axioms\s+(\S+)", src, flags=re.M)
    proc = subprocess.run(["lake", "env", "lean", "Axioms.lean"], cwd=LEAN_DIR,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print("check_axioms: Axioms.lean did not elaborate cleanly", file=sys.stderr)
        return 1
    seen = {}
    for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        seen[name] = {a.strip() for a in axs.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", out):
        seen[name] = set()
    bad = False
    for name in expected:
        if name not in seen:
            print(f"check_axioms: no axiom report for {name}", file=sys.stderr)
            bad = True
            continue
        extra = seen[name] - ALLOWED
        if extra:
            print(f"check_axioms: {name} uses {sorted(extra)}", file=sys.stderr)
            bad = True
        else:
            print(f"ok {name}: {sorted(seen[name])}")
    if bad:
        return 1
    print(f"check_axioms: {len(expected)} theorems use only {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
