#!/usr/bin/env python3
"""Fail unless every theorem in Axioms.lean uses only the
standard axioms (propext, Classical.choice, Quot.sound).

Exception, by exact name: the theorems in KNOWN_SORRY rest on the open
conjecture `fullRound_commutes_iff_id` (DRAFT-SORRY) and may additionally use
`sorryAx`. The list must match exactly: any other theorem using sorryAx fails,
and a listed theorem that no longer uses sorryAx fails too (remove it here and
from ALLOWED_SORRY in checks/scan_sorry.py).

Security-package twin of proofs/doubledeal/check_axioms.py. Run after
`lake build` in proofs/doubledeal/security.
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PKG = Path(__file__).resolve().parent
FILES = ["Axioms.lean"]
KNOWN_SORRY = {
    "DoubleDeal.Security.fullRound_commutes_iff_id",  # the conjecture itself
    "DoubleDeal.Security.encrypt6_commutes_iff_id",   # reduces to it (round_of_encrypt6)
}


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
    known = 0
    for name in KNOWN_SORRY - set(expected):
        print(f"check_axioms: KNOWN_SORRY entry {name} is not listed in {fname}", file=sys.stderr)
        bad += 1
    for name in expected:
        if name not in seen:
            print(f"check_axioms: no axiom report for {name}", file=sys.stderr)
            bad += 1
        elif name in KNOWN_SORRY:
            extra = seen[name] - ALLOWED - {"sorryAx"}
            if extra:
                print(f"FAIL {name}: uses {sorted(extra)}", file=sys.stderr)
                bad += 1
            elif "sorryAx" not in seen[name]:
                print(f"FAIL {name}: listed in KNOWN_SORRY but no longer uses sorryAx; "
                      "remove it from KNOWN_SORRY", file=sys.stderr)
                bad += 1
            else:
                known += 1
                print(f"known-sorry {name}: {sorted(seen[name])}")
        elif seen[name] - ALLOWED:
            print(f"FAIL {name}: uses {sorted(seen[name] - ALLOWED)}", file=sys.stderr)
            bad += 1
        else:
            print(f"ok {name}: {sorted(seen[name])}")
    clean = len(expected) - bad - known
    print(f"check_axioms: {fname}: {clean}/{len(expected)} clean, "
          f"{known} known-sorry (allowlisted), {bad} failing")
    return bad


def main() -> int:
    bad = sum(audit(f) for f in FILES)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
