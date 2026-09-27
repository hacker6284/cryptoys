#!/usr/bin/env python3
"""Axiom gate for the DoubleDeal Lean packages.

    python3 proofs/doubledeal/check_axioms.py            # core package (lean/)
    python3 proofs/doubledeal/check_axioms.py security   # Mathlib package (security/)

Runs `lake env lean Axioms.lean` in the package (after `lake build`) and parses
the "'X' depends on axioms: [...]" reports. Allowed: propext, Classical.choice,
Quot.sound. Anything else (sorryAx, Lean.ofReduceBool from native_decide, a user
axiom) fails, as does a Lean error.

- core: audits the theorems listed with `#print axioms` in lean/Axioms.lean;
  each listed theorem must be reported.
- security: security/Axioms.lean audits EVERY theorem declared in a
  `DoubleDealSecurity.*` module, private ones included (`#audit_all`), and the
  parsed report count must equal the `audited N` line Lean prints. Exception, by exact name: the
  theorems in KNOWN_SORRY may also use `sorryAx`. A KNOWN_SORRY entry that is
  not reported, or no longer uses sorryAx, fails (stale allowlist); so does any
  `axiom` declared in the package, used or not.
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parent
PACKAGES = {
    "lean": {"dir": ROOT / "lean", "mode": "list", "known_sorry": set(), "min": 1},
    "security": {
        "dir": ROOT / "security",
        "mode": "all",
        # The open conjecture (DRAFT-SORRY) and the two theorems that rest on it.
        # Keep in sync with ALLOWED_SORRY in security/checks/scan_sorry.py.
        "known_sorry": {
            "DoubleDeal.Security.roundBody_covariant_iff_id",  # the conjecture
            "DoubleDeal.Security.fullRound_commutes_iff_id",   # its case tau = sigma
            "DoubleDeal.Security.encrypt6_commutes_iff_id",    # via round_covariant_of_encrypt6
        },
        "min": 100,  # sanity: the audit must actually see the package
    },
}
REPORT = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")


def main(argv) -> int:
    pkg = argv[1] if len(argv) > 1 else "lean"
    if pkg not in PACKAGES:
        print(f"usage: check_axioms.py [{'|'.join(PACKAGES)}]", file=sys.stderr)
        return 2
    cfg = PACKAGES[pkg]
    proc = subprocess.run(["lake", "env", "lean", "Axioms.lean"], cwd=cfg["dir"],
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {pkg}/Axioms.lean did not elaborate cleanly", file=sys.stderr)
        return 1
    seen = {}
    for name, axs in REPORT.findall(out):
        seen[name] = {a.strip() for a in axs.split(",") if a.strip()}
    for name in re.findall(r"'(\S+?)' does not depend on any axioms", out):
        seen[name] = set()
    if cfg["mode"] == "all":
        m = re.findall(r"\baudited (\d+)\b", out)
        if len(m) != 1:
            print(out, file=sys.stderr)
            print("check_axioms: missing or repeated 'audited N' line", file=sys.stderr)
            return 1
        if int(m[0]) != len(seen):
            print(f"check_axioms: Lean audited {m[0]} theorems but {len(seen)} reports were parsed",
                  file=sys.stderr)
            return 1
    if cfg["mode"] == "list":
        src = (cfg["dir"] / "Axioms.lean").read_text()
        expected = re.findall(r"^#print axioms\s+(\S+)", src, flags=re.M)
    else:
        expected = sorted(seen)
    known_sorry = cfg["known_sorry"]
    bad = []
    if len(expected) < cfg["min"]:
        bad.append(f"only {len(expected)} theorems audited (expected at least {cfg['min']})")
    for name in sorted(known_sorry - set(seen)):
        bad.append(f"KNOWN_SORRY entry {name} was not reported (renamed or removed?)")
    for name in re.findall(r"'(\S+?)' is an axiom declared in the package", out):
        bad.append(f"axiom declared in the package: {name}")
    ok = known = 0
    for name in expected:
        if name not in seen:
            bad.append(f"no axiom report for {name}")
            continue
        axs = seen[name]
        if name in known_sorry:
            if axs - ALLOWED - {"sorryAx"}:
                bad.append(f"{name} uses {sorted(axs - ALLOWED - {'sorryAx'})}")
            elif "sorryAx" not in axs:
                bad.append(f"{name} is in KNOWN_SORRY but no longer uses sorryAx; remove it")
            else:
                known += 1
                print(f"known-sorry {name}: {sorted(axs)}")
        elif axs - ALLOWED:
            bad.append(f"{name} uses {sorted(axs - ALLOWED)}")
        else:
            ok += 1
    for b in bad:
        print(f"check_axioms: FAIL {b}", file=sys.stderr)
    print(f"check_axioms: {pkg}: {len(expected)} theorems audited, {ok} use only "
          f"{sorted(ALLOWED)}, {known} known-sorry (allowlisted), {len(bad)} failures")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
