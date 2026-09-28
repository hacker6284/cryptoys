#!/usr/bin/env python3
"""Axiom gate for the DoubleDeal Lean packages.

    python3 proofs/doubledeal/check_axioms.py            # core package (lean/)
    python3 proofs/doubledeal/check_axioms.py security   # Mathlib package (security/)
    python3 proofs/doubledeal/check_axioms.py security-heavy  # heavy library (after
                                          # `lake build DoubleDealSecurityHeavy`)
    python3 proofs/doubledeal/check_axioms.py v9-deprecated  # frozen v9 witness package
    python3 proofs/doubledeal/check_axioms.py v10-deprecated # frozen v10 GridCycle witness

Runs `lake env lean Axioms.lean` in the package (after `lake build`) and parses
the "'X' depends on axioms: [...]" reports. Allowed: propext, Classical.choice,
Quot.sound. Anything else (sorryAx, Lean.ofReduceBool from native_decide, a user
axiom) fails, as does a Lean error.

- core: audits the theorems listed with `#print axioms` in lean/Axioms.lean;
  each listed theorem must be reported.
- v9-deprecated: like core, for proofs/deprecated/doubledeal-v9/lean/Axioms.lean
  (the kernel-checked K♣↔Q♥ witness on the emitted frozen v9 encrypt).
- v10-deprecated: like core, for proofs/deprecated/doubledeal-v10/lean/Axioms.lean
  (the kernel-checked single-deck K♣↔K♦ witness on the emitted frozen v10 mix_columns).
- security: security/Axioms.lean audits EVERY theorem declared in a
  `DoubleDealSecurity.*` module, private ones included (`#audit_all`), and the
  parsed report count must equal the `audited N` line Lean prints. Exception, by exact name: the
  theorems in KNOWN_SORRY may also use `sorryAx`. A KNOWN_SORRY entry that is
  not reported, or no longer uses sorryAx, fails (stale allowlist); so does any
  `axiom` declared in the package, used or not.
- security-heavy: security/AxiomsHeavy.lean audits every theorem declared in a
  `DoubleDealSecurityHeavy.*` module (the heavy kernel witnesses, not a default
  build target), with the same rules and no KNOWN_SORRY. Every theorem declared in
  security/DoubleDealSecurityHeavy/ must be listed in HEAVY_THEOREMS and vice versa
  (checked in both security modes, so the default job cannot silently drop the
  heavy target), and every listed theorem must be reported by the heavy audit.
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parent
# Every theorem declared in security/DoubleDealSecurityHeavy/ (checked against the
# source in both security modes; audited by `security-heavy`).
HEAVY_DIR = ROOT / "security" / "DoubleDealSecurityHeavy"
HEAVY_THEOREMS = {
    "DoubleDeal.Security.realKey_enc_id",
    "DoubleDeal.Security.realKey_enc_v10Sym10",
    "DoubleDeal.Security.realKey_enc_v10Sym01",
    "DoubleDeal.Security.realKey_enc_v10Sym02",
    "DoubleDeal.Security.realKey_enc_v10Sym03",
    "DoubleDeal.Security.v10Sym10_not_commutes_realE",
    "DoubleDeal.Security.v10Sym01_not_commutes_realE",
    "DoubleDeal.Security.v10Sym02_not_commutes_realE",
    "DoubleDeal.Security.v10Sym03_not_commutes_realE",
    "DoubleDeal.Security.generated_encrypt_realKey_not_v10Sym_equivariant",
}
PACKAGES = {
    "lean": {"dir": ROOT / "lean", "mode": "list", "known_sorry": set(), "min": 1},
    "v9-deprecated": {"dir": ROOT.parent / "deprecated" / "doubledeal-v9" / "lean", "mode": "list",
                      "known_sorry": set(), "min": 1},
    "v10-deprecated": {"dir": ROOT.parent / "deprecated" / "doubledeal-v10" / "lean", "mode": "list",
                       "known_sorry": set(), "min": 1},
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
        # Headline theorems that must be reported (and axiom-clean) by the audit.
        "required": {
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_le",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_le'",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_threeCycle",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_lower",
        },
    },
    "security-heavy": {
        "dir": ROOT / "security",
        "axioms": "AxiomsHeavy.lean",
        "mode": "all",
        "known_sorry": set(),
        "min": 1,
        "required": HEAVY_THEOREMS,
    },
}


def heavy_source_theorems():
    """Fully qualified names of the theorems declared in DoubleDealSecurityHeavy/."""
    names = set()
    for path in sorted(HEAVY_DIR.rglob("*.lean")):
        text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        ns = re.findall(r"^namespace\s+(\S+)", text, flags=re.M)
        prefix = (ns[0] + ".") if ns else ""
        for n in re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\s+([^\s(:{\[]+)",
                            text, flags=re.M):
            names.add(prefix + n)
    return names


def heavy_registry_problems():
    src = heavy_source_theorems()
    bad = [f"heavy theorem {n} is not listed in HEAVY_THEOREMS" for n in sorted(src - HEAVY_THEOREMS)]
    bad += [f"stale HEAVY_THEOREMS entry {n} (not declared in DoubleDealSecurityHeavy/)"
            for n in sorted(HEAVY_THEOREMS - src)]
    if not src:
        bad.append("no theorems found in DoubleDealSecurityHeavy/ (heavy target missing?)")
    return bad


REPORT = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")


def main(argv) -> int:
    pkg = argv[1] if len(argv) > 1 else "lean"
    if pkg not in PACKAGES:
        print(f"usage: check_axioms.py [{'|'.join(PACKAGES)}]", file=sys.stderr)
        return 2
    cfg = PACKAGES[pkg]
    axioms = cfg.get("axioms", "Axioms.lean")
    proc = subprocess.run(["lake", "env", "lean", axioms], cwd=cfg["dir"],
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {pkg}: {axioms} did not elaborate cleanly", file=sys.stderr)
        return 1
    seen = {}
    reports = 0
    bad = []
    found = [(n, {a.strip() for a in axs.split(",") if a.strip()}) for n, axs in REPORT.findall(out)]
    found += [(n, set()) for n in re.findall(r"'(\S+?)' does not depend on any axioms", out)]
    for name, axs in found:
        # audit private theorems under their user-facing name, in every mode;
        # a private and a public theorem with the same user name must not merge
        user = re.sub(r"^_private\.[\w.']+?\.0\.", "", name)
        if user in seen:
            bad.append(f"duplicate audited name {user} (private/public collision)")
        seen[user] = axs
        reports += 1
    if cfg["mode"] == "all":
        m = re.findall(r"\baudited (\d+)\b", out)
        if len(m) != 1:
            print(out, file=sys.stderr)
            print("check_axioms: missing or repeated 'audited N' line", file=sys.stderr)
            return 1
        if int(m[0]) != reports:
            print(f"check_axioms: Lean audited {m[0]} theorems but {reports} reports were parsed",
                  file=sys.stderr)
            return 1
    if cfg["mode"] == "list":
        src = (cfg["dir"] / "Axioms.lean").read_text()
        expected = re.findall(r"^#print axioms\s+(\S+)", src, flags=re.M)
    else:
        expected = sorted(seen)
    known_sorry = cfg["known_sorry"]
    if len(expected) < cfg["min"]:
        bad.append(f"only {len(expected)} theorems audited (expected at least {cfg['min']})")
    if pkg.startswith("security"):
        bad += heavy_registry_problems()
    for name in sorted(cfg.get("required", set()) - set(seen)):
        bad.append(f"required theorem {name} was not reported by the audit")
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
    if pkg == "security":
        print(f"check_axioms: security: the {len(HEAVY_THEOREMS)} theorems of the heavy library "
              "DoubleDealSecurityHeavy are NOT in this audit; they are audited separately by "
              "`check_axioms.py security-heavy` (CI job doubledeal-security-heavy)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
