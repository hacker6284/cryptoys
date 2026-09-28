#!/usr/bin/env python3
"""Axiom gate for the MegaDreifach Lean package (proofs/megadreifach/lean).

    python3 proofs/megadreifach/check_axioms.py          # default library (after `lake build`)
    python3 proofs/megadreifach/check_axioms.py heavy    # heavy library (after
                                                         # `lake build MegaDreifachHeavy`)

Modelled on proofs/doubledeal/check_axioms.py (security modes). Builds the small
non-default lean_lib `MegaDreifachAudit` (the `#audit_all` command), then runs
`lake env lean Axioms.lean` (or `AxiomsHeavy.lean`) in lean/ and parses the
"'X' depends on axioms: [...]" reports. `#audit_all` covers EVERY theorem declared
in a module under the root (`MegaDreifach` or `MegaDreifachHeavy`), private ones
included, and errors on any module file under the root that was not loaded.

Allowed: propext, Classical.choice, Quot.sound. Anything else (sorryAx,
Lean.ofReduceBool from native_decide, a user axiom) fails, as does an `axiom`
declared in the package, a Lean error, a report count that differs from the
`audited N` line, too few theorems, or a missing headline theorem. In the default
mode the heavy source must still declare the headline KAT theorems (so the
default job notices if the heavy target is dropped or renamed).
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN = Path(__file__).resolve().parent / "lean"
KATS = ["empty", "short_abc", "short_one", "edge_27", "edge_28", "edge_29",
        "multi_56", "multi_100"]
HEAVY_REQUIRED = {f"MegaDreifach.Link2.Kat.kat_{k}" for k in KATS}
PACKAGES = {
    "default": {
        "axioms": "Axioms.lean",
        "min": 500,  # sanity: the audit must actually see the library
        "required": {
            "MegaDreifach.Link2.v_Hash_refines",
            "MegaDreifach.Link2.v_Hash_refines_array",
            "MegaDreifach.Link2.v_MegaDreifach_refines",
            "MegaDreifach.Link2.v_Hash_eq_hashBlocks",
            "MegaDreifach.Link2.em_block_refines",
            "MegaDreifach.Link2.position_to_bytes_refines_gen",
            "MegaDreifach.Link2.even_perm_rank_big_refines_gen",
            "MegaDreifach.Link2.big_mul_gen_refines",
            "MegaDreifach.Link2.phi_chunk_refines",
            "MegaDreifach.Link2.pad_message_refines",
        },
    },
    "heavy": {
        "axioms": "AxiomsHeavy.lean",
        "min": len(HEAVY_REQUIRED),
        "required": HEAVY_REQUIRED,
    },
}
REPORT = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")


def heavy_source_problems():
    """The headline KAT theorems must be declared in MegaDreifachHeavy/."""
    text = "".join(re.sub(r"/-.*?-/", "", p.read_text(), flags=re.S)
                   for p in sorted((LEAN / "MegaDreifachHeavy").rglob("*.lean")))
    return [f"heavy source does not declare theorem kat_{k} (MegaDreifachHeavy/ dropped or renamed?)"
            for k in KATS if not re.search(rf"^theorem\s+kat_{k}\s", text, flags=re.M)]


def main(argv) -> int:
    pkg = argv[1] if len(argv) > 1 else "default"
    if pkg not in PACKAGES:
        print(f"usage: check_axioms.py [{'|'.join(PACKAGES)}]", file=sys.stderr)
        return 2
    cfg = PACKAGES[pkg]
    build = subprocess.run(["lake", "build", "MegaDreifachAudit"], cwd=LEAN,
                           capture_output=True, text=True)
    if build.returncode != 0:
        print(build.stdout + build.stderr, file=sys.stderr)
        print("check_axioms: could not build MegaDreifachAudit", file=sys.stderr)
        return 1
    proc = subprocess.run(["lake", "env", "lean", cfg["axioms"]], cwd=LEAN,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {pkg}: {cfg['axioms']} did not elaborate cleanly", file=sys.stderr)
        return 1
    seen = {}
    bad = []
    found = [(n, {a.strip() for a in axs.split(",") if a.strip()}) for n, axs in REPORT.findall(out)]
    found += [(n, set()) for n in re.findall(r"'(\S+?)' does not depend on any axioms", out)]
    # Keyed by the full constant name. Unlike DoubleDeal's security package there is
    # no allowlist by user-facing name, and this library reuses private helper names
    # across modules (`_private.<Module>.0.<name>`), which are distinct constants.
    for name, axs in found:
        if name in seen:
            bad.append(f"duplicate axiom report for {name}")
        seen[name] = axs
    m = re.findall(r"\baudited (\d+)\b", out)
    if len(m) != 1:
        print(out, file=sys.stderr)
        print("check_axioms: missing or repeated 'audited N' line", file=sys.stderr)
        return 1
    if int(m[0]) != len(found):
        print(f"check_axioms: Lean audited {m[0]} theorems but {len(found)} reports were parsed",
              file=sys.stderr)
        return 1
    if len(seen) < cfg["min"]:
        bad.append(f"only {len(seen)} theorems audited (expected at least {cfg['min']})")
    for name in sorted(cfg["required"] - set(seen)):
        bad.append(f"required theorem {name} was not reported by the audit")
    for name in re.findall(r"'(\S+?)' is an axiom declared in the package", out):
        bad.append(f"axiom declared in the package: {name}")
    if pkg == "default":
        bad += heavy_source_problems()
    ok = 0
    for name, axs in sorted(seen.items()):
        if axs - ALLOWED:
            bad.append(f"{name} uses {sorted(axs - ALLOWED)}")
        else:
            ok += 1
    for b in bad:
        print(f"check_axioms: FAIL {b}", file=sys.stderr)
    print(f"check_axioms: megadreifach {pkg}: {len(seen)} theorems audited, {ok} use only "
          f"{sorted(ALLOWED)}, {len(bad)} failures")
    if pkg == "default":
        print("check_axioms: the heavy library MegaDreifachHeavy (8 KAT witnesses) is NOT in "
              "this audit; it is audited by `check_axioms.py heavy` (CI job megadreifach-heavy)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
