#!/usr/bin/env python3
"""Axiom gate for the Lean proof packages (the single gate: DoubleDeal and MegaDreifach).

    python3 proofs/doubledeal/check_axioms.py            # core package (lean/)
    python3 proofs/doubledeal/check_axioms.py security   # Mathlib package (security/)
    python3 proofs/doubledeal/check_axioms.py security-heavy  # heavy library (after
                                          # `lake build DoubleDealSecurityHeavy`)
    python3 proofs/doubledeal/check_axioms.py v9-deprecated  # frozen v9 witness package
    python3 proofs/doubledeal/check_axioms.py v10-deprecated # frozen v10 GridCycle witness
    python3 proofs/doubledeal/check_axioms.py megadreifach   # proofs/megadreifach/lean (default lib)
    python3 proofs/doubledeal/check_axioms.py megadreifach-heavy  # its heavy library (after
                                          # `lake build MegaDreifachHeavy`)

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
- megadreifach / megadreifach-heavy: like security / security-heavy (mode "all",
  no KNOWN_SORRY) for proofs/megadreifach/lean, roots `MegaDreifach` and
  `MegaDreifachHeavy`. Its heavy source must declare the 8 headline `kat_*`
  theorems (MD_HEAVY_THEOREMS; the `step_*` / `alg_*` helpers need not be listed),
  checked in both modes.

`#audit_all` is the one command in the core-only package proofs/audit (required by
path by both the security package and MegaDreifach); in mode "all" this script
builds it (`lake build AuditAll`) before running the audit file.

Keying. By default reports are keyed by the user-facing name (a `private` theorem
under the name it is written with), and a private/public collision fails. With
`"key": "full"` they are keyed by the full constant name instead, so private
theorems of the same user name in different modules stay distinct constants.
MegaDreifach needs this: Lean generates private match-equation theorems
(`<def>.match_1.eq_1`, for Generated definitions) on demand in each module that
unfolds them, and a few modules keep small private helpers of the same name.
A public theorem whose name is also the user name of a private one fails in BOTH
keyings (a private copy of a public lemma, or two different lemmas under one
name); only private/private collisions are tolerated under `"key": "full"`.
Public names cannot collide with each other either way (Lean rejects them in one
environment, and `#audit_all` reports an identical re-declaration as `DUP`).

    python3 proofs/doubledeal/check_axioms.py --selftest   # keying rules on synthetic reports
"""
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parent
# Every theorem declared in security/DoubleDealSecurityHeavy/ (checked against the
# source in both security modes; audited by `security-heavy`).
# The heavy audit reports ONE MORE theorem than this registry lists:
# `DoubleDeal.Security.GridCycleSurvival.chunkOK.eq_1`, the equation lemma that Lean
# generates on demand when `of_chunks` unfolds `chunkOK` (`simp only [chunkOK, ...]`).
# It is not declared in the source, so it is not registered here; like every audited
# theorem it must still use only the allowed axioms.
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
    # DoubleDealSecurityHeavy/GridCycleSurvival.lean (GridCycle survival of v10Sym 0 3)
    "DoubleDeal.Security.GridCycleSurvival.of_chunks",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_0",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_1",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_2",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_3",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_0",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_1",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_2",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_3",
    "DoubleDeal.Security.GridCycleSurvival.check3_KC",
    "DoubleDeal.Security.GridCycleSurvival.check3_KS",
    "DoubleDeal.Security.GridCycleSurvival.gc_survival_v10Sym03_le",
    "DoubleDeal.Security.GridCycleSurvival.gc_survival_v10Sym_le",
    # DoubleDealSecurityHeavy/TrailBound.lean (unconditional multi-round characteristic bounds)
    "DoubleDeal.Security.TrailBound.trail_card_le_64",
    "DoubleDeal.Security.TrailBound.trail_card_le_4420_v10Sym",
    # DoubleDealSecurityHeavy/CovariantNarrow.lean and the generated CovariantNarrowChecks.lean
    # (check_e*, checks_all: cell0_witness.py --lean): the covariant round conjecture for
    # every transposition, and the reduction to the remaining prime-order case
    "DoubleDeal.Security.CovariantNarrow.goodPairsCheck_ok",
    "DoubleDeal.Security.CovariantNarrow.check_e1",
    "DoubleDeal.Security.CovariantNarrow.check_e2",
    "DoubleDeal.Security.CovariantNarrow.check_e3",
    "DoubleDeal.Security.CovariantNarrow.check_e4",
    "DoubleDeal.Security.CovariantNarrow.check_e5",
    "DoubleDeal.Security.CovariantNarrow.check_e6",
    "DoubleDeal.Security.CovariantNarrow.check_e7",
    "DoubleDeal.Security.CovariantNarrow.check_e8",
    "DoubleDeal.Security.CovariantNarrow.check_e9",
    "DoubleDeal.Security.CovariantNarrow.check_e10",
    "DoubleDeal.Security.CovariantNarrow.check_e11",
    "DoubleDeal.Security.CovariantNarrow.check_e12",
    "DoubleDeal.Security.CovariantNarrow.check_e13",
    "DoubleDeal.Security.CovariantNarrow.check_e14",
    "DoubleDeal.Security.CovariantNarrow.check_e15",
    "DoubleDeal.Security.CovariantNarrow.check_e16",
    "DoubleDeal.Security.CovariantNarrow.check_e17",
    "DoubleDeal.Security.CovariantNarrow.check_e18",
    "DoubleDeal.Security.CovariantNarrow.check_e19",
    "DoubleDeal.Security.CovariantNarrow.check_e20",
    "DoubleDeal.Security.CovariantNarrow.check_e21",
    "DoubleDeal.Security.CovariantNarrow.check_e22",
    "DoubleDeal.Security.CovariantNarrow.check_e23",
    "DoubleDeal.Security.CovariantNarrow.check_e24",
    "DoubleDeal.Security.CovariantNarrow.check_e25",
    "DoubleDeal.Security.CovariantNarrow.check_e26",
    "DoubleDeal.Security.CovariantNarrow.check_e27",
    "DoubleDeal.Security.CovariantNarrow.check_e28",
    "DoubleDeal.Security.CovariantNarrow.check_e29",
    "DoubleDeal.Security.CovariantNarrow.check_e30",
    "DoubleDeal.Security.CovariantNarrow.check_e31",
    "DoubleDeal.Security.CovariantNarrow.check_e32",
    "DoubleDeal.Security.CovariantNarrow.check_e33",
    "DoubleDeal.Security.CovariantNarrow.check_e34",
    "DoubleDeal.Security.CovariantNarrow.check_e35",
    "DoubleDeal.Security.CovariantNarrow.check_e36",
    "DoubleDeal.Security.CovariantNarrow.check_e37",
    "DoubleDeal.Security.CovariantNarrow.check_e38",
    "DoubleDeal.Security.CovariantNarrow.check_e39",
    "DoubleDeal.Security.CovariantNarrow.check_e40",
    "DoubleDeal.Security.CovariantNarrow.check_e41",
    "DoubleDeal.Security.CovariantNarrow.check_e42",
    "DoubleDeal.Security.CovariantNarrow.check_e43",
    "DoubleDeal.Security.CovariantNarrow.check_e44",
    "DoubleDeal.Security.CovariantNarrow.check_e45",
    "DoubleDeal.Security.CovariantNarrow.check_e46",
    "DoubleDeal.Security.CovariantNarrow.check_e47",
    "DoubleDeal.Security.CovariantNarrow.check_e48",
    "DoubleDeal.Security.CovariantNarrow.check_e49",
    "DoubleDeal.Security.CovariantNarrow.check_e50",
    "DoubleDeal.Security.CovariantNarrow.check_e51",
    "DoubleDeal.Security.CovariantNarrow.checks_all",
    "DoubleDeal.Security.CovariantNarrow.cov0Checks_ok",
    "DoubleDeal.Security.CovariantNarrow.roundBody_not_covariant_swap",
    "DoubleDeal.Security.CovariantNarrow.roundBody_not_commutes_swap",
    "DoubleDeal.Security.CovariantNarrow.roundBody_covariant_iff_id_of_prime_nonswap",
    "DoubleDeal.Security.CovariantNarrow.prime_nonswap_case_iff",
}
# proofs/megadreifach/lean: the 8 hash KATs in MegaDreifachHeavy/Kat.lean (the names
# match the vectors of primitives/hash/megadreifach/kats/megaminx_hash_kats.json;
# vectors/json_to_lean.py --check checks their statements against the JSON).
MD_LEAN = ROOT.parent / "megadreifach" / "lean"
MD_HEAVY_DIR = MD_LEAN / "MegaDreifachHeavy"
MD_HEAVY_THEOREMS = {f"MegaDreifach.Link2.Kat.kat_{k}" for k in
                     ["empty", "short_abc", "short_one", "edge_27", "edge_28", "edge_29",
                      "multi_56", "multi_100"]}
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
            # CovariantNarrow (roadmap M4): reductions of the open conjecture
            "DoubleDeal.Security.CovariantNarrow.prime_case_iff",
            "DoubleDeal.Security.CovariantNarrow.roundBody_covariant_iff_id_of_prime",
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
    "megadreifach": {
        "dir": MD_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
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
    "megadreifach-heavy": {
        "dir": MD_LEAN,
        "axioms": "AxiomsHeavy.lean",
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": len(MD_HEAVY_THEOREMS),
        "required": MD_HEAVY_THEOREMS,
    },
}
# Heavy-library registries, checked in both modes of each family (so the default
# job notices a dropped or renamed heavy target). exact: the source must declare
# exactly the registered theorems; otherwise it must declare at least them.
REGISTRIES = {
    "security": {"dir": HEAVY_DIR, "theorems": HEAVY_THEOREMS, "exact": True,
                 "what": "HEAVY_THEOREMS"},
    "megadreifach": {"dir": MD_HEAVY_DIR, "theorems": MD_HEAVY_THEOREMS, "exact": False,
                     "what": "MD_HEAVY_THEOREMS"},
}


def heavy_source_theorems(heavy_dir=HEAVY_DIR):
    """Fully qualified names of the theorems declared in a heavy source dir."""
    names = set()
    for path in sorted(heavy_dir.rglob("*.lean")):
        text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        ns = re.findall(r"^namespace\s+(\S+)", text, flags=re.M)
        prefix = (ns[0] + ".") if ns else ""
        for n in re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\s+([^\s(:{\[]+)",
                            text, flags=re.M):
            names.add(prefix + n)
    return names


def heavy_registry_problems(reg):
    src = heavy_source_theorems(reg["dir"])
    what, names, where = reg["what"], reg["theorems"], reg["dir"].name + "/"
    bad = []
    if reg["exact"]:
        bad += [f"heavy theorem {n} is not listed in {what}" for n in sorted(src - names)]
    bad += [f"{what} entry {n} is not declared in {where} (dropped or renamed?)"
            for n in sorted(names - src)]
    if not src:
        bad.append(f"no theorems found in {where} (heavy target missing?)")
    return bad


REPORT = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")
PRIVATE = re.compile(r"^_private\.[\w.']+?\.0\.")


def key_reports(found, full):
    """Key the (name, axioms) reports; return (seen, problems).

    default: private theorems under their user-facing name, so any two reports with
    the same user name (private/public or private/private) fail. full: keyed by the
    constant name (distinct private constants stay distinct), but a public theorem
    that shares its user name with a private one still fails."""
    seen, bad = {}, []
    for name, axs in found:
        key = name if full else PRIVATE.sub("", name)
        if key in seen:
            bad.append(f"duplicate audited name {key} (private/public collision)"
                       if not full else f"duplicate axiom report for {key}")
        seen[key] = axs
    if full:
        public = {n for n, _ in found if not PRIVATE.match(n)}
        for name, _ in found:
            user = PRIVATE.sub("", name)
            if user != name and user in public:
                bad.append(f"private theorem {name} has the user name of public theorem {user} "
                           "(private/public collision; keep one public lemma or rename)")
    return seen, bad


def selftest():
    """The keying rules on synthetic reports (no Lean needed)."""
    pa = "_private.MegaDreifach.Link2.A.0.MegaDreifach.Link2.h"
    pb = "_private.MegaDreifach.Link2.B.0.MegaDreifach.Link2.h"
    pub = "MegaDreifach.Link2.h"
    cases = [  # (reports, full, expected number of problems)
        ([pa, "X.y"], True, 0),
        ([pa, pb], True, 0),      # private/private: tolerated under key "full"
        ([pa, pb], False, 1),     # ... but not under user-name keying
        ([pa, pub], True, 1),     # private/public: fails under key "full"
        ([pub, pa, pb], True, 2),
        ([pa, pub], False, 1),    # ... and under user-name keying
    ]
    failed = 0
    for names, full, want in cases:
        _, bad = key_reports([(n, set()) for n in names], full)
        ok = len(bad) == want
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} key={'full' if full else 'user'} "
              f"{names}: {len(bad)} problem(s), expected {want}")
    return 1 if failed else 0


def main(argv) -> int:
    pkg = argv[1] if len(argv) > 1 else "lean"
    if pkg == "--selftest":
        return selftest()
    if pkg not in PACKAGES:
        print(f"usage: check_axioms.py [{'|'.join(PACKAGES)}]", file=sys.stderr)
        return 2
    cfg = PACKAGES[pkg]
    axioms = cfg.get("axioms", "Axioms.lean")
    if cfg["mode"] == "all":
        # `#audit_all` lives in the shared core-only package proofs/audit
        build = subprocess.run(["lake", "build", "AuditAll"], cwd=cfg["dir"],
                               capture_output=True, text=True)
        if build.returncode != 0:
            print(build.stdout + build.stderr, file=sys.stderr)
            print(f"check_axioms: {pkg}: could not build AuditAll (proofs/audit)", file=sys.stderr)
            return 1
    proc = subprocess.run(["lake", "env", "lean", axioms], cwd=cfg["dir"],
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {pkg}: {axioms} did not elaborate cleanly", file=sys.stderr)
        return 1
    found = [(n, {a.strip() for a in axs.split(",") if a.strip()}) for n, axs in REPORT.findall(out)]
    found += [(n, set()) for n in re.findall(r"'(\S+?)' does not depend on any axioms", out)]
    seen, bad = key_reports(found, cfg.get("key", "user") == "full")
    reports = len(found)
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
    for fam, reg in REGISTRIES.items():
        if pkg == fam or pkg == fam + "-heavy":
            bad += heavy_registry_problems(reg)
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
    if pkg == "megadreifach":
        print("check_axioms: megadreifach: the heavy library MegaDreifachHeavy (the "
              f"{len(MD_HEAVY_THEOREMS)} KAT theorems and their step lemmas) is NOT in this "
              "audit; it is audited by `check_axioms.py megadreifach-heavy` (CI job "
              "megadreifach-heavy)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
