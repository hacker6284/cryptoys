#!/usr/bin/env python3
"""Planted negatives for the generated KAT statement guard MegaDreifachHeavy/KatSpec.lean.

    python3 proofs/megadreifach/vectors/katspec_negatives.py   # after `lake build` (default lib)

Copies the MegaDreifach Lean package (with its built .lake) and proofs/audit to a
temporary directory. There it replaces every proof in MegaDreifachHeavy/Kat.lean by a
stub (so no KAT kernel evaluation is needed; the guard only reads the theorem TYPES)
and, for each case, plants a shadow in Kat.lean and/or MegaDreifach/Hex.lean. Then:
- `lake build MegaDreifachHeavy.Kat` must SUCCEED (the shadow is valid Lean, and the
  KAT statement text is unchanged, so json_to_lean.py's text lint passes too); and
- `lake build MegaDreifachHeavy.KatSpec` must FAIL with a `#guard_expr` failure on the
  attacked `kat_<name>`, and
- `lake env lean --run KatSpecCheck.lean` (the syntax-independent copy) must FAIL.
One case (R1) neuters `#guard_expr` with a `macro_rules` in Kat.lean: there KatSpec.lean
passes and only KatSpecCheck.lean catches it. One case replaces the kat_empty theorem by
an `axiom` of the same type: only KatSpecCheck.lean (theorem required) and the axiom
audit catch that.
The honest (unmodified) Kat.lean must pass both. Cases whose shadow Lean itself
rejects (a root-level redeclaration) must fail already at Kat. The repository is not
modified; everything happens in the temporary copy.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import json_to_lean  # noqa: E402

LEAN = json_to_lean.LEAN_DIR
AUDIT = LEAN.parents[1] / "audit"
STUB = "sorry"  # test-only stub in the temporary copy (never in the repository)
VH = "MegaDreifach.Vectors.HashVec"
FAKE = f'{{ MegaDreifach.Vectors.vec_empty with digestHex := "00" }}'

# name -> (lines added after `namespace MegaDreifach.Link2.Kat` in Kat.lean,
#          lines added before `end MegaDreifach` in Hex.lean,
#          extra imports for Kat.lean, proof of kat_empty (None: stub), expected outcome)
CASES = {
    "honest": ("", "", "", None, "pass"),
    "T1 open .. in def Vectors.vec_empty (Kat.lean)":
        (f"open MegaDreifach in def Vectors.vec_empty : Vectors.HashVec := {FAKE}", "", "", None, "guard"),
    "T1 open .. in def Link2.Vectors.vec_empty (Hex.lean)":
        ("", "structure Link2.Vectors.Fake where\n  msgHex : String\n  digestHex : String\n"
             'open Nat in def Link2.Vectors.vec_empty : Link2.Vectors.Fake := ⟨"", "00"⟩', "", None, "guard"),
    "T3 inductive Vectors | vec_empty + Vectors.msgHex/digestHex (Kat.lean)":
        ("inductive Vectors | vec_empty\n"
         'def Vectors.msgHex : Vectors → String := fun _ => ""\n'
         'def Vectors.digestHex : Vectors → String := fun _ => "00"', "", "", None, "guard"),
    "T4 local hexBytes (Kat.lean)":
        ("def hexBytes (_ : String) : List Nat := []", "", "", None, "guard"),
    "T5 local def Megadreifach.v_Hash, kat_empty by rfl (Kat.lean)":
        ("def Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) :=\n"
         "  .ok (embed (hexBytes Vectors.vec_empty.digestHex))", "", "", "rfl", "guard"),
    "T5 def Megadreifach.v_Hash in namespace MegaDreifach (Hex.lean)":
        ("", "def Megadreifach.v_Hash (_ : Array Int) : Except String (Array Int) := .ok #[]", "", None, "guard"),
    "T5 at root: def _root_.Megadreifach.v_Hash (Kat.lean)":
        ("def _root_.Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) := .ok #[]",
         "", "", None, "kat-error"),
    "T7 class Vectors where vec_empty + anonymous instance (Kat.lean)":
        (f"class Vectors where\n  vec_empty : {VH}\ninstance : Vectors := ⟨{FAKE}⟩", "", "", None, "guard"),
    "T12 run_cmd declaring \"vec\" ++ \"_empty\" (Kat.lean)":
        ("open Lean Elab Command in\nrun_cmd do\n"
         '  let id := mkIdent (Name.mkStr `Vectors ("vec" ++ "_empty"))\n'
         f"  elabCommand (← `(def $id : {VH} := {FAKE}))", "", "import Lean\n", None, "guard"),
    # A deliberate syntax hijack: Kat.lean rewrites `#guard_expr .. =ₛ ..` to nothing, so
    # KatSpec.lean passes; KatSpecCheck.lean (no Kat-side syntax involved) must still fail.
    "R1 T5 + macro_rules neutering #guard_expr (Kat.lean)":
        ("def Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) :=\n"
         "  .ok (embed (hexBytes Vectors.vec_empty.digestHex))\n"
         "macro_rules | `(#guard_expr $_a =ₛ $_b) => `(section end)", "", "", "rfl", "check"),
    "kat_empty as an axiom with the honest type (Kat.lean)":
        ("", "", "", None, "axiom"),
}


def stub_kat(text: str, kat_empty_proof: str | None) -> str:
    """Replace the proof of every top-level theorem by STUB (kat_empty: optionally a real one)."""
    out, block = [], []

    def flush():
        if block:
            b = "\n".join(block)
            head = b[: b.index(" :=") + 3]
            name = re.match(r"theorem\s+(\S+)", b).group(1)
            proof = kat_empty_proof if (name == "kat_empty" and kat_empty_proof) else STUB
            out.append(f"{head} {proof}")
            block.clear()

    for line in text.split("\n"):
        if block:
            if line.strip() == "":
                flush()
                out.append(line)
            else:
                block.append(line)
        elif line.startswith("theorem "):
            block.append(line)
        else:
            out.append(line)
    flush()
    return "\n".join(out)


def lake(cwd: Path, target: str) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", "build", target], cwd=cwd, capture_output=True, text=True)


def main() -> int:
    doc = json.loads(json_to_lean.DEFAULT_JSON.read_text())
    kat_src = (LEAN / "MegaDreifachHeavy" / "Kat.lean").read_text()
    hex_src = (LEAN / "MegaDreifach" / "Hex.lean").read_text()
    anchor = "namespace MegaDreifach.Link2.Kat\n"
    assert anchor in kat_src and "\nend MegaDreifach\n" in hex_src
    failed = 0
    with tempfile.TemporaryDirectory(prefix="katspec-neg-") as tmp:
        pkg = Path(tmp) / "proofs" / "megadreifach" / "lean"
        shutil.copytree(LEAN, pkg, symlinks=True)
        shutil.copytree(AUDIT, Path(tmp) / "proofs" / "audit", symlinks=True)
        for what, (kat_add, hex_add, imports, proof, want) in CASES.items():
            kat = stub_kat(kat_src, proof)
            if kat_add:
                kat = kat.replace(anchor, anchor + "\n" + kat_add + "\n", 1)
            kat = imports + kat
            hexs = hex_src.replace("\nend MegaDreifach\n", "\n" + hex_add + "\n\nend MegaDreifach\n", 1) \
                if hex_add else hex_src
            (pkg / "MegaDreifach" / "Hex.lean").write_text(hexs)
            if want == "axiom":
                kat = re.sub(r"theorem kat_empty (.*?) := sorry", r"axiom kat_empty \1", kat, count=1, flags=re.S)
            (pkg / "MegaDreifachHeavy" / "Kat.lean").write_text(kat)
            lint = json_to_lean.kat_text_problems(doc, kat)
            k = lake(pkg, "MegaDreifachHeavy.Kat")
            k_err = [l for l in (k.stdout + k.stderr).splitlines() if "error" in l]
            if want == "kat-error":
                ok = k.returncode != 0
                how = f"Lean rejects the shadow: {k_err[0].strip()[:160] if k_err else '?'}"
            elif k.returncode:
                ok, how = False, f"Kat.lean itself did not build: {k_err[:2]}"
            else:
                s = lake(pkg, "MegaDreifachHeavy.KatSpec")
                out = s.stdout + s.stderr
                guard_fail = s.returncode != 0 and "failed: type_of%" in out
                attacked = sorted(set(re.findall(r"MegaDreifach\.Link2\.Kat\.(kat_\w+) =ₛ", out)))
                c = subprocess.run(["lake", "env", "lean", "--run", "KatSpecCheck.lean"], cwd=pkg,
                                   capture_output=True, text=True)
                c_bad = sorted(set(re.findall(r"FAIL MegaDreifach\.Link2\.Kat\.(kat_\w+)", c.stderr)))
                spec = (f"KatSpec #guard_expr fails on {', '.join(attacked) or '?'}" if guard_fail
                        else "KatSpec builds" if s.returncode == 0 else "KatSpec fails (not at a guard)")
                chk = (f"KatSpecCheck fails on {', '.join(c_bad) or '?'}" if c.returncode
                       else "KatSpecCheck passes")
                how = f"Kat builds (text lint: {'passes' if not lint else 'FAILS'}); {spec}; {chk}"
                if want == "pass":
                    ok = s.returncode == 0 and c.returncode == 0
                elif want == "guard":
                    ok = guard_fail and c.returncode != 0
                else:  # "check" / "axiom": KatSpecCheck must catch it
                    ok = c.returncode != 0
            failed += not ok
            print(f"katspec_negatives: {'ok  ' if ok else 'FAIL'} {what}: {how}")
    print(f"katspec_negatives: {len(CASES) - failed}/{len(CASES)} cases as expected")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
