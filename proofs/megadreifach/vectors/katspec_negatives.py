#!/usr/bin/env python3
"""Planted negatives for KatSpecCheck.lean, the generated check of the heavy KAT statements.

    python3 proofs/megadreifach/vectors/katspec_negatives.py   # after `lake build` (default lib)

Copies the MegaDreifach Lean package (with its built .lake) and proofs/audit to a
temporary directory. There it replaces every proof in MegaDreifachHeavy/Kat.lean by a
stub (so no KAT kernel evaluation is needed; the check only reads theorem TYPES and
attributes) and, for each case, plants a shadow or an `[init]` hook in Kat.lean and/or
MegaDreifach/Hex.lean (optionally a wrong digest in Vectors.lean). Then
`lake build MegaDreifachHeavy` (root: Kat only) must SUCCEED and
`lake env lean --run KatSpecCheck.lean` must FAIL for the stated reason:
- "stmt": a `kat_<name>` type is not the expected Expr (shadowed vec_* / hexBytes /
  v_Hash, including a `macro_rules` hijack), or kat_empty is an axiom;
- "init": the init scan finds a constant with `[init]` / `[builtin_init]`. The DHH case
  (an `@[init]` that exits 0 whenever the command line mentions Kat, plus a wrong
  vec_empty digest) runs on a warm .lake: the Kat "build" exits 0 and keeps the stale
  honest Kat.olean, the statements still match, and only the init scan catches it (it
  also shows the scan is not bypassed: `lean --run KatSpecCheck.lean` mentions Kat,
  and the hook did not run);
- "kat-error": Lean rejects the shadow (root redeclaration), or, with the CI step that
  deletes MegaDreifachHeavy build outputs first, the exit-0 hook leaves no Kat.olean.
The honest (unmodified) Kat.lean must pass. For init cases it also reports whether
scan_sorry.py flags the source. The repository is not modified.
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

EXIT_ON_KAT = ("@[init] def evilKatExit : IO Unit := do\n"
               "  let cmd ← IO.FS.readFile \"/proc/self/cmdline\"\n"
               "  if (cmd.splitOn \"Kat\").length > 1 then IO.Process.exit 0")

# name -> (lines added after `namespace MegaDreifach.Link2.Kat` in Kat.lean,
#          lines added before `end MegaDreifach` in Hex.lean,
#          extra imports for Kat.lean, proof of kat_empty (None: stub), expected outcome,
#          options: "warm" (rebuild honest Kat first), "baddigest", "delete" (CI deletion))
CASES = {
    "honest": ("", "", "", None, "pass", ()),
    "T1 open .. in def Vectors.vec_empty (Kat.lean)":
        (f"open MegaDreifach in def Vectors.vec_empty : Vectors.HashVec := {FAKE}", "", "", None, "stmt", ()),
    "T1 open .. in def Link2.Vectors.vec_empty (Hex.lean)":
        ("", "structure Link2.Vectors.Fake where\n  msgHex : String\n  digestHex : String\n"
             'open Nat in def Link2.Vectors.vec_empty : Link2.Vectors.Fake := ⟨"", "00"⟩', "", None, "stmt", ()),
    "T3 inductive Vectors | vec_empty + Vectors.msgHex/digestHex (Kat.lean)":
        ("inductive Vectors | vec_empty\n"
         'def Vectors.msgHex : Vectors → String := fun _ => ""\n'
         'def Vectors.digestHex : Vectors → String := fun _ => "00"', "", "", None, "stmt", ()),
    "T4 local hexBytes (Kat.lean)":
        ("def hexBytes (_ : String) : List Nat := []", "", "", None, "stmt", ()),
    "T5 local def Megadreifach.v_Hash, kat_empty by rfl (Kat.lean)":
        ("def Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) :=\n"
         "  .ok (embed (hexBytes Vectors.vec_empty.digestHex))", "", "", "rfl", "stmt", ()),
    "T5 def Megadreifach.v_Hash in namespace MegaDreifach (Hex.lean)":
        ("", "def Megadreifach.v_Hash (_ : Array Int) : Except String (Array Int) := .ok #[]", "", None, "stmt", ()),
    "T5 at root: def _root_.Megadreifach.v_Hash (Kat.lean)":
        ("def _root_.Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) := .ok #[]",
         "", "", None, "kat-error", ()),
    "T7 class Vectors where vec_empty + anonymous instance (Kat.lean)":
        (f"class Vectors where\n  vec_empty : {VH}\ninstance : Vectors := ⟨{FAKE}⟩", "", "", None, "stmt", ()),
    "T12 run_cmd declaring \"vec\" ++ \"_empty\" (Kat.lean)":
        ("open Lean Elab Command in\nrun_cmd do\n"
         '  let id := mkIdent (Name.mkStr `Vectors ("vec" ++ "_empty"))\n'
         f"  elabCommand (← `(def $id : {VH} := {FAKE}))", "", "import Lean\n", None, "stmt", ()),
    # A syntax hijack of the kind that neutered the former KatSpec.lean `#guard_expr` layer.
    "R1 T5 + macro_rules neutering #guard_expr (Kat.lean)":
        ("def Megadreifach.v_Hash (_ : Array Int) : Except SudoRt.Trap (Array Int) :=\n"
         "  .ok (embed (hexBytes Vectors.vec_empty.digestHex))\n"
         "macro_rules | `(#guard_expr $_a =ₛ $_b) => `(section end)", "", "", "rfl", "stmt", ()),
    "kat_empty as an axiom with the honest type (Kat.lean)":
        ("", "", "", None, "axiom", ()),
    "I1 DHH: @[init] exit 0 if cmdline mentions Kat (Hex.lean) + wrong vec_empty digest, warm .lake":
        ("", EXIT_ON_KAT, "", None, "init", ("warm", "baddigest")),
    "I2 same, after deleting MegaDreifachHeavy build outputs (CI step)":
        ("", EXIT_ON_KAT, "", None, "kat-error", ("warm", "baddigest", "delete")),
    "I3 harmless @[init] in Kat.lean itself":
        ("@[init] def katInitNoop : IO Unit := pure ()", "", "", None, "init", ()),
    "I4 @[init mkR] opaque ref (Hex.lean)":
        ("", "def mkR : IO Nat := pure 0\n@[init mkR] opaque initRef : Nat", "", None, "init", ()),
    "I5 attribute [init] after the def (Hex.lean)":
        ("", "def hexInitLater : IO Unit := pure ()\nattribute [init] hexInitLater", "", None, "init", ()),
    "I6 @[builtin_init] (Hex.lean)":
        ("", "@[builtin_init] def hexBuiltinInit : IO Unit := pure ()", "", None, "init", ()),
    "I7 initialize command (Hex.lean)":
        ("", "initialize pure ()", "", None, "init", ()),
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


def check(pkg: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", "env", "lean", "--run", "KatSpecCheck.lean"], cwd=pkg,
                          capture_output=True, text=True)


SCAN_SORRY = LEAN.parents[2] / "proofs" / "doubledeal" / "security" / "checks" / "scan_sorry.py"


def main() -> int:
    doc = json.loads(json_to_lean.DEFAULT_JSON.read_text())
    kat_src = (LEAN / "MegaDreifachHeavy" / "Kat.lean").read_text()
    hex_src = (LEAN / "MegaDreifach" / "Hex.lean").read_text()
    vec_src = (LEAN / "MegaDreifach" / "Vectors.lean").read_text()
    good_digest = next(v["digest_hex"] for v in doc["vectors"] if v["name"] == "empty")
    anchor = "namespace MegaDreifach.Link2.Kat\n"
    assert anchor in kat_src and "\nend MegaDreifach\n" in hex_src and good_digest in vec_src
    failed = 0
    with tempfile.TemporaryDirectory(prefix="katspec-neg-") as tmp:
        pkg = Path(tmp) / "proofs" / "megadreifach" / "lean"
        shutil.copytree(LEAN, pkg, symlinks=True)
        shutil.copytree(AUDIT, Path(tmp) / "proofs" / "audit", symlinks=True)
        kat_f, hex_f, vec_f = (pkg / "MegaDreifachHeavy" / "Kat.lean", pkg / "MegaDreifach" / "Hex.lean",
                               pkg / "MegaDreifach" / "Vectors.lean")
        for what, (kat_add, hex_add, imports, proof, want, opts) in CASES.items():
            if "warm" in opts:  # an honest, up-to-date (stubbed) Kat.olean in the cache
                kat_f.write_text(stub_kat(kat_src, None)); hex_f.write_text(hex_src); vec_f.write_text(vec_src)
                assert lake(pkg, "MegaDreifachHeavy").returncode == 0
            kat = stub_kat(kat_src, proof)
            if kat_add:
                kat = kat.replace(anchor, anchor + "\n" + kat_add + "\n", 1)
            kat = imports + kat
            hexs = hex_src.replace("\nend MegaDreifach\n", "\n" + hex_add + "\n\nend MegaDreifach\n", 1) \
                if hex_add else hex_src
            hex_f.write_text(hexs)
            vec_f.write_text(vec_src.replace(good_digest, "00" + good_digest[2:], 1) if "baddigest" in opts
                             else vec_src)
            if want == "axiom":
                kat = re.sub(r"theorem kat_empty (.*?) := sorry", r"axiom kat_empty \1", kat, count=1, flags=re.S)
            kat_f.write_text(kat)
            if "delete" in opts:
                for d in ("lib", "ir"):
                    for q in (pkg / ".lake" / "build" / d).glob("MegaDreifachHeavy*"):
                        shutil.rmtree(q) if q.is_dir() else q.unlink()
            lint = json_to_lean.kat_text_problems(doc, kat)
            extra = ""
            if want == "init" or "delete" in opts:
                sc = subprocess.run([sys.executable, str(SCAN_SORRY), "--root", str(kat_f), "--root", str(hex_f)],
                                    capture_output=True, text=True)
                hits = re.findall(r"forbidden (\[\w+\] attribute|initialize|builtin_initialize)", sc.stderr)
                extra = f"; scan_sorry: {'flags ' + ', '.join(sorted(set(hits))) if hits else 'does not flag it'}"
            k = lake(pkg, "MegaDreifachHeavy")
            k_err = [l for l in (k.stdout + k.stderr).splitlines() if "error" in l]
            if want == "kat-error":
                ok = k.returncode != 0
                how = f"Kat build fails: {k_err[0].strip()[:160] if k_err else '?'}"
            elif k.returncode:
                ok, how = False, f"Kat.lean itself did not build: {k_err[:2]}"
            else:
                c = check(pkg)
                c_bad = sorted(set(re.findall(r"FAIL MegaDreifach\.Link2\.Kat\.(kat_\w+)", c.stderr)))
                inits = re.findall(r"FAIL init attribute: (\S+): (\S+)", c.stderr)
                ran = "init scan:" in c.stdout
                parts = []
                if inits:
                    parts.append("init scan: " + ", ".join(f"{d} ({m})" for m, d in inits))
                if c_bad:
                    parts.append(f"statement: {', '.join(c_bad)}")
                if not ran:
                    parts.append("did not run to completion: " + " | ".join(c.stderr.strip().splitlines()[-2:])[:300])
                chk = (f"KatSpecCheck fails [{'; '.join(parts)}]" if c.returncode
                       else f"KatSpecCheck passes{'' if ran else ' WITHOUT RUNNING (exit 0 early)'}")
                how = f"Kat builds (text lint: {'passes' if not lint else 'FAILS'}); {chk}"
                if want == "pass":
                    ok = c.returncode == 0 and ran and not inits
                elif want == "init":
                    ok = c.returncode != 0 and ran and bool(inits)
                else:  # "stmt" / "axiom"
                    ok = c.returncode != 0 and ran and bool(c_bad) and not inits
            failed += not ok
            print(f"katspec_negatives: {'ok  ' if ok else 'FAIL'} {what}: {how}{extra}")
    print(f"katspec_negatives: {len(CASES) - failed}/{len(CASES)} cases as expected")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
