"""Selftest for the duplicate-owner check in `#audit_all` (DoubleDealSecurity/Audit.lean).

Writes throwaway modules under DoubleDealSecurity/, builds them, runs
`#audit_all DoubleDealSecurity` in an environment that loads all of them, and requires the
DUP errors to be exactly WANT (Lean 4.14 merges identical imported theorems silently, so the
constant table alone cannot show these duplicates):
- DupFixture: an identical copy of PermKeys' `isDeck_mixColumns` (same namespace, opens and
  proof, without importing PermKeys). Must be reported.
- ZfxH1, ZfxH2: each declares an identical `theorem zfxH.eq_1 : True`, where `zfxH` is a
  theorem, so the name is a real user declaration, not a reserved one. Must be reported.
- ZfxUseA, ZfxUseB: each uses `zfxF.eq_unfold` and `induction ... using zfxF.induct` of the
  structurally recursive `zfxF` (ZfxBase), so both modules generate those reserved names on
  demand. Must NOT be reported (no DUP line for `zfxF.`).
All fixture sources and their build outputs are removed again.
usage (from proofs/doubledeal/security): python3 checks/audit_dup_selftest.py
"""
import subprocess
import sys
from pathlib import Path

SEC = Path(__file__).resolve().parents[1]
LIB = SEC / "DoubleDealSecurity"
RUNNER = SEC / "AuditDupSelftest.lean"

DUP_ISDECK = """import DoubleDealSecurity.GridCycle

namespace DoubleDeal.Security

open DoubleDeal Relabel

theorem isDeck_mixColumns {h : Fin 52 → Nat} (hh : IsDeck h) : IsDeck (mixColumns h) := by
  simpa only [mixColumns_eq] using isDeck_scoop_gridW chooseSeat! freeChooser hh

end DoubleDeal.Security
"""
ZFX_BASE = """namespace ZfxFixture

def zfxF : Nat → Nat
  | 0 => 0
  | n + 1 => zfxF n + 1

theorem zfxH : True := trivial

end ZfxFixture
"""
ZFX_USE = """import DoubleDealSecurity.ZfxBase

namespace ZfxFixture

theorem zfxF_id_{tag} (n : Nat) : zfxF n = n := by
  induction n using zfxF.induct with
  | case1 => rw [zfxF.eq_unfold]
  | case2 n ih => rw [zfxF.eq_unfold]; simp [ih]

end ZfxFixture
"""
ZFX_H = """import DoubleDealSecurity.ZfxBase

namespace ZfxFixture

theorem zfxH.eq_1 : True := trivial

end ZfxFixture
"""
FIX = [
    ("DupFixture", DUP_ISDECK),
    ("ZfxBase", ZFX_BASE),
    ("ZfxUseA", ZFX_USE.format(tag="A")),
    ("ZfxUseB", ZFX_USE.format(tag="B")),
    ("ZfxH1", ZFX_H),
    ("ZfxH2", ZFX_H),
]
MODS = [f"DoubleDealSecurity.{name}" for name, _ in FIX]
RUN = ("import DoubleDealSecurity\n" + "".join(f"import {m}\n" for m in MODS)
       + "import DoubleDealSecurity.Audit\n\n#audit_all DoubleDealSecurity\n")
PREFIX = "declared in more than one module: "
WANT = sorted([
    "DUP DoubleDeal.Security.isDeck_mixColumns: " + PREFIX
    + "DoubleDealSecurity.DupFixture, DoubleDealSecurity.PermKeys",
    "DUP ZfxFixture.zfxH.eq_1: " + PREFIX + "DoubleDealSecurity.ZfxH1, DoubleDealSecurity.ZfxH2",
])


def main() -> int:
    paths = [LIB / f"{name}.lean" for name, _ in FIX] + [RUNNER]
    if any(p.exists() for p in paths):
        print("audit_dup_selftest: a fixture file already exists; refusing to overwrite",
              file=sys.stderr)
        return 2
    try:
        for name, src in FIX:
            (LIB / f"{name}.lean").write_text(src)
        RUNNER.write_text(RUN)
        b = subprocess.run(["lake", "build", "DoubleDealSecurity.Audit", *MODS], cwd=SEC,
                           capture_output=True, text=True)
        if b.returncode != 0:
            print(b.stdout + b.stderr, file=sys.stderr)
            print("audit_dup_selftest: fixtures did not build", file=sys.stderr)
            return 1
        r = subprocess.run(["lake", "env", "lean", RUNNER.name], cwd=SEC,
                           capture_output=True, text=True)
        out = r.stdout + r.stderr
        dups = sorted(l.split("error: ", 1)[-1] for l in out.splitlines() if "DUP " in l)
        bad = []
        if any("zfxF." in d for d in dups):
            bad.append("false positive on reserved zfxF.* names")
        if dups != WANT:
            bad.append(f"expected exactly {WANT}, got {dups}")
        if bad:
            print(out, file=sys.stderr)
            for msg in bad:
                print(f"audit_dup_selftest: {msg}", file=sys.stderr)
            return 1
        for d in dups:
            print(f"audit_dup_selftest: reported: {d}")
        print("audit_dup_selftest: no DUP for the on-demand zfxF.eq_unfold / zfxF.induct")
        return 0
    finally:
        for p in paths:
            p.unlink(missing_ok=True)
        stems = tuple(name for name, _ in FIX)
        for p in (SEC / ".lake" / "build").rglob("*"):
            if p.is_file() and p.name.split(".")[0] in stems:
                p.unlink()


if __name__ == "__main__":
    sys.exit(main())
