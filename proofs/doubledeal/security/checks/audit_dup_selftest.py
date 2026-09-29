"""Selftest for the duplicate-owner check in `#audit_all` (proofs/audit/AuditAll.lean).

Copies the security package (with its built .lake; .lake/packages, i.e. Mathlib, is
symlinked, not copied), ../lean (DoubleDeal) and proofs/audit to a temporary directory,
writes throwaway modules under DoubleDealSecurity/ THERE, builds them, runs
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
The source tree is never written; the temporary copy is deleted afterwards.
usage (from proofs/doubledeal/security): python3 checks/audit_dup_selftest.py
"""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SRC_SEC = Path(__file__).resolve().parents[1]          # proofs/doubledeal/security
PROOFS = SRC_SEC.parents[1]                            # proofs/

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
       + "import AuditAll\n\n#audit_all DoubleDealSecurity\n")
PREFIX = "declared in more than one module: "
WANT = sorted([
    "DUP DoubleDeal.Security.isDeck_mixColumns: " + PREFIX
    + "DoubleDealSecurity.DupFixture, DoubleDealSecurity.PermKeys",
    "DUP ZfxFixture.zfxH.eq_1: " + PREFIX + "DoubleDealSecurity.ZfxH1, DoubleDealSecurity.ZfxH2",
])


def copy_packages(tmp: Path) -> Path:
    """Copy security (minus .lake/packages, which is symlinked), ../lean and proofs/audit
    into `tmp`, keeping their relative layout (the lakefiles require them by path)."""
    sec = tmp / "doubledeal" / "security"
    shutil.copytree(SRC_SEC, sec, symlinks=True,
                    ignore=lambda d, names: ["packages"] if Path(d) == SRC_SEC / ".lake" else [])
    pkgs = SRC_SEC / ".lake" / "packages"
    if pkgs.exists():
        (sec / ".lake" / "packages").symlink_to(pkgs, target_is_directory=True)
    shutil.copytree(PROOFS / "doubledeal" / "lean", tmp / "doubledeal" / "lean", symlinks=True)
    shutil.copytree(PROOFS / "audit", tmp / "audit", symlinks=True)
    return sec


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="audit-dup-") as tmp:
        sec = copy_packages(Path(tmp))
        lib, runner = sec / "DoubleDealSecurity", sec / "AuditDupSelftest.lean"
        if any((lib / f"{name}.lean").exists() for name, _ in FIX) or runner.exists():
            print("audit_dup_selftest: a fixture name is already a module of the package",
                  file=sys.stderr)
            return 2
        for name, src in FIX:
            (lib / f"{name}.lean").write_text(src)
        runner.write_text(RUN)
        b = subprocess.run(["lake", "build", "AuditAll", *MODS], cwd=sec,
                           capture_output=True, text=True)
        if b.returncode != 0:
            print(b.stdout + b.stderr, file=sys.stderr)
            print("audit_dup_selftest: fixtures did not build", file=sys.stderr)
            return 1
        r = subprocess.run(["lake", "env", "lean", runner.name], cwd=sec,
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


if __name__ == "__main__":
    sys.exit(main())
