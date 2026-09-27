"""Selftest for the duplicate-owner check in `#audit_all` (DoubleDealSecurity/Audit.lean).

Writes a throwaway module DoubleDealSecurity/DupFixture.lean holding an identical copy of
PermKeys' `isDeck_mixColumns` (same namespace, opens and proof, without importing PermKeys),
builds it, runs `#audit_all DoubleDealSecurity` in an environment that loads both modules,
and requires exactly one DUP error, the full expected message (modules sorted). Lean 4.14 merges the two
identical imported theorems silently, so this is exactly the case the check exists for.
The fixture source and its build outputs are always removed again.
usage (from proofs/doubledeal/security): python3 checks/audit_dup_selftest.py
"""
import subprocess
import sys
from pathlib import Path

SEC = Path(__file__).resolve().parents[1]
FIX = SEC / "DoubleDealSecurity" / "DupFixture.lean"
RUNNER = SEC / "AuditDupSelftest.lean"
FIXTURE = """import DoubleDealSecurity.GridCycle

namespace DoubleDeal.Security

open DoubleDeal Relabel

theorem isDeck_mixColumns {h : Fin 52 → Nat} (hh : IsDeck h) : IsDeck (mixColumns h) := by
  simpa only [mixColumns_eq] using isDeck_scoop_gridW chooseSeat! freeChooser_v9 hh

end DoubleDeal.Security
"""
RUN = """import DoubleDealSecurity
import DoubleDealSecurity.DupFixture
import DoubleDealSecurity.Audit

#audit_all DoubleDealSecurity
"""
WANT = ("DUP DoubleDeal.Security.isDeck_mixColumns: declared in more than one module: "
        "DoubleDealSecurity.DupFixture, DoubleDealSecurity.PermKeys")


def main() -> int:
    if FIX.exists() or RUNNER.exists():
        print(f"audit_dup_selftest: {FIX.name} or {RUNNER.name} already exists; refusing to overwrite",
              file=sys.stderr)
        return 2
    try:
        FIX.write_text(FIXTURE)
        RUNNER.write_text(RUN)
        b = subprocess.run(["lake", "build", "DoubleDealSecurity.Audit", "DoubleDealSecurity.DupFixture"], cwd=SEC,
                           capture_output=True, text=True)
        if b.returncode != 0:
            print(b.stdout + b.stderr, file=sys.stderr)
            print("audit_dup_selftest: fixture did not build", file=sys.stderr)
            return 1
        r = subprocess.run(["lake", "env", "lean", RUNNER.name], cwd=SEC, capture_output=True, text=True)
        out = r.stdout + r.stderr
        dups = [l.split("error: ", 1)[-1] for l in out.splitlines() if "DUP " in l]
        if dups != [WANT]:
            print(out, file=sys.stderr)
            print(f"audit_dup_selftest: expected exactly the DUP error '{WANT}', got {dups}",
                  file=sys.stderr)
            return 1
        print(f"audit_dup_selftest: an identical duplicate in two modules gives: {dups[0]}")
        return 0
    finally:
        FIX.unlink(missing_ok=True)
        RUNNER.unlink(missing_ok=True)
        for p in (SEC / ".lake" / "build").rglob("DupFixture*"):
            p.unlink()


if __name__ == "__main__":
    sys.exit(main())
