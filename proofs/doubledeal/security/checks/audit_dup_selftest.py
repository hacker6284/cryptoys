"""Selftest for the duplicate-owner check in `#audit_all` (DoubleDealSecurity/Audit.lean).

Writes a throwaway module DoubleDealSecurity/DupFixture.lean holding an identical copy of
PermKeys' `isDeck_mixColumns` (same namespace, opens and proof, without importing PermKeys),
builds it, runs `#audit_all DoubleDealSecurity` in an environment that loads both modules,
and requires the error `DUP DoubleDeal.Security.isDeck_mixColumns`. Lean 4.14 merges the two
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
WANT = "DUP DoubleDeal.Security.isDeck_mixColumns"


def main() -> int:
    if FIX.exists() or RUNNER.exists():
        print(f"audit_dup_selftest: {FIX.name} or {RUNNER.name} already exists; refusing to overwrite",
              file=sys.stderr)
        return 2
    try:
        FIX.write_text(FIXTURE)
        RUNNER.write_text(RUN)
        b = subprocess.run(["lake", "build", "DoubleDealSecurity.DupFixture"], cwd=SEC,
                           capture_output=True, text=True)
        if b.returncode != 0:
            print(b.stdout + b.stderr, file=sys.stderr)
            print("audit_dup_selftest: fixture did not build", file=sys.stderr)
            return 1
        r = subprocess.run(["lake", "env", "lean", RUNNER.name], cwd=SEC, capture_output=True, text=True)
        out = r.stdout + r.stderr
        dups = [l for l in out.splitlines() if "DUP " in l]
        if not any(WANT in l for l in dups) or len(dups) != 1:
            print(out, file=sys.stderr)
            print(f"audit_dup_selftest: expected exactly one '{WANT}' error, got {len(dups)} DUP lines",
                  file=sys.stderr)
            return 1
        print(f"audit_dup_selftest: an identical duplicate in two modules gives: {dups[0].split('error: ')[-1]}")
        return 0
    finally:
        FIX.unlink(missing_ok=True)
        RUNNER.unlink(missing_ok=True)
        for p in (SEC / ".lake" / "build").rglob("DupFixture*"):
            p.unlink()


if __name__ == "__main__":
    sys.exit(main())
