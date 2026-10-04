#!/usr/bin/env python3
"""Planted negatives for the v3 compiled KAT run (`lake exe megadreifach_v3_kat`).

    python3 proofs/megadreifach-v3/vectors/kat_negatives.py   # after `lake build` in proofs/megadreifach-v3/lean

Copies the v3 Lean package (with its built .lake), the v2 Link 2 sources its
MegaDreifachLink lib re-elaborates (../../megadreifach/lean, without .lake) and
proofs/audit to a temporary directory, keeping their relative layout. There, for each case,
it edits MegaDreifachV3/Vectors.lean, rebuilds the exe and runs it:
- "honest": unmodified, the run must exit 0;
- "bad digest": one hex digit of vec_empty's digest changed, the run must exit non-zero;
- "bad body digest": one hex digit of body_0's digest changed, the run must exit non-zero;
- "empty lists": `vectors` and `bodyVectors` emptied (the remaining checks all pass), the
  run must exit non-zero because it requires exactly `expectedChecks` (52) checks.
The repository is not modified.
"""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent                      # proofs/megadreifach-v3
PROOFS = PKG.parent                    # proofs
V2_LEAN = PROOFS / "megadreifach" / "lean"
AUDIT = PROOFS / "audit"
VEC = Path("MegaDreifachV3") / "Vectors.lean"


def flip_digest(src: str, name: str) -> str:
    """Change the first hex digit of `name`'s digestHex."""
    m = re.search(rf'def {name} : \w+ where.*?digestHex := "([0-9a-f])', src, re.S)
    if not m:
        raise SystemExit(f"kat_negatives: no digestHex for {name}")
    i = m.start(1)
    return src[:i] + ("1" if src[i] == "0" else "0") + src[i + 1:]


def empty_lists(src: str) -> str:
    out, n = re.subn(r"def (vectors|bodyVectors) : List (\w+) :=\n  \[[^\]]*\]",
                     r"def \1 : List \2 :=\n  []", src)
    if n != 2:
        raise SystemExit(f"kat_negatives: expected 2 vector lists, found {n}")
    return out


CASES = [
    ("honest", lambda s: s, 0),
    ("bad digest (vec_empty)", lambda s: flip_digest(s, "vec_empty"), 1),
    ("bad digest (body_0)", lambda s: flip_digest(s, "body_0"), 1),
    ("empty vector lists", empty_lists, 1),
]


def main() -> int:
    fails = 0
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / "proofs"
        shutil.copytree(PKG, root / "megadreifach-v3", symlinks=True)
        shutil.copytree(V2_LEAN, root / "megadreifach" / "lean", symlinks=True,
                        ignore=shutil.ignore_patterns(".lake"))
        shutil.copytree(AUDIT, root / "audit", symlinks=True)
        lean = root / "megadreifach-v3" / "lean"
        honest = (lean / VEC).read_text()
        for name, edit, want in CASES:
            (lean / VEC).write_text(edit(honest))
            b = subprocess.run(["lake", "build", "megadreifach_v3_kat"], cwd=lean,
                               capture_output=True, text=True)
            if b.returncode != 0:
                print(f"FAIL {name}: build failed\n{(b.stdout + b.stderr)[-2000:]}")
                fails += 1
                continue
            r = subprocess.run(["lake", "exe", "megadreifach_v3_kat"], cwd=lean,
                               capture_output=True, text=True)
            got = 0 if r.returncode == 0 else 1
            last = [l for l in r.stdout.splitlines() if "checks passed" in l or l.startswith("FAIL:")]
            ok = got == want
            print(f"{'ok  ' if ok else 'FAIL'} {name}: exit {r.returncode} "
                  f"(want {'0' if want == 0 else 'non-zero'}); {' | '.join(last)}")
            fails += 0 if ok else 1
    print(f"kat_negatives: {len(CASES) - fails}/{len(CASES)} cases as expected")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
