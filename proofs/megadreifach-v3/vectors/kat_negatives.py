#!/usr/bin/env python3
"""Planted negatives for the v3 compiled KAT run (`lake exe megadreifach_v3_kat`).

    python3 proofs/megadreifach-v3/vectors/kat_negatives.py   # after `lake build` in proofs/megadreifach-v3/lean

Copies the v3 Lean package (with its built .lake), the v2 Link 2 sources its
MegaDreifachLink lib re-elaborates (../../megadreifach/lean, without .lake) and
proofs/audit to a temporary directory, keeping their relative layout. There, for each case,
it edits MegaDreifachV3/Vectors.lean, rebuilds the exe and runs it. Each case must end the
way its planted fault predicts, by exit code AND by the runner's own summary lines, so a
crash (a non-zero exit without the summary) never counts as an expected failure:
- "honest": unmodified; exit 0, "MegaDreifach v3 KATs: 52/52 checks passed", no "FAIL:" line;
- "bad digest": one hex digit of vec_empty's digest changed; exit 1 and "N/52 checks passed"
  with N < 52;
- "bad body digest": the same for body_0;
- "empty lists": `vectors` and `bodyVectors` emptied (the remaining checks all pass); exit 1
  and "FAIL: expected 52 checks", because the run requires exactly `expectedChecks` (52).
The repository is not modified.

    python3 proofs/megadreifach-v3/vectors/kat_negatives.py --selftest-crash

runs the same cases but invokes a runner that does not exist (`lake exe` of a missing
target: a crash with no summary line) and passes only if every case is reported as an
error, i.e. the harness cannot mistake a crash for a planted failure.
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


SUMMARY = re.compile(r"^MegaDreifach v3 KATs: (\d+)/(\d+) checks passed$", re.M)
EXPECTED = 52
RUNNER = "megadreifach_v3_kat"
MISSING_RUNNER = "megadreifach_v3_kat_does_not_exist"


def summary(out: str) -> tuple[int, int] | None:
    """(passed, ran) from the runner's summary line, or None if there is none."""
    m = SUMMARY.findall(out)
    return (int(m[-1][0]), int(m[-1][1])) if len(m) == 1 else None


def honest_ok(code: int, out: str) -> str | None:
    if code != 0:
        return f"exit {code}, want 0"
    if summary(out) != (EXPECTED, EXPECTED):
        return f"no '{EXPECTED}/{EXPECTED} checks passed' line"
    if "FAIL:" in out:
        return "unexpected 'FAIL:' line"
    return None


def bad_digest_ok(code: int, out: str) -> str | None:
    if code != 1:
        return f"exit {code}, want 1"
    sm = summary(out)
    if sm is None:
        return "no 'N/52 checks passed' line (crash?)"
    if not (sm[1] == EXPECTED and sm[0] < EXPECTED):
        return f"summary {sm[0]}/{sm[1]}, want N/{EXPECTED} with N < {EXPECTED}"
    return None


def empty_lists_ok(code: int, out: str) -> str | None:
    if code != 1:
        return f"exit {code}, want 1"
    if summary(out) is None:
        return "no 'checks passed' line (crash?)"
    if f"FAIL: expected {EXPECTED} checks" not in out:
        return f"no 'FAIL: expected {EXPECTED} checks' line"
    return None


CASES = [
    ("honest", lambda s: s, honest_ok),
    ("bad digest (vec_empty)", lambda s: flip_digest(s, "vec_empty"), bad_digest_ok),
    ("bad digest (body_0)", lambda s: flip_digest(s, "body_0"), bad_digest_ok),
    ("empty vector lists", empty_lists, empty_lists_ok),
]


def run_cases(runner: str) -> list[tuple[str, str | None, str]]:
    """[(case, problem or None, runner summary lines)] with `runner` as the exe to run."""
    results = []
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / "proofs"
        shutil.copytree(PKG, root / "megadreifach-v3", symlinks=True)
        shutil.copytree(V2_LEAN, root / "megadreifach" / "lean", symlinks=True,
                        ignore=shutil.ignore_patterns(".lake"))
        shutil.copytree(AUDIT, root / "audit", symlinks=True)
        lean = root / "megadreifach-v3" / "lean"
        honest = (lean / VEC).read_text()
        for name, edit, check in CASES:
            (lean / VEC).write_text(edit(honest))
            b = subprocess.run(["lake", "build", RUNNER], cwd=lean,
                               capture_output=True, text=True)
            if b.returncode != 0:
                results.append((name, "build failed: " + (b.stdout + b.stderr)[-2000:], ""))
                continue
            r = subprocess.run(["lake", "exe", runner], cwd=lean, capture_output=True, text=True)
            out = r.stdout
            lines = " | ".join(l for l in out.splitlines()
                               if "checks passed" in l or l.startswith("FAIL:"))
            if not lines:
                lines = "no summary; stderr: " + " ".join(r.stderr.split())[-200:]
            results.append((name, check(r.returncode, out), f"exit {r.returncode}; {lines}"))
    return results


def main() -> int:
    if sys.argv[1:] == ["--selftest-crash"]:
        results = run_cases(MISSING_RUNNER)
        flagged = 0
        for name, problem, info in results:
            print(f"{'ok  ' if problem else 'FAIL'} {name} with a crashing runner is "
                  f"{'reported as an error' if problem else 'NOT reported'}: {problem}; {info}")
            flagged += bool(problem)
        print(f"kat_negatives --selftest-crash: {flagged}/{len(results)} crash runs reported "
              "as errors")
        return 0 if flagged == len(results) == len(CASES) else 1
    if sys.argv[1:]:
        raise SystemExit("usage: kat_negatives.py [--selftest-crash]")
    results = run_cases(RUNNER)
    fails = 0
    for name, problem, info in results:
        print(f"{'FAIL' if problem else 'ok  '} {name}: {info}" + (f"; {problem}" if problem else ""))
        fails += bool(problem)
    print(f"kat_negatives: {len(CASES) - fails}/{len(CASES)} cases as expected")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
