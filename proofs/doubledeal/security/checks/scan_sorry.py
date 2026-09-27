#!/usr/bin/env python3
"""CI gate for the security package: no admit / native_decide anywhere, and
`sorry` only inside the listed known conjectures (by declaration name).

The allowlist must match exactly: a new sorry fails, and so does a listed
conjecture that no longer contains one (then remove it here and from
KNOWN_SORRY in check_axioms.py).
"""
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
# Known open conjectures (DRAFT-SORRY). Each must contain exactly one sorry.
ALLOWED_SORRY = {"fullRound_commutes_iff_id"}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example|structure)\s+([^\s(:{\[]+)?")


def strip_block_comments(text: str) -> str:
    # keep line numbers: replace comment bodies but keep newlines
    return re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)


def main() -> int:
    bad = []
    found = {}
    for path in sorted(PKG.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        decl = None
        text = strip_block_comments(path.read_text())
        for i, line in enumerate(text.splitlines(), 1):
            code = re.sub(r"--.*", "", line)
            m = DECL.match(code)
            if m:
                decl = (m.group(1) or "<anonymous>").split(".")[-1]
            if re.search(r"\b(admit|native_decide)\b", code):
                bad.append(f"{path}:{i}: admit/native_decide: {line.strip()}")
            for _ in re.finditer(r"\bsorry\b", code):
                if decl in ALLOWED_SORRY:
                    found[decl] = found.get(decl, 0) + 1
                else:
                    bad.append(f"{path}:{i}: sorry outside the allowlist (in {decl}): {line.strip()}")
    for name in sorted(ALLOWED_SORRY):
        n = found.get(name, 0)
        if n != 1:
            bad.append(f"allowlisted conjecture {name}: expected exactly 1 sorry, found {n} "
                       "(if proved, remove it from ALLOWED_SORRY and KNOWN_SORRY)")
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    print(f"security package: no admit/native_decide; sorry only in {sorted(ALLOWED_SORRY)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
