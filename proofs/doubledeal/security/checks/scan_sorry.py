#!/usr/bin/env python3
"""CI gate for the security package: no admit / native_decide / sorryAx / axiom
declarations anywhere, and
`sorry` only inside the listed known conjectures (by declaration name).

The allowlist must match exactly: a new sorry fails, and so does a listed
conjecture that no longer contains one (then remove it here and from
KNOWN_SORRY in ../check_axioms.py).
"""
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
# Known open conjectures (DRAFT-SORRY). Each must contain exactly one sorry.
ALLOWED_SORRY = {"roundBody_covariant_iff_id"}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example|structure)\s+([^\s(:{\[]+)?")


# `let rec f ...` / `have f ... :=` helpers inside a declaration
HELPER = re.compile(r"^\s+(?:let\s+rec|have)\s+([A-Za-z_][\w'.]*)\b")
# an item of a `where` block: `  f (x : α) : β := ...`
WHERE_ITEM = re.compile(r"^\s+([A-Za-z_][\w'.]*)\b[^:=|]*(?::[^=]|:=)")


def strip_block_comments(text: str) -> str:
    # keep line numbers: replace comment bodies but keep newlines
    return re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)


def main() -> int:
    bad = []
    found = {}
    for path in sorted(PKG.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        decl = None      # current top-level declaration
        top = None
        in_where = False
        helper_indent = None
        text = strip_block_comments(path.read_text())
        for i, line in enumerate(text.splitlines(), 1):
            code = re.sub(r"--.*", "", line)
            m = DECL.match(code)
            if m:
                top = decl = (m.group(1) or "<anonymous>").split(".")[-1]
                in_where = False
                helper_indent = None
            elif top is not None:
                # helpers get their own name, so a sorry in a helper is neither
                # attributed to nor counted for the allowlisted parent
                indent = len(code) - len(code.lstrip())
                if helper_indent is not None and code.strip() and indent <= helper_indent:
                    decl, helper_indent = top, None   # left the `have`/`let rec` body
                h = HELPER.match(code)
                if h:
                    decl, helper_indent = f"{top}.{h.group(1)}", indent
                elif in_where:
                    w = WHERE_ITEM.match(code)
                    if w:
                        decl = f"{top}.{w.group(1)}"
            if re.search(r"\bwhere\b", code) and top is not None:
                in_where = True
                w = re.search(r"\bwhere\s+([A-Za-z_][\w'.]*)", code)
                if w:
                    decl = f"{top}.{w.group(1)}"
            if re.search(r"\b(admit|native_decide|sorryAx)\b", code):
                bad.append(f"{path}:{i}: admit/native_decide/sorryAx: {line.strip()}")
            if re.match(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*axiom\b", code):
                bad.append(f"{path}:{i}: axiom declaration: {line.strip()}")
            for _ in re.finditer(r"\bsorry\b", code):
                if decl in ALLOWED_SORRY:
                    found[decl] = found.get(decl, 0) + 1
                else:
                    bad.append(f"{path}:{i}: sorry outside the allowlist (in {decl}): {line.strip()}")
    for name in sorted(ALLOWED_SORRY):
        n = found.get(name, 0)
        if n != 1:
            bad.append(f"allowlisted conjecture {name}: expected exactly 1 sorry, found {n} "
                       "(if proved, remove it from ALLOWED_SORRY and from KNOWN_SORRY in ../check_axioms.py)")
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    print("security package: no admit, native_decide, sorryAx or axiom declarations; "
          f"sorry only in {sorted(ALLOWED_SORRY)} (exactly once each)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
