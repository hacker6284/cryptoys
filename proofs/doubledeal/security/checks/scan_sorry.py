#!/usr/bin/env python3
"""CI gate for the security package: no admit / native_decide / sorryAx / axiom
declarations anywhere, and
`sorry` only inside the listed known conjectures (by declaration name).

The allowlist must match exactly: a new sorry fails, and so does a listed
conjecture that no longer contains one (then remove it here and from
KNOWN_SORRY in ../check_axioms.py).

A sorry is attributed to its top-level declaration, except inside a `let rec`
or a `where` item: Lean compiles those to their own declarations (`top.f`),
which is also how the axiom gate names them. `have` stays with its parent.
The axiom gate (../check_axioms.py) is the real enforcer; this scan is a
cheap source-level check. `--selftest` runs the built-in cases below.
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


# `let rec f ...` inside a declaration (compiled to its own declaration `top.f`)
LET_REC = re.compile(r"^\s+let\s+rec\s+([A-Za-z_][\w'.]*)\b")
# an item of a `where` block: `  f (x : α) : β := ...`
WHERE_ITEM = re.compile(r"^\s+([A-Za-z_][\w'.]*)\b[^:=|]*(?::[^=]|:=)")


def strip_block_comments(text: str) -> str:
    # keep line numbers: replace comment bodies but keep newlines
    return re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)


def scan(sources):
    """sources: iterable of (label, text). Returns (bad, found)."""
    bad = []
    found = {}
    for path, raw in sources:
        decl = None      # current top-level declaration
        top = None
        in_where = False
        let_rec_indent = None
        text = strip_block_comments(raw)
        for i, line in enumerate(text.splitlines(), 1):
            code = re.sub(r"--.*", "", line)
            m = DECL.match(code)
            if m:
                top = decl = (m.group(1) or "<anonymous>").split(".")[-1]
                in_where = False
                let_rec_indent = None
            elif top is not None:
                # a `let rec` / `where` item gets its own name (`top.f`), so a sorry
                # there is neither attributed to nor counted for the parent
                indent = len(code) - len(code.lstrip())
                if let_rec_indent is not None and code.strip() and indent <= let_rec_indent:
                    decl, let_rec_indent = top, None   # left the `let rec` body
                h = LET_REC.match(code)
                if h:
                    decl, let_rec_indent = f"{top}.{h.group(1)}", indent
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
    return bad, found


def check(sources):
    bad, found = scan(sources)
    for name in sorted(ALLOWED_SORRY):
        n = found.get(name, 0)
        if n != 1:
            bad.append(f"allowlisted conjecture {name}: expected exactly 1 sorry, found {n} "
                       "(if proved, remove it from ALLOWED_SORRY and from KNOWN_SORRY in ../check_axioms.py)")
    return bad


def main() -> int:
    files = [p for p in sorted(PKG.rglob("*.lean")) if ".lake" not in p.parts]
    bad = check((str(p), p.read_text()) for p in files)
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    print("security package: no admit, native_decide, sorryAx or axiom declarations; "
          f"sorry only in {sorted(ALLOWED_SORRY)} (exactly once each)")
    return 0


C = "roundBody_covariant_iff_id"
SELFTEST = [
    # (name, source, expect_pass, substring expected in the failure output)
    ("clean conjecture", f"theorem {C} : P := by\n  sorry\n", True, None),
    ("comments ignored", f"theorem {C} : P := by\n  sorry -- sorry admit\n/- sorry native_decide -/\n", True, None),
    ("sorry elsewhere", f"theorem {C} : P := by\n  sorry\ntheorem other : Q := by\n  sorry\n", False, "(in other)"),
    ("private decl", f"theorem {C} : P := by\n  sorry\nprivate theorem priv : Q := sorry\n", False, "(in priv)"),
    ("two sorries", f"theorem {C} : P := by\n  sorry\n  sorry\n", False, "found 2"),
    ("conjecture proved", f"theorem {C} : P := by\n  trivial\n", False, "found 0"),
    ("have stays with parent", f"theorem {C} : P := by\n  have h : Q := by\n    sorry\n  exact h\n", True, None),
    ("have adds to parent", f"theorem {C} : P := by\n  have h : Q := by\n    sorry\n  sorry\n", False, "found 2"),
    ("let rec is its own decl", f"theorem {C} : P := by\n  let rec aux : Q := by\n    sorry\n  sorry\n", False, f"(in {C}.aux)"),
    ("let rec body ends", f"theorem {C} : P := by\n  let rec aux : Nat := 0\n  sorry\n", True, None),
    ("inline where item", f"theorem {C} : P := by\n  sorry\ndef wh : Nat := go where go : Nat := sorry\n", False, "(in wh.go)"),
    ("where item", f"theorem {C} : P := by\n  sorry\ndef wh : Nat := go\nwhere\n  go : Nat := sorry\n", False, "(in wh.go)"),
    ("admit", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := by admit\n", False, "admit/native_decide/sorryAx"),
    ("native_decide", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := by native_decide\n", False, "admit/native_decide/sorryAx"),
    ("sorryAx", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := sorryAx Q\n", False, "admit/native_decide/sorryAx"),
    ("axiom declaration", f"theorem {C} : P := by\n  sorry\naxiom ax : False\n", False, "axiom declaration"),
]


def selftest() -> int:
    fails = 0
    for name, src, ok, want in SELFTEST:
        bad = check([("<selftest>", src)])
        good = (not bad) if ok else (bool(bad) and any(want in b for b in bad))
        if not good:
            fails += 1
            print(f"SELFTEST FAIL {name}: {bad}", file=sys.stderr)
    if fails:
        return 1
    print(f"scan_sorry selftest: {len(SELFTEST)} cases pass")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if args not in ([], ["--selftest"]):
        sys.exit("usage: scan_sorry.py [--selftest]")
    sys.exit(selftest() if args else main())
