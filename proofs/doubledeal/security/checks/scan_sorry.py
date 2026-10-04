#!/usr/bin/env python3
"""CI gate for the security package: no admit / admitGoal / native_decide / sorryAx / initialize /
`[init]` / `[builtin_init]` attributes / axiom declarations anywhere, and
`sorry` only inside the listed known conjectures (by declaration name). For this
package the list (ALLOWED_SORRY) is EMPTY: no `sorry` at all. (The last one,
`roundBody_covariant_iff_id`, was removed: that statement is proved in the heavy library,
and the default library has the `_of_covariant` reductions.)

An allowlist must match exactly: a new sorry fails, and so does a listed
conjecture that no longer contains one (then remove it from the list, and here
also from KNOWN_SORRY in ../check_axioms.py).

A sorry is attributed to its top-level declaration, except inside a `let rec`
or a `where` item: Lean compiles those to their own declarations (`top.f`),
which is also how the axiom gate names them. `have` stays with its parent.
The axiom gate (../check_axioms.py) is the real enforcer; this scan is a
cheap source-level check. `--selftest` runs the built-in cases below.

Other Lean packages use the same gate (one line per CI job):
  scan_sorry.py                                    # this package, ALLOWED_SORRY (empty)
  scan_sorry.py --root DIR_OR_FILE ... [--exclude PART ...] [--allow-sorry NAME ...]
With --root, the sorry allowlist is exactly the --allow-sorry names (default: none).
--allow-sorry without --root is rejected (exit 2): the default scan's allowlist is
ALLOWED_SORRY only.
--exclude skips files with that path component (e.g. Generated); .lake is always skipped.
This is a source-level scan and parses no imports; the import-closure bound for
SumRanks.lean is checks/check_closure.py (run after `lake build`).
"""
import argparse
import re
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
# Known DRAFT-SORRY theorems of this package; each must contain exactly one sorry.
# Empty: the package has no sorry. Keep in sync with KNOWN_SORRY in ../check_axioms.py.
ALLOWED_SORRY: set[str] = set()

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


# `@[init f]` / `@[builtin_init]` / `attribute [init] x` (also inside a list such as
# `@[simp, init]`, with `local` / `scoped` / `-`): code run when the module is imported,
# e.g. inside `lean` while a later module is compiled. Same hazard as `initialize`.
ATTR_BLOCK = re.compile(r"(?:@\[|\battribute\s*\[)([^\]]*)\]")
INIT_ATTRS = {"init", "builtin_init", "«init»", "«builtin_init»"}


def init_attrs(code: str):
    """(offset, name) of init attributes in the `@[...]` / `attribute [...]` blocks of
    `code` (comments already removed; a block may span lines)."""
    for m in ATTR_BLOCK.finditer(code):
        for item in m.group(1).split(","):
            words = item.strip().lstrip("-").split()
            while words and words[0] in ("local", "scoped"):
                words = words[1:]
            if words and words[0].lstrip("-") in INIT_ATTRS:
                yield m.start(), words[0].lstrip("-")


def scan(sources, allowed):
    """sources: iterable of (label, text); allowed: declarations that may hold one sorry.
    Returns (bad, found)."""
    bad = []
    found = {}
    for path, raw in sources:
        decl = None      # current top-level declaration
        top = None
        in_where = False
        let_rec_indent = None
        text = strip_block_comments(raw)
        code_all = "\n".join(re.sub(r"--.*", "", l) for l in text.splitlines())
        lines = raw.splitlines()
        for off, name in init_attrs(code_all):
            i = code_all.count("\n", 0, off) + 1
            bad.append(f"{path}:{i}: forbidden [{name}] attribute: {lines[i - 1].strip() if i <= len(lines) else ''}")
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
            for f in re.finditer(r"\b(admit|admitGoal|native_decide|sorryAx|initialize|builtin_initialize)\b", code):
                bad.append(f"{path}:{i}: forbidden {f.group(1)}: {line.strip()}")
            if re.match(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*axiom\b", code):
                bad.append(f"{path}:{i}: axiom declaration: {line.strip()}")
            for _ in re.finditer(r"\bsorry\b", code):
                if decl in allowed:
                    found[decl] = found.get(decl, 0) + 1
                else:
                    bad.append(f"{path}:{i}: sorry outside the allowlist (in {decl}): {line.strip()}")
    return bad, found


def check(sources, allowed):
    bad, found = scan(sources, allowed)
    for name in sorted(allowed):
        n = found.get(name, 0)
        if n != 1:
            bad.append(f"allowlisted conjecture {name}: expected exactly 1 sorry, found {n} "
                       "(if proved, remove it from ALLOWED_SORRY and from KNOWN_SORRY in ../check_axioms.py)")
    return bad


def lean_files(roots, exclude=()):
    skip = {".lake", *exclude}
    files = []
    for root in roots:
        root = Path(root)
        if root.is_file():
            files.append(root)
        elif root.is_dir():
            files += [p for p in sorted(root.rglob("*.lean")) if not skip & set(p.relative_to(root).parts)]
        else:
            raise SystemExit(f"scan_sorry: no such file or directory: {root}")
    return files


def main(roots, exclude, allowed, label) -> int:
    files = lean_files(roots, exclude)
    if not files:
        print(f"scan_sorry: no .lean files under {label}", file=sys.stderr)
        return 1
    bad = check(((str(p), p.read_text()) for p in files), allowed)
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    what = f"sorry only in {sorted(allowed)} (exactly once each)" if allowed else "no sorry"
    print(f"{label} ({len(files)} files): no admit, admitGoal, native_decide, sorryAx, initialize, [init] or "
          f"axiom declarations; {what}")
    return 0


# The allowlist mechanics (still used via --allow-sorry) are tested with a scratch
# allowlist {C}; DEFAULT_SELFTEST below runs against the package default ALLOWED_SORRY.
C = "someConjecture"
SELFTEST_ALLOWED = {C}
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
    ("admit", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := by admit\n", False, "forbidden admit:"),
    ("native_decide", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := by native_decide\n", False, "forbidden native_decide:"),
    ("admitGoal", f"theorem {C} : P := by\n  sorry\nelab \"trustme\" : tactic => do\n  admitGoal (← getMainGoal)\n", False, "forbidden admitGoal:"),
    ("sorryAx", f"theorem {C} : P := by\n  sorry\ntheorem t : Q := sorryAx Q\n", False, "forbidden sorryAx:"),
    ("initialize", f"theorem {C} : P := by\n  sorry\ninitialize IO.println \"loaded module X\"\n", False, "forbidden initialize:"),
    ("builtin_initialize", f"theorem {C} : P := by\n  sorry\nbuiltin_initialize IO.println \"loaded module X\"\n", False, "forbidden builtin_initialize:"),
    ("axiom declaration", f"theorem {C} : P := by\n  sorry\naxiom ax : False\n", False, "axiom declaration"),
    ("@[init] exit", f"theorem {C} : P := by\n  sorry\n@[init] def evil : IO Unit := IO.Process.exit 0\n", False, "forbidden [init] attribute:"),
    ("@[init f] ref", f"theorem {C} : P := by\n  sorry\n@[init mkR] opaque r : Nat\n", False, "forbidden [init] attribute:"),
    ("@[builtin_init]", f"theorem {C} : P := by\n  sorry\n@[builtin_init] def evil : IO Unit := pure ()\n", False, "forbidden [builtin_init] attribute:"),
    ("init in a list, over two lines", f"theorem {C} : P := by\n  sorry\n@[simp,\n  init] def evil : IO Unit := pure ()\n", False, "forbidden [init] attribute:"),
    ("attribute [init]", f"theorem {C} : P := by\n  sorry\ndef evil : IO Unit := pure ()\nattribute [init] evil\n", False, "forbidden [init] attribute:"),
    ("attribute [local init]", f"theorem {C} : P := by\n  sorry\nattribute [local init] evil\n", False, "forbidden [init] attribute:"),
    ("init-like names are fine", f"theorem {C} : P := by\n  sorry\n@[simp] theorem init_eq : xs.init = ys := rfl\n-- @[init] in a comment\n", True, None),
]

# Against the package default ALLOWED_SORRY (empty): no sorry anywhere, including in the
# former DRAFT-SORRY theorem.
DEFAULT_SELFTEST = [
    ("default: clean", "theorem t : True := trivial\n-- sorry in a comment\n", True, None),
    ("default: former conjecture with sorry", "theorem roundBody_covariant_iff_id : P := by\n  sorry\n",
     False, "(in roundBody_covariant_iff_id)"),
    ("default: any sorry", "theorem t : P := by\n  sorry\n", False, "(in t)"),
    ("default: native_decide", "theorem t : True := by native_decide\n", False, "forbidden native_decide:"),
]


# --root / --exclude / --allow-sorry, run on a scratch tree:
# (name, {relpath: source}, argv, expect_pass, substring expected in the failure output)
FLAG_SELFTEST = [
    ("root: clean", {"A/X.lean": "theorem t : True := trivial\n"}, ["--root", "A"], True, None),
    ("root: no default allowlist", {"A/X.lean": f"theorem {C} : P := by\n  sorry\n"},
     ["--root", "A"], False, f"(in {C})"),
    ("root: --allow-sorry", {"A/X.lean": f"theorem {C} : P := by\n  sorry\n"},
     ["--root", "A", "--allow-sorry", C], True, None),
    ("root: --allow-sorry must be used", {"A/X.lean": "theorem t : True := trivial\n"},
     ["--root", "A", "--allow-sorry", C], False, "found 0"),
    ("root: native_decide", {"A/X.lean": "theorem t : True := by native_decide\n"},
     ["--root", "A", "--allow-sorry", "t"], False, "forbidden native_decide:"),
    ("root: file root", {"A/X.lean": "theorem t : Q := by admit\n"}, ["--root", "A/X.lean"], False,
     "forbidden admit:"),
    ("root: several roots", {"A/X.lean": "", "B/Y.lean": "theorem u : Q := sorry\n"},
     ["--root", "A", "--root", "B"], False, "(in u)"),
    ("exclude: skipped part", {"A/X.lean": "", "A/Generated/G.lean": "theorem g : Q := sorry\n"},
     ["--root", "A", "--exclude", "Generated"], True, None),
    ("exclude: others still scanned", {"A/Generated/G.lean": "", "A/Y.lean": "theorem u : Q := sorry\n"},
     ["--root", "A", "--exclude", "Generated"], False, "(in u)"),
    ("exclude: not excluded by default", {"A/Generated/G.lean": "theorem g : Q := sorry\n"},
     ["--root", "A"], False, "(in g)"),
    (".lake always skipped", {"A/X.lean": "", "A/.lake/p/Z.lean": "theorem z : Q := sorry\n"},
     ["--root", "A"], True, None),
    ("root: missing path", {}, ["--root", "nope"], False, "no such file"),
    ("default: --allow-sorry without --root rejected", {}, ["--allow-sorry", C], False,
     "--allow-sorry needs --root"),
    ("root: no .lean files", {"A/readme.md": "sorry"}, ["--root", "A"], False, "no .lean files"),
]


def parse(argv):
    ap = argparse.ArgumentParser(description="sorry / native_decide gate for Lean packages")
    ap.add_argument("--selftest", action="store_true", help="run the built-in cases and exit")
    ap.add_argument("--root", action="append", help="file or directory to scan (repeatable; "
                    "default: the security package with ALLOWED_SORRY)")
    ap.add_argument("--exclude", action="append", default=[], help="skip paths with this component")
    ap.add_argument("--allow-sorry", action="append", help="declaration allowed exactly one sorry "
                    "(repeatable; only with --root, where the default is none)")
    return ap.parse_args(argv)


def run(a) -> int:
    """a: parsed arguments. The one place that picks the roots and the allowlist default:
    no --root = the security package with ALLOWED_SORRY (and --allow-sorry is rejected);
    with --root, none."""
    if a.root is None and a.allow_sorry is not None:
        print("scan_sorry: --allow-sorry needs --root (the security package's allowlist is "
              "ALLOWED_SORRY, which is empty; it cannot be widened from the command line)",
              file=sys.stderr)
        return 2
    if a.root is None:
        roots, label, default = [PKG], "security package", ALLOWED_SORRY
    else:
        roots, label, default = a.root, ", ".join(a.root), set()
    allowed = default if a.allow_sorry is None else set(a.allow_sorry)
    return main(roots, a.exclude, allowed, label)


def selftest() -> int:
    import contextlib, io, os, tempfile
    fails = 0
    if ALLOWED_SORRY:
        fails += 1
        print(f"SELFTEST FAIL: ALLOWED_SORRY should be empty, is {sorted(ALLOWED_SORRY)}", file=sys.stderr)
    cases = [(n, s, ok, w, SELFTEST_ALLOWED) for n, s, ok, w in SELFTEST]
    cases += [(n, s, ok, w, ALLOWED_SORRY) for n, s, ok, w in DEFAULT_SELFTEST]
    for name, src, ok, want, allowed in cases:
        bad = check([("<selftest>", src)], allowed)
        good = (not bad) if ok else (bool(bad) and any(want in b for b in bad))
        if not good:
            fails += 1
            print(f"SELFTEST FAIL {name}: {bad}", file=sys.stderr)
    for name, tree, argv, ok, want in FLAG_SELFTEST:
        with tempfile.TemporaryDirectory() as d:
            for rel, text in tree.items():
                (Path(d) / rel).parent.mkdir(parents=True, exist_ok=True)
                (Path(d) / rel).write_text(text)
            out, cwd = io.StringIO(), os.getcwd()
            os.chdir(d)
            try:
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                    try:
                        rc = run(parse(argv))
                    except SystemExit as e:
                        print(e)
                        rc = 1
            finally:
                os.chdir(cwd)
        got = out.getvalue()
        good = rc == 0 if ok else (rc != 0 and want in got)
        if not good:
            fails += 1
            print(f"SELFTEST FAIL {name}: rc={rc} {got!r}", file=sys.stderr)
    if fails:
        return 1
    print(f"scan_sorry selftest: {len(SELFTEST)} cases + {len(DEFAULT_SELFTEST)} default-allowlist cases + "
          f"{len(FLAG_SELFTEST)} flag cases pass")
    return 0


if __name__ == "__main__":
    args = parse(sys.argv[1:])
    if args.selftest:
        if args.root or args.exclude or args.allow_sorry:
            sys.exit("scan_sorry.py: --selftest takes no other flags")
        sys.exit(selftest())
    sys.exit(run(args))
