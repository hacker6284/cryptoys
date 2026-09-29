#!/usr/bin/env python3
"""Import-closure gate for SumRanks.lean (cheap: about 2 s when up to date (rebuilds
SumRanks/PermWitness if stale); no heavy build).

The point of the PermWitness split (#116) is the import cost of SumRanks.lean. This gate
checks that cost directly, on the real transitive closure, computed by Lean rather than
by parsing source:

  a. `lake build` of every module the scratch file imports (SumRanks and PermWitness;
     the selftest adds Mathlib.Tactic.Ring), so the .olean files match the sources.
     A stale .olean would otherwise make the check pass on the old imports. A failed
     build fails the gate.
  b. A scratch file that imports those modules is run with `lake env lean` from the
     security package. It prints the environment header: the number of entries of
     `env.header.moduleNames` and of `env.header.moduleData`, then every module in the
     import closure with the direct imports recorded in its .olean (same index). Unequal
     lengths, a module line count that differs from them, or an imported module with no
     entry of its own fail the gate. (`lean --deps` only lists direct imports, so it is
     not used.)

From that graph:
  1. the closure of DoubleDealSecurity.SumRanks has EXACTLY SUMRANKS_CLOSURE_MODULES
     modules, and EXACTLY SUMRANKS_MATHLIB_MODULES of them are named `Mathlib` or
     `Mathlib.*` (equality, so a change in either direction is noticed and the
     constants re-measured);
  2. the closure of DoubleDealSecurity.PermWitness is the closure of
     Mathlib.GroupTheory.Perm.Basic plus PermWitness itself: it adds nothing else
     (of any package, not only Mathlib).

What this assumes: the counts are for the current Mathlib pin (lake-manifest.json) and
Lean toolchain (lean-toolchain); they are not a property of the sources alone. It does
not assume anything about where the modules come from: Lean's own modules, the core
DoubleDeal package, its emitted Generated/ package, Batteries and every Mathlib module are
counted as Lean resolved them.

usage: check_closure.py            # the gate (CI job doubledeal-security)
       check_closure.py --print    # print the measured numbers, no check
       check_closure.py --selftest # synthetic graphs + one Lean case (Mathlib.Tactic.Ring)
"""
import subprocess
import sys
import tempfile
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent

# The import closure of DoubleDealSecurity.SumRanks, measured with Lean v4.14.0 and the
# Mathlib pin in lake-manifest.json. UPDATE BOTH WHEN MATHLIB OR THE TOOLCHAIN IS BUMPED
# (the total also counts Lean's own Init/Std/Lean modules and Batteries): run
# `check_closure.py --print` and check that the new numbers are still just the closure of
# Relabel's three Mathlib imports, Mathlib.GroupTheory.Perm.Basic and the core DoubleDeal
# package, not a new heavy import.
SUMRANKS_CLOSURE_MODULES = 1579   # every module, SumRanks itself included
SUMRANKS_MATHLIB_MODULES = 338    # of which named Mathlib / Mathlib.*
PINS = (SUMRANKS_CLOSURE_MODULES, SUMRANKS_MATHLIB_MODULES)   # (total, Mathlib), as counts()

SUMRANKS = "DoubleDealSecurity.SumRanks"
PERMWITNESS = "DoubleDealSecurity.PermWitness"
PERM_BASIC = "Mathlib.GroupTheory.Perm.Basic"

QUERY = """open Lean in
#eval show CoreM Unit from do
  let h := (← getEnv).header
  IO.println s!"SIZES {h.moduleNames.size} {h.moduleData.size}"
  for i in [0:h.moduleNames.size] do
    let imps := h.moduleData[i]?.map (·.imports.toList.map (·.module.toString))
    IO.println s!"MODULE {h.moduleNames[i]!} {" ".intercalate (imps.getD ["<no-moduleData>"])}"
"""


def fail(msg):
    raise SystemExit(f"check_closure: {msg}")


def lean_graph(imports):
    """{module: [direct imports]} for the import closure of `imports`, from Lean, after
    rebuilding `imports` (step a of the docstring)."""
    b = subprocess.run(["lake", "build", *imports], cwd=PKG, capture_output=True, text=True)
    if b.returncode != 0:
        fail(f"`lake build {' '.join(imports)}` failed in {PKG}:\n{b.stdout}{b.stderr}")
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "Closure.lean"
        f.write_text("".join(f"import {m}\n" for m in imports) + QUERY)
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=PKG, capture_output=True, text=True)
    if r.returncode != 0:
        fail(f"`lake env lean` on the scratch file failed:\n{r.stdout}{r.stderr}")
    return parse_graph(r.stdout)


def parse_graph(out):
    """The graph from the scratch file's output; fails on any inconsistency."""
    sizes = [l.split()[1:] for l in out.splitlines() if l.startswith("SIZES ")]
    mods = [l.split()[1:] for l in out.splitlines() if l.startswith("MODULE ")]
    if len(sizes) != 1:
        fail(f"expected exactly one SIZES line (got {len(sizes)}) in the Lean output:\n{out}")
    if len(sizes[0]) != 2 or not all(x.isdigit() for x in sizes[0]):
        fail(f"malformed SIZES line (expected two counts): SIZES {' '.join(sizes[0])}")
    names, data = map(int, sizes[0])
    if not (names == data == len(mods)):
        fail(f"moduleNames has {names} entries, moduleData {data}, {len(mods)} module lines")
    graph = {}
    for name, *deps in mods:
        if "<no-moduleData>" in deps:
            fail(f"no moduleData entry for {name} (moduleData shorter than moduleNames)")
        if name in graph:
            fail(f"duplicate header entry for {name}")
        graph[name] = deps
    return graph


def closure(graph, roots):
    seen, todo = set(), [(m, "<root>") for m in roots]
    while todo:
        m, by = todo.pop()
        if m in seen:
            continue
        if m not in graph:
            fail(f"{m} (imported by {by}) has no entry in the environment header")
        seen.add(m)
        todo += [(d, m) for d in graph[m]]
    return seen


def is_mathlib(m):
    return m == "Mathlib" or m.startswith("Mathlib.")


def counts(graph, roots):
    """(total, Mathlib) module counts of the import closure of `roots`."""
    c = closure(graph, roots)
    return len(c), sum(map(is_mathlib, c))


def check(graph, sumranks_roots=(SUMRANKS,), pins=PINS):
    """(failures, (total, mathlib)) for checks 1 and 2 on `graph`; `sumranks_roots` is
    what counts as SumRanks (the selftest adds a heavy import next to it)."""
    got = counts(graph, sumranks_roots)
    bad = []
    for what, n, pin, const in (
            ("modules", got[0], pins[0], "SUMRANKS_CLOSURE_MODULES"),
            ("Mathlib modules", got[1], pins[1], "SUMRANKS_MATHLIB_MODULES")):
        if n != pin:
            bad.append(f"{' + '.join(sumranks_roots)}: {n} {what} in the import closure, pinned "
                       f"{const} = {pin} (a new import, or a Mathlib/toolchain bump: see the "
                       "comment at the constants)")
    extra = closure(graph, [PERMWITNESS]) - closure(graph, [PERM_BASIC]) - {PERMWITNESS}
    if extra:
        bad.append(f"{PERMWITNESS} adds {len(extra)} module(s) beyond the closure of {PERM_BASIC}: "
                   f"{', '.join(sorted(extra)[:10])}{' ...' if len(extra) > 10 else ''}")
    return bad, got


def summary(graph):
    total, ml = counts(graph, [SUMRANKS])
    return (f"{SUMRANKS}: {total} modules in the import closure "
            f"(pinned {SUMRANKS_CLOSURE_MODULES}), {ml} Mathlib "
            f"(pinned {SUMRANKS_MATHLIB_MODULES}); {PERMWITNESS}: "
            f"{len(closure(graph, [PERMWITNESS]))} = {PERM_BASIC} "
            f"({len(closure(graph, [PERM_BASIC]))}) + itself")


# Synthetic graphs: (name, graph, (total pin, Mathlib pin), expect_pass, substring expected
# in the failure output). G_OK: SumRanks' closure has 6 modules, 2 of them Mathlib.
G_OK = {SUMRANKS: ["R", PERMWITNESS], "R": ["Mathlib.A", "Core"], "Core": [],
        PERMWITNESS: [PERM_BASIC], PERM_BASIC: ["Mathlib.A"], "Mathlib.A": []}
SELFTEST = [
    ("exact pins", G_OK, (6, 2), True, None),
    ("one Mathlib module too many",
     {**G_OK, "R": ["Mathlib.A", "Core", "Mathlib.B"], "Mathlib.B": []}, (6, 2), False,
     "3 Mathlib modules in the import closure, pinned SUMRANKS_MATHLIB_MODULES = 2"),
    ("bare Mathlib counts", {**G_OK, "R": ["Mathlib.A", "Core", "Mathlib"], "Mathlib": []},
     (7, 2), False, "3 Mathlib modules"),
    ("fewer than pinned also fails", G_OK, (6, 3), False, "2 Mathlib modules"),
    ("heavy via the core package", {**G_OK, "Core": ["Mathlib.B"], "Mathlib.B": []},
     (7, 2), False, "3 Mathlib modules"),
    ("one non-Mathlib module too many", {**G_OK, "Core": ["Batteries.X"], "Batteries.X": []},
     (6, 2), False, "7 modules in the import closure, pinned SUMRANKS_CLOSURE_MODULES = 6"),
    ("PermWitness adds a non-Mathlib module", {**G_OK, PERMWITNESS: [PERM_BASIC, "Core"]},
     (6, 2), False, f"{PERMWITNESS} adds 1 module(s) beyond the closure of {PERM_BASIC}: Core"),
    ("SumRanks missing", {k: v for k, v in G_OK.items() if k != SUMRANKS}, (6, 2), False,
     f"{SUMRANKS} (imported by <root>) has no entry"),
    ("imported module without an entry", {k: v for k, v in G_OK.items() if k != "Core"},
     (6, 2), False, "Core (imported by R) has no entry"),
]
# Lean output: (name, text, substring expected in the failure; "passed" = must parse)
PARSE_SELFTEST = [
    ("well-formed", "SIZES 2 2\nMODULE A\nMODULE B A\n", "passed"),
    ("length mismatch", "SIZES 2 1\nMODULE A\nMODULE B A\n",
     "moduleNames has 2 entries, moduleData 1"),
    ("missing module line", "SIZES 2 2\nMODULE A\n", "2 entries, moduleData 2, 1 module lines"),
    ("missing moduleData", "SIZES 1 1\nMODULE A <no-moduleData>\n",
     "no moduleData entry for A (moduleData shorter than moduleNames)"),
    ("duplicate entry", "SIZES 2 2\nMODULE A\nMODULE A\n", "duplicate header entry for A"),
    ("no SIZES line", "MODULE A\n", "expected exactly one SIZES line (got 0)"),
    ("two SIZES lines", "SIZES 1 1\nSIZES 1 1\nMODULE A\n",
     "expected exactly one SIZES line (got 2)"),
    ("malformed SIZES line", "SIZES 1\nMODULE A\n", "malformed SIZES line"),
]


def selftest():
    fails = 0
    for name, graph, pins, ok, want in SELFTEST:
        try:
            bad = check(graph, pins=pins)[0]
        except SystemExit as e:
            bad = [str(e)]
        if not ((not bad) if ok else (bad and any(want in b for b in bad))):
            fails += 1
            print(f"SELFTEST FAIL {name}: {bad}", file=sys.stderr)
    for name, text, want in PARSE_SELFTEST:
        try:
            parse_graph(text)
            got = "passed"
        except SystemExit as e:
            got = str(e)
        if want not in got:
            fails += 1
            print(f"SELFTEST FAIL {name}: {got}", file=sys.stderr)
    # Lean: SumRanks next to Mathlib.Tactic.Ring must exceed the pins.
    roots = (SUMRANKS, "Mathlib.Tactic.Ring")
    bad, (total, ml) = check(lean_graph(roots), sumranks_roots=roots)
    if not (ml > SUMRANKS_MATHLIB_MODULES and total > SUMRANKS_CLOSURE_MODULES and len(bad) >= 2):
        fails += 1
        print(f"SELFTEST FAIL Lean: SumRanks + Mathlib.Tactic.Ring: {total} / {ml}: {bad}",
              file=sys.stderr)
    if fails:
        return 1
    print(f"check_closure selftest: {len(SELFTEST)} synthetic + {len(PARSE_SELFTEST)} parse cases "
          f"+ 1 Lean case (SumRanks + Mathlib.Tactic.Ring: {total} modules, {ml} Mathlib, "
          "rejected) pass")
    return 0


def main(argv):
    if argv == ["--selftest"]:
        return selftest()
    if argv not in ([], ["--print"]):
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    graph = lean_graph([SUMRANKS, PERMWITNESS])
    if argv == ["--print"]:
        print(summary(graph))
        return 0
    bad = check(graph)[0]
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    print(f"check_closure: {summary(graph)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
