#!/usr/bin/env python3
"""Import-closure gate for SumRanks.lean (cheap, a few seconds; needs `lake build` first).

The point of the PermWitness split (#116) is the import cost of SumRanks.lean. This gate
checks that cost directly, on the real transitive closure, computed by Lean rather than
by parsing source. A scratch file that imports the module(s) is run with `lake env lean`
from the security package. Lean loads the built .olean files, and the scratch file prints
the environment header: every module in the import closure (`env.header.moduleNames`)
together with the direct imports recorded in its .olean (`env.header.moduleData`, same
order). (`lean --deps` only lists direct imports, so it is not used.) From that graph:

  1. the closure of DoubleDealSecurity.SumRanks contains EXACTLY
     SUMRANKS_MATHLIB_MODULES modules named `Mathlib` or `Mathlib.*` (equality, so a
     change in either direction is noticed and the constant re-measured);
  2. the closure of DoubleDealSecurity.PermWitness is the closure of
     Mathlib.GroupTheory.Perm.Basic plus PermWitness itself: it adds nothing else
     (of any package, not only Mathlib).

What this assumes: the counts are for the current Mathlib pin (lake-manifest.json) and
Lean toolchain (lean-toolchain); they are not a property of the sources alone. It does
not assume anything about where the modules come from: the core DoubleDeal package, its
emitted Generated/ package and every Mathlib module are counted as Lean resolved them.
Check 1 counts Mathlib modules only; non-Mathlib dependencies of SumRanks (Lean, Batteries,
the core package) are reported, not bounded.

usage: check_closure.py            # the gate (CI job doubledeal-security, after the build)
       check_closure.py --print    # print the measured numbers, no check
       check_closure.py --selftest # synthetic graphs + one Lean case (Mathlib.Tactic.Ring)
"""
import subprocess
import sys
import tempfile
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent

# Mathlib modules in the import closure of DoubleDealSecurity.SumRanks (1579 modules in
# all, measured with Lean v4.14.0 and the Mathlib pin in lake-manifest.json). UPDATE THIS
# WHEN MATHLIB (or the toolchain) IS BUMPED: run `check_closure.py --print` and check that
# the new number is still just the closure of Relabel's three Mathlib imports and
# Mathlib.GroupTheory.Perm.Basic, not a new heavy import.
SUMRANKS_MATHLIB_MODULES = 338

SUMRANKS = "DoubleDealSecurity.SumRanks"
PERMWITNESS = "DoubleDealSecurity.PermWitness"
PERM_BASIC = "Mathlib.GroupTheory.Perm.Basic"

QUERY = """open Lean in
#eval show CoreM Unit from do
  let h := (← getEnv).header
  for n in h.moduleNames, d in h.moduleData do
    IO.println s!"MODULE {n} {" ".intercalate (d.imports.toList.map (·.module.toString))}"
"""


def lean_graph(imports):
    """{module: [direct imports]} for the import closure of `imports`, from Lean."""
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "Closure.lean"
        f.write_text("".join(f"import {m}\n" for m in imports) + QUERY)
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=PKG, capture_output=True, text=True)
    graph = {}
    for line in r.stdout.splitlines():
        if line.startswith("MODULE "):
            name, *deps = line.split()[1:]
            graph[name] = deps
    if r.returncode != 0 or not graph:
        raise SystemExit(f"check_closure: `lake env lean` failed (run `lake build` in {PKG} "
                         f"first):\n{r.stdout}{r.stderr}")
    return graph


def closure(graph, roots):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo += graph.get(m, [])
    return seen


def is_mathlib(m):
    return m == "Mathlib" or m.startswith("Mathlib.")


def check(graph, sumranks_roots=(SUMRANKS,), pin=SUMRANKS_MATHLIB_MODULES):
    """Failures of checks 1 and 2 on `graph`; `sumranks_roots` is what counts as
    SumRanks (the selftest adds a heavy import next to it)."""
    bad = []
    for m in (*sumranks_roots, PERMWITNESS, PERM_BASIC):
        if m not in graph:
            bad.append(f"{m} is not in the import closure Lean reported")
    if bad:
        return bad
    n = sum(map(is_mathlib, closure(graph, sumranks_roots)))
    if n != pin:
        bad.append(f"{' + '.join(sumranks_roots)}: {n} Mathlib modules in the import closure, "
                   f"pinned SUMRANKS_MATHLIB_MODULES = {pin} (a new import, or a Mathlib bump: "
                   "see the comment at the constant)")
    extra = closure(graph, [PERMWITNESS]) - closure(graph, [PERM_BASIC]) - {PERMWITNESS}
    if extra:
        bad.append(f"{PERMWITNESS} adds {len(extra)} module(s) beyond the closure of {PERM_BASIC}: "
                   f"{', '.join(sorted(extra)[:10])}{' ...' if len(extra) > 10 else ''}")
    return bad


def summary(graph):
    c = closure(graph, [SUMRANKS])
    return (f"{SUMRANKS}: {len(c)} modules in the import closure, {sum(map(is_mathlib, c))} "
            f"Mathlib (pinned {SUMRANKS_MATHLIB_MODULES}); {PERMWITNESS}: "
            f"{len(closure(graph, [PERMWITNESS]))} = {PERM_BASIC} "
            f"({len(closure(graph, [PERM_BASIC]))}) + itself")


# Synthetic graphs: (name, graph, pin, expect_pass, substring expected in the failure output)
G_OK = {SUMRANKS: ["R", PERMWITNESS], "R": ["Mathlib.A", "Core"], "Core": [],
        PERMWITNESS: [PERM_BASIC], PERM_BASIC: ["Mathlib.A"], "Mathlib.A": []}
SELFTEST = [
    ("exact pin", G_OK, 2, True, None),
    ("one Mathlib module too many",
     {**G_OK, "R": ["Mathlib.A", "Core", "Mathlib.B"], "Mathlib.B": []}, 2, False, "3 Mathlib modules in the import closure, pinned SUMRANKS_MATHLIB_MODULES = 2"),
    ("bare Mathlib counts", {**G_OK, "R": ["Mathlib.A", "Core", "Mathlib"], "Mathlib": []},
     2, False, "3 Mathlib modules"),
    ("fewer than pinned also fails", G_OK, 3, False, "2 Mathlib modules"),
    ("heavy via the core package", {**G_OK, "Core": ["Mathlib.B"], "Mathlib.B": []},
     2, False, "3 Mathlib modules"),
    ("PermWitness adds a non-Mathlib module", {**G_OK, PERMWITNESS: [PERM_BASIC, "Core"]},
     2, False, f"{PERMWITNESS} adds 1 module(s) beyond the closure of {PERM_BASIC}: Core"),
    ("SumRanks missing", {k: v for k, v in G_OK.items() if k != SUMRANKS}, 2, False,
     f"{SUMRANKS} is not in the import closure"),
]


def selftest():
    fails = 0
    for name, graph, pin, ok, want in SELFTEST:
        bad = check(graph, pin=pin)
        if not ((not bad) if ok else (bad and any(want in b for b in bad))):
            fails += 1
            print(f"SELFTEST FAIL {name}: {bad}", file=sys.stderr)
    # Lean: SumRanks next to Mathlib.Tactic.Ring must exceed the pin.
    roots = (SUMRANKS, "Mathlib.Tactic.Ring")
    bad = check(lean_graph(roots), sumranks_roots=roots)
    if not any("pinned SUMRANKS_MATHLIB_MODULES" in b for b in bad):
        fails += 1
        print(f"SELFTEST FAIL Lean: SumRanks + Mathlib.Tactic.Ring passed: {bad}", file=sys.stderr)
    if fails:
        return 1
    print(f"check_closure selftest: {len(SELFTEST)} synthetic cases + 1 Lean case "
          f"(SumRanks + Mathlib.Tactic.Ring: {bad[0].split(': ')[1].split(' Mathlib')[0]} "
          "Mathlib modules, rejected) pass")
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
    bad = check(graph)
    if bad:
        print(*bad, sep="\n", file=sys.stderr)
        return 1
    print(f"check_closure: {summary(graph)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
