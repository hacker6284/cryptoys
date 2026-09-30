#!/usr/bin/env python3
"""Manual check (not run in CI): exact rational values of the two numeric tables behind
`sumRanksV10_survival_le` (DoubleDealSecurity/SumRanksDP/Standalone.lean).

* Table A, `EA_le`: E_A(n) <= 1/100 for 13 <= n <= 49 (PROOF.md §3 (A2)).
* Table B, `EB_le`: E_B(m) <= 1/64 for 2 <= m <= 39 (PROOF.md §4 Theorem B, with the Lean
  refinement f(2, 0) = 1/4).

The definitions mirror the Lean ones (`hA`, `EA`, `fB`, `EB`). Lean proves both tables itself
by kernel `decide!`; this script is an independent re-computation with Python `Fraction`s.
PROOF.md is sumranks-dp-paper/PROOF.md.

Run from anywhere:  python3 checks/sumranks_dp_tables.py   (a few seconds; exits 1 on failure)
Expected: max E_A on 13..49 is 0.008416 at n = 49; E_B(2) = 1/68, E_B(3) = 1/425.
"""
import sys
from fractions import Fraction
from math import comb


def row_weight(z):
    """hA: pointwise bound for a row holding z cards of the majority class."""
    return Fraction(1) if z == 13 else Fraction(1, z + 1)


def expect_rows(n):
    """EA(n): sum over row counts (z0..z3), each 0..13 and summing to n, of
    prod_r C(13, z_r) * hA(z_r), divided by C(52, n)."""
    total = Fraction(0)
    for z0 in range(14):
        for z1 in range(14):
            for z2 in range(14):
                z3 = n - z0 - z1 - z2
                if 0 <= z3 <= 13:
                    term = Fraction(1)
                    for z in (z0, z1, z2, z3):
                        term *= comb(13, z) * row_weight(z)
                    total += term
    return total / comb(52, n)


def col_weight(prev, cur):
    """fB(prev, cur): pointwise bound for the column after one with `prev` off cards."""
    if prev == 0:
        return Fraction(0) if cur == 1 else Fraction(1)
    if prev == 1:
        return Fraction(1, 4)
    if prev == 2:
        return Fraction(1, 4) if cur == 0 else Fraction(1, 3)
    if prev == 3:
        return Fraction(1, 2)
    return Fraction(1)


def expect_cols(m):
    """EB(m): sum over cyclic column counts (y0..y12), each 0..4 and summing to m, of
    prod_j C(4, y_j) * fB(y_{j-1}, y_j), divided by C(52, m); by a transfer matrix."""
    total = Fraction(0)
    for first in range(5):
        # (cards placed so far, count in the previous column) -> weight
        states = {(first, first): Fraction(comb(4, first))}
        for _ in range(1, 13):
            nxt = {}
            for (placed, prev), weight in states.items():
                for cur in range(5):
                    if placed + cur > m:
                        continue
                    key = (placed + cur, cur)
                    nxt[key] = nxt.get(key, Fraction(0)) + weight * comb(4, cur) * col_weight(prev, cur)
            states = nxt
        for (placed, prev), weight in states.items():
            if placed == m:
                total += weight * col_weight(prev, first)
    return total / comb(52, m)


def main():
    table_a = {n: expect_rows(n) for n in range(13, 50)}
    n_max = max(table_a, key=table_a.get)
    ok_a = all(v <= Fraction(1, 100) for v in table_a.values())
    print(f"Table A: max E_A(n) over 13..49 = {float(table_a[n_max]):.6f} at n = {n_max}; "
          f"all <= 1/100: {ok_a}")

    table_b = {m: expect_cols(m) for m in range(2, 40)}
    m_max = max(table_b, key=table_b.get)
    ok_b = all(v <= Fraction(1, 64) for v in table_b.values())
    print(f"Table B: E_B(2) = {table_b[2]}, E_B(3) = {table_b[3]}; max over 2..39 = "
          f"{table_b[m_max]} at m = {m_max}; all <= 1/64: {ok_b}")
    return 0 if ok_a and ok_b else 1


if __name__ == "__main__":
    sys.exit(main())
