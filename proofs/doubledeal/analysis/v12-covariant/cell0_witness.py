"""Pre-check (and reproduction) for the Lean theorem that no card transposition is
COVARIANT for the unkeyed v12 round body F = GridCycle o stem (any output
relabelling tau allowed), i.e. roundBody_covariant_iff_id for transpositions.

EXHAUSTIVE over the 51 representatives (0 e), e = 1..51 (v10Sym conjugation
reduces all 1326 transpositions to them; see NOTES.md). Not a proof by itself:
the Lean heavy library re-checks the same statements by kernel decide!.

Argument. GridCycle puts walk card 0 at output seat 26, so F(m)[26] = stem(m)[0].
If F(s.m) = tau.F(m) on every deck, then g(s.m) = tau(g(m)) with g(m) = stem(m)[0].
Two decks m1 = identity deck and m2 = identity with positions i, j exchanged, with
g(m1) = g(m2) but g(s.m1) != g(s.m2), rule out every tau at once.

Prints the table (e -> (i, j)) used by Lean (`covW`) and the set of position
pairs used (`goodPairs`); asserts every entry works.

Usage: python3 cell0_witness.py
"""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

V = 12


def g(m):
    return P.stem(m, V)[0]


def pos_swap(i, j):
    d = list(range(52))
    d[i], d[j] = d[j], d[i]
    return d


def main():
    idd = list(range(52))
    c = g(idd)
    cands = [(i, j) for i, j in itertools.combinations(range(52), 2) if g(pos_swap(i, j)) == c]
    print(f'g(identity deck) = {c}; single position swaps (i, j) keeping g: {len(cands)} of 1326')
    table = [(1, 2)]  # entry 0 unused (e = 0 is not a transposition)
    for e in range(1, 52):
        s = list(range(52))
        s[0], s[e] = e, 0
        v1 = g([s[x] for x in idd])
        for i, j in cands:
            if g([s[x] for x in pos_swap(i, j)]) != v1:
                table.append((i, j))
                break
        else:
            raise SystemExit(f'no witness for e = {e}')
    used = sorted(set(table))
    for i, j in used:
        assert g(pos_swap(i, j)) == c
    print(f'witness found for all 51 representatives; position pairs used: {used}')
    print('covW =', table)


if __name__ == '__main__':
    main()
