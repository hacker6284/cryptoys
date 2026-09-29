"""Pre-check (and reproduction) for the Lean theorem that no card transposition
commutes with the unkeyed v12 round body F = GridCycle o stem on every deck.

EXHAUSTIVE over the 51 representatives e = 1..51 (card 0 = A-clubs paired with
card e); every transposition is v10Sym-conjugate to one of them (v10Sym acts
simply transitively on the 52 cards). Not a proof by itself: the Lean heavy
library re-checks the same 51 statements by kernel decide!.

For each e: x_e = (all cards except 0, e in increasing order) ++ [0, e] (so the
swapped pair sits at walk positions 50, 51, where swapping them never changes
the GridCycle seat walk), m_e = stem^{-1}(x_e). The check is
    stem((0 e) . m_e) != (0 e) . x_e
i.e. SumRanks does not commute with (0 e) at m_e. If F commuted with (0 e) on
every deck, GridCycle survival at x_e would force equality.

Usage: python3 swap_tail_witness.py
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

V = 12


def inv_shift_rows(g):
    return [row[-r:] + row[:-r] if r else row[:] for r, row in enumerate(g)]


def inv_stem(x):
    return P.scoop_cm(P.inv_sum_ranks_v10(inv_shift_rows(P.lay_cm(x))))


def xe(e):
    return [c for c in range(52) if c not in (0, e)] + [0, e]


def main():
    # self-checks of the inverse and of the tail property
    import random
    rng = random.Random(1)
    for _ in range(200):
        d = list(range(52))
        rng.shuffle(d)
        assert P.stem(inv_stem(d), V) == d and inv_stem(P.stem(d, V)) == d
        s = list(range(52))
        s[d[50]], s[d[51]] = d[51], d[50]
        assert P.walk_v11([s[c] for c in d]) == P.walk_v11(d)
    print('selfcheck: inv_stem is the inverse of stem; swapping walk cards 50/51 keeps the walk: ok (200 decks)')
    bad = []
    for e in range(1, 52):
        x = xe(e)
        m = inv_stem(x)
        s = list(range(52))
        s[0], s[e] = e, 0
        lhs = P.stem([s[c] for c in m], V)
        rhs = [s[c] for c in x]
        if lhs == rhs:
            bad.append(e)
    print(f'representatives e = 1..51: stem((0 e).m_e) != (0 e).x_e for {51 - len(bad)} of 51; failing: {bad}')


if __name__ == '__main__':
    main()
