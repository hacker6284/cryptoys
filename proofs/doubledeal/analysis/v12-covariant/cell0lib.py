"""Shared witness search for the seat-26 (stem cell 0) refutations of the covariant
round conjecture, used by `cell0_witness.py` (transpositions) and
`../v12-primenonswap/aff_witness.py` (affine relabellings).

Not a proof: every table entry is re-checked by kernel `decide!` in the heavy Lean
library, so a wrong entry fails the heavy build.

Witness for a relabelling s: m1 = identity deck, m2 = identity deck with seats i, j
exchanged, with g(m1) = g(m2) (g = stem cell 0) but g(s.m1) != g(s.m2). The pair
(i, j) is the FIRST of the identity-deck candidates (lexicographic) that works.

The Lean list `cell0Pairs` (CovariantNarrowLists.lean, written by cell0_witness.py) is
`PAIRS`: the union of the pairs used by both tables, so ONE check A covers both.
"""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SEC = HERE.parents[1] / 'security'
sys.path.insert(0, str(SEC / 'checks'))
import ddport as P  # noqa: E402

V = 12

# GL(2,2) as bit matrices [[m00, m01], [m10, m11]] on the label bits (l % 2, l // 2):
# new bit 0 = m00 b0 + m01 b1, new bit 1 = m10 b0 + m11 b1 (mod 2). Index g = position.
GL_MATS = [((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 1), (0, 1)),
           ((1, 0), (1, 1)), ((0, 1), (1, 1)), ((1, 1), (1, 0))]


def gl_apply(mat, l):
    b0, b1 = l & 1, l >> 1
    return ((mat[0][0] * b0 + mat[0][1] * b1) & 1) | (((mat[1][0] * b0 + mat[1][1] * b1) & 1) << 1)


GL_TAB = [[gl_apply(m, l) for l in range(4)] for m in GL_MATS]  # emitted as Lean `glTab`
GL_INV = [next(h for h in range(6) if all(GL_TAB[h][GL_TAB[g][l]] == l for l in range(4)))
          for g in range(6)]                                    # emitted as Lean `glInvTab`
UNIT_INV = [pow(k + 1, -1, 13) - 1 for k in range(12)]           # emitted as Lean `unitInvTab`


def lin(k, g):
    """Lean `linSym k g` as an image list: rank index * (k + 1) mod 13, label -> GL_TAB[g]."""
    return [13 * P.SUIT_OF_LABEL[GL_TAB[g][P.LABEL[c // 13]]] + ((k + 1) * (c % 13)) % 13
            for c in range(52)]


def swap0(e):
    s = list(range(52))
    s[0], s[e] = e, 0
    return s


def sanity():
    assert len({tuple(r) for r in GL_TAB}) == 6 and GL_TAB[0] == [0, 1, 2, 3]
    for row in GL_TAB:
        assert row[0] == 0 and row[3] == row[1] ^ row[2] and sorted(row) == [0, 1, 2, 3]
    ident = list(range(52))
    for k in range(12):
        for g in range(6):
            s = lin(k, g)
            assert sorted(s) == ident and (s == ident) == ((k, g) == (0, 0))


def g(m):
    return P.stem(m, V)[0]


def pos_swap(i, j):
    d = list(range(52))
    d[i], d[j] = d[j], d[i]
    return d


def candidates():
    """(g(identity deck), the position swaps of the identity deck that keep g)."""
    c = g(list(range(52)))
    return c, [(i, j) for i, j in itertools.combinations(range(52), 2) if g(pos_swap(i, j)) == c]


def witness(s, cands):
    v1 = g(s)  # s applied to the identity deck is s itself
    for i, j in cands:
        if g([s[x] for x in pos_swap(i, j)]) != v1:
            return (i, j)
    return None


def tables():
    """(c, number of candidates, covW[1..51], affW[1..71], PAIRS): covW[e - 1] for the
    transposition (0 e); affW[n - 1] for linSym k g with n = 6 k + g. Entry 0 of the Lean
    lists (unused) is added by the emitters as PAIRS[0]."""
    sanity()
    c, cands = candidates()
    cov = [witness(swap0(e), cands) for e in range(1, 52)]
    aff = [witness(lin(*divmod(n, 6)), cands) for n in range(1, 72)]
    if None in cov or None in aff:
        raise SystemExit('missing witness')
    pairs = sorted(set(cov) | set(aff))
    for i, j in pairs:
        assert g(pos_swap(i, j)) == c
    return c, len(cands), cov, aff, pairs


def fmt(ps):
    rows = [', '.join(f'({i}, {j})' for i, j in ps[k:k + 8]) for k in range(0, len(ps), 8)]
    return '[' + ',\n    '.join(rows) + ']'
