"""Shared library for the MegaDreifach v2 hash-fix study (stage 3, scratch only).

Imports the in-tree v2 engine READ-ONLY from ../../v2/engine.py.  (The study ran against a byte-identical
export of origin/main; in tree the only change to these study scripts is this import path.)  Extra rules
are built in memory only.

Rules built here (all use the v2 card rule = visual noon, read at once, corner/edge alternating):
  Ct(t)     52 card steps on A, then t F3 rounds on A, then DM:  y = h * E(h).
            Ct(36) is v2 (C36), Ct(76) is the in-tree engine's C76 (same Engine class, t=76).
  SWA(t)    Ct(t) on A, then the SWEEP (read every piece of A in a fixed tour, turn B), then
            'solve B onto A'.  y = B0^-1 X with B0 = U h^-1.
  SWB(t)    52 card steps on A (no F3 on A), SWEEP (read A, turn B), then t F3 rounds on B,
            then 'solve B onto A'.  y = Bf^-1 X with Bf = R(B0) B0, B0 = U h^-1.
SWEEP tour (home grip on A): faces in card order 0..11; on each face start at its (visual)
noon edge and go clockwise: edge {f,n_i}, then the corner after it {f,n_i,n_i+1}; skip any piece
that touches an earlier face.  Each piece read gives (c1 on f, c2 on n_i); on B turn face c1 +1
then face c2 +1 (faces found by centre colour; no re-grip of B).
Composition: compose_st(g, h) = g o h (h applied first); a face turn f acts st <- f o st.
"""
import math
import os
import random
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.join(HERE, '..', '..', 'v2')
sys.path.insert(0, os.path.abspath(V2))
import engine as eng  # noqa: E402

E = eng.engine('C36')          # card-step and F3 tables are the same for every visual-noon rule
ref = eng.ref
STEPS, F3 = E.steps, E.f3
apply, compose_st = eng.apply, eng.compose_st
ID_ST = [3 * s for s in range(20)] + [2 * s for s in range(30)]
IV_ST = list(eng.IV_ST)
uniform_st = eng.uniform_st
GRIPS = eng.GRIPS
FACE_OP = [eng.make_op(eng.face_pos(f, 1)) for f in range(12)]


def inv_st(g):
    """Inverse on encoded states (checked against md.inverse in selftest)."""
    out = [0] * 50
    for s in range(20):
        x = g[s]
        out[x // 3] = 3 * s + (-(x % 3)) % 3
    for s in range(30):
        x = g[20 + s]
        out[20 + x // 2] = 2 * s + (x % 2)
    return out


def cards(st, deal, gi=0, start=0, stop=52):
    for i in range(start, stop):
        op1, rd, op2, _ = STEPS[(i + 1) & 1][gi][deal[i]]
        apply(st, op1)
        s, tab = rd[0]
        ng = tab[st[s]]
        apply(st, op2)
        gi = ng
    return gi


def card_step(st, deal, i, gi):
    op1, rd, op2, _ = STEPS[(i + 1) & 1][gi][deal[i]]
    apply(st, op1)
    s, tab = rd[0]
    ng = tab[st[s]]
    apply(st, op2)
    return ng


def f3_round(st, r, gi):
    """F3 round r (1-based): parity of r selects corner (odd) or edge (even)."""
    op, rd, _, _ = F3[r & 1][gi]
    apply(st, op)
    s, tab = rd[0]
    return tab[st[s]]


def f3(st, t, gi=0):
    for r in range(1, t + 1):
        op, rd, _, _ = F3[r & 1][gi]
        apply(st, op)
        s, tab = rd[0]
        gi = tab[st[s]]
    return gi


def em_ct(h, deal, t):
    st = list(h)
    gi = cards(st, deal)
    f3(st, t, gi)
    return st


def dm_ct(h, deal, t):
    return compose_st(h, em_ct(h, deal, t))


# ---------------------------------------------------------------- sweep
def _tour(gi=0):
    """Tour in grip gi: hold positions in card order 0..11; on each held face start at its
    visual noon edge, go clockwise: edge {f, n_i}, then the corner after it; skip pieces already
    read (= pieces touching an earlier held face).  c1 = colour on the toured face, c2 = colour
    on n_i (physical colours, so B is turned by centre colour, independent of the grip)."""
    o = GRIPS[gi]
    seen = set()
    tour = []
    for p in range(12):
        f = o[p]
        noon = ref.vnoon(p, o)
        nb = list(eng.NBRS[f])
        k = nb.index(noon)
        nb = nb[k:] + nb[:k]
        for i in range(5):
            for par in (0, 1):  # edge {f, nb[i]} then the corner after it
                idx, tab = eng.read_table(f, nb[i], par)
                if idx in seen:
                    continue
                seen.add(idx)
                tour.append((idx, tuple((GRIPS[g][0], GRIPS[g][1]) for g in tab)))
    assert len(tour) == 50 and sorted(seen) == list(range(50)), 'tour does not cover all 50 slots'
    return tour


TOURS = [_tour(g) for g in range(60)]
TOUR = TOURS[0]


def sweep_onto(B, X, gi=0):
    """Read X in the tour of grip gi, turn faces c1 then c2 (+1) on B (mutated)."""
    for idx, tab in TOURS[gi]:
        c1, c2 = tab[X[idx]]
        apply(B, FACE_OP[c1])
        apply(B, FACE_OP[c2])


def dm_swa(h, deal, t):
    """Cards + t F3 on A, then the sweep in A's final grip (no rounds on B)."""
    X = list(h)
    gi = f3(X, t, cards(X, deal))
    B = inv_st(h)
    sweep_onto(B, X, gi)
    return compose_st(inv_st(B), X)


def dm_swb(h, deal, t, home=False):
    """Cards on A; sweep of A in the grip the last card left (home=True: in the home grip,
    which discards that grip); t F3 rounds on B from B's home grip; solve B onto A."""
    X = list(h)
    gi = cards(X, deal)
    B = inv_st(h)
    sweep_onto(B, X, 0 if home else gi)
    f3(B, t, 0)
    return compose_st(inv_st(B), X)


def make_dm(kind, t):
    if kind == 'C':
        return lambda h, d: dm_ct(h, d, t)
    if kind == 'SWA':
        return lambda h, d: dm_swa(h, d, t)
    if kind == 'SWB':
        return lambda h, d: dm_swb(h, d, t)
    if kind == 'SWBh':
        return lambda h, d: dm_swb(h, d, t, home=True)
    raise ValueError(kind)


def cost(kind, t):
    """Hand cost per block (SPEC §5.7 model: card step = 3 face turns, k+2 clicks; F3 round =
    1 turn, 1 click, 1 read, 1 re-grip; sweep = 50 reads, 100 turns / 100 clicks on B, plus
    putting A (and B) into the home grip)."""
    turns, clicks, reads, regrips = 156, 234, 52, 52
    if kind == 'C':
        return dict(turns=turns + t, clicks=clicks + t, reads=reads + t, regrips=regrips + t, solves=3)
    if kind in ('SWA', 'SWB', 'SWBh'):
        return dict(turns=turns + t + 100, clicks=clicks + t + 100, reads=reads + t + 50,
                    regrips=regrips + t + (0 if kind == 'SWA' else 1 if kind == 'SWB' else 2), solves=3)


# ---------------------------------------------------------------- statistics
def fixc(z):
    return sum(z[s] // 3 == s for s in range(20))


def fixe(z):
    return sum(z[20 + s] // 2 == s for s in range(30))


def moved(z):
    return sum(z[s] != 3 * s for s in range(20)) + sum(z[20 + s] != 2 * s for s in range(30))


def cyc(perm):
    n = len(perm)
    seen = [False] * n
    out = []
    for i in range(n):
        if not seen[i]:
            L = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
                L += 1
            out.append(L)
    return tuple(sorted(out, reverse=True))


def cyc_c(z):
    return cyc([z[s] // 3 for s in range(20)])


def cyc_e(z):
    return cyc([z[20 + s] // 2 for s in range(30)])


def fix_law(n):
    """Exact law of the number of fixed points of a uniform element of A_n (n >= 4)."""
    D = [1, 0]
    for m in range(2, n + 1):
        D.append((m - 1) * (D[-1] + D[-2]))
    even = [1] + [(D[m] + (-1) ** (m - 1) * (m - 1)) // 2 for m in range(1, n + 1)]
    tot = math.factorial(n) // 2
    law = [Fraction(math.comb(n, j) * even[n - j], tot) for j in range(n + 1)]
    assert sum(law) == 1
    return law


def zfix_law(n, q):
    """Law of #slots fixed with zero orientation (q = #orientations), uniform element of the
    piece group (orientation of a proper subset of slots is iid uniform; the identity-perm case
    has probability 2/n! and is treated the same way: error < 1e-17)."""
    fl = fix_law(n)
    out = [Fraction(0)] * (n + 1)
    for m, p in enumerate(fl):
        for j in range(m + 1):
            out[j] += p * math.comb(m, j) * Fraction(1, q) ** j * Fraction(q - 1, q) ** (m - j)
    return out


def moved_law():
    """Exact law of moved(z) (= #differing slots between two independent uniform states)."""
    lc, le = zfix_law(20, 3), zfix_law(30, 2)
    law = [Fraction(0)] * 51
    for a, pa in enumerate(lc):
        for b, pb in enumerate(le):
            law[50 - a - b] += pa * pb
    return law


def class_probs(n):
    """Exact P(cycle type = lam) for uniform A_n: 2/z_lam for even lam."""
    out = {}

    def parts(m, mx):
        if m == 0:
            yield ()
            return
        for k in range(min(m, mx), 0, -1):
            for rest in parts(m - k, k):
                yield (k,) + rest
    for lam in parts(n, n):
        if sum(k - 1 for k in lam) % 2:
            continue
        z = 1
        for k in set(lam):
            m = lam.count(k)
            z *= k ** m * math.factorial(m)
        out[lam] = Fraction(2, z)
    assert sum(out.values()) == 1
    return out


def wilson(k, n):
    return eng.ci95(k, n)


def chi2_cycletype(counts, probs, minexp=20):
    """Pearson chi-square of observed cycle-type counts against exact probs; classes with
    expected < minexp are pooled into one bin.  Returns (chi2, dof, p)."""
    from scipy.stats import chi2 as C2
    n = sum(counts.values())
    big = [lam for lam, p in probs.items() if float(p) * n >= minexp]
    bigset = set(big)
    x2 = 0.0
    for lam in big:
        e = float(probs[lam]) * n
        x2 += (counts.get(lam, 0) - e) ** 2 / e
    pe = float(1 - sum(probs[lam] for lam in big)) * n
    po = n - sum(counts.get(lam, 0) for lam in big)
    if pe > 0:
        x2 += (po - pe) ** 2 / pe
    dof = len(big) + (1 if pe > 0 else 0) - 1
    return x2, dof, float(C2.sf(x2, dof))


def selftest():
    """Fast pieces == in-tree engine: Ct(36) == C36 and Ct(76) == C76 em on random blocks; v2
    KAT via eng.selfcheck; inv_st == md.inverse; sweep coverage."""
    out = eng.selfcheck(10)
    rng = random.Random(1234)
    E76 = eng.engine('C76')
    for _ in range(200):
        h = uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        assert em_ct(h, d, 36) == E.em(h, d)
        assert em_ct(h, d, 76) == E76.em(h, d)
        assert inv_st(h) == eng.to_st(eng.inverse(eng.from_st(h)))
        assert compose_st(h, inv_st(h)) == ID_ST
    # one fast block equals the slow reference for t=36 and t=76
    for t in (36, 76, 0, 12):
        h = uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        a = eng.as_tuple_pos(eng.from_st(em_ct(h, d, t)))
        b = ref.em_block(eng.as_tuple_pos(eng.from_st(h)), d, t=t)
        assert a == b, t
    # sweep: distinct turn pairs as group elements
    els = set()
    for c1 in range(12):
        for c2 in eng.NBRS[c1]:
            s = list(ID_ST)
            apply(s, FACE_OP[c1])
            apply(s, FACE_OP[c2])
            els.add(tuple(s))
    assert len(els) == 60
    out.append('mdfix_lib: Ct(36)==C36, Ct(76)==C76 (200 blocks), fast==slow ref for t in 36,76,0,12, '
               'inv_st==md.inverse, sweep tour covers 50 slots, 60 turn pairs (c1,c2) distinct: OK')
    return out


if __name__ == '__main__':
    print('\n'.join(selftest()))
    print('cost', {k: cost(*k) for k in [('C', 36), ('C', 76), ('SWB', 12), ('SWB', 36)]})
    print('P(fixE>=2)', float(1 - sum(fix_law(30)[:2])), 'P(fixC>=2)', float(1 - sum(fix_law(20)[:2])))
    ml = moved_law()
    print('E[moved]', float(sum(k * p for k, p in enumerate(ml))))


# ---------------------------------------------------------------- F3b: a 2-turn blank round
# F3b round r: turn Up +1; read Up's noon piece at once (odd r corner, even r edge; c1 on Up,
# c2 on Front); turn Front +1 (same grip); re-grip c1/c2.  2 face turns, 2 clicks, 1 read,
# 1 re-grip per round (an F3 round is 1 / 1 / 1 / 1).
def _f3b_tables():
    tabs = [[None] * 60 for _ in range(2)]
    for par in (0, 1):
        for gi in range(60):
            o = GRIPS[gi]
            up, fr = o[0], o[1]
            idx, tab = eng.read_table(up, ref.vnoon(0, o), par)
            tabs[par][gi] = (FACE_OP[up], idx, tab, FACE_OP[fr])
    return tabs


F3B = _f3b_tables()


def f3b(st, t, gi=0):
    for r in range(1, t + 1):
        op1, s, tab, op2 = F3B[r & 1][gi]
        apply(st, op1)
        ng = tab[st[s]]
        apply(st, op2)
        gi = ng
    return gi


def dm_cb(h, deal, t):
    st = list(h)
    f3b(st, t, cards(st, deal))
    return compose_st(h, st)


def dm_swbb(h, deal, t):
    X = list(h)
    gi = cards(X, deal)
    B = inv_st(h)
    sweep_onto(B, X, gi)
    f3b(B, t, 0)
    return compose_st(inv_st(B), X)


_make_dm0 = make_dm


def make_dm(kind, t):  # noqa: F811
    if kind == 'Cb':
        return lambda h, d: dm_cb(h, d, t)
    if kind == 'SWBb':
        return lambda h, d: dm_swbb(h, d, t)
    return _make_dm0(kind, t)


_cost0 = cost


def cost(kind, t):  # noqa: F811
    if kind == 'Cb':
        return dict(turns=156 + 2 * t, clicks=234 + 2 * t, reads=52 + t, regrips=52 + t, solves=3)
    if kind == 'SWBb':
        return dict(turns=156 + 100 + 2 * t, clicks=234 + 100 + 2 * t, reads=52 + 50 + t, regrips=52 + 1 + t, solves=3)
    return _cost0(kind, t)
