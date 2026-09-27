"""Structural checks behind the low-weight cases (analysis only; empirical confirmation of
statements that are proposed as Lean lemmas in NOTES.md).

 [1] GridCycle tail lemma: for every deck d, GC(swap d 50 51) differs from GC(d) in exactly 2 seats,
     and GC(d)[26] = d[0] (walk card 0 sits at seat (2,0) = row-major index 26).
 [2] GridCycle weight-2 characterisation: for a swap of walk indices p<q,
       w = 2  <=>  the seat sequence is unchanged.
     Necessary local condition: at step p (and at step q if q < 51) cards d[p] and d[q] lead to the
     same next seat. Sufficient: both targets blocked and the overflow scan returns the same seat
     (v8: scan ignores the target, so "both blocked" suffices; v9: scan starts at the target column,
     so two same-rank cards give the same seat once both are blocked). A second route exists: one
     target free and the other overflowing into exactly that seat; it desynchronises t, so it only
     gives w = 2 if no later overflow notices.
 [3] SumRanks exact swap classification (positions i,j of the column-major lay; a=d[i], b=d[j]):
       same row, a = b mod 4 (v9: rank+suit = c+1 mod 4) / rank = rank mod 4 (v8)   -> w = 2
       same row, otherwise                                                        -> w = 8
       different rows, same rank, same column after row rotation                  -> w = 2
       different rows, same rank, different columns after rotation: v9 -> 8, v8 -> 2
       different rows, different ranks                                            -> w >= M (measured)
 [4] Anatomy of weight-2 events of the unkeyed full round SRGC.
"""
import random, collections
from common import *
from dd_v8 import rank, suit

rng = random.Random(4242)
NDECK = 400

# ---------- [1] tail lemma and seat 26
for v in (8, 9):
    f = GC(v)
    for _ in range(20000):
        d = rdeck(rng); a = f(d)
        assert wt(a, f(swap(d, 50, 51))) == 2 and a[26] == d[0]
    print(f'[1] v{v}: 20000 random decks: GC(swap 50 51) has weight exactly 2; GC(d)[26] == d[0]')

# ---------- [2] weight-2 characterisation of GC
def step_info(d, v, seats, k):
    """At step k (card d[k] just placed at seats[k]): target of d[k] and whether it is occupied."""
    occ = [[False]*13 for _ in range(4)]
    for (r, c) in seats[:k+1]: occ[r][c] = True
    return occ

def walk_trace(d, v):
    """Re-implementation of ddport.walk that also records the overflow state t before each step."""
    occ = [[False]*13 for _ in range(4)]; t = 0; seats = []; ts = []
    for i in range(52):
        ts.append(t)
        r, c = 2, 0
        if i > 0:
            pc = d[i-1]; pr, pcc = seats[-1]
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if not occ[tr][tc]: r, c = tr, tc
            else: r, c, t = P.overflow_seat(occ, t, tc if v == 9 else 0)
        occ[r][c] = True; seats.append((r, c))
    assert seats == P.walk(d, v)
    return seats, ts

def next_seat(occ, t, r, c, x, v):
    tr, tc = (r + suit(x)) % 4, (c + rank(x)) % 13
    if not occ[tr][tc]: return (tr, tc), t, 'free'
    rr, cc, t2 = P.overflow_seat(occ, t, tc if v == 9 else 0)
    return (rr, cc), t2, 'ovf'

def kinds_at(d, e, v, p, q):
    """For a weight-2 swap (same seat sequence), label how the two walks leave seat p and seat q:
    'bb' = both overflow (to the same seat), 'fo' = one steps onto a free target and the other
    overflows onto that same seat (this desynchronises the overflow state t), 'end' = q is 51."""
    sd, td = walk_trace(d, v); se, te = walk_trace(e, v)
    assert sd == se
    labs = []
    for k in (p, q):
        if k == 51: labs.append('end'); continue
        occ = step_info(d, v, sd, k); r, c = sd[k]
        _, _, kx = next_seat(occ, td[k+1], r, c, d[k], v)
        _, _, ky = next_seat(occ, te[k+1], r, c, e[k], v)
        assert kx == 'ovf' or ky == 'ovf'      # distinct cards have distinct step offsets
        labs.append('bb' if kx == ky else 'fo')
    return tuple(labs)

for v in (8, 9):
    f = GC(v); tot = 0; kinds = collections.Counter(); samerank = collections.Counter()
    for _ in range(NDECK // 4):
        d = rdeck(rng); a = f(d); sd = P.walk(d, v)
        for p in range(52):
            for q in range(p+1, 52):
                e = swap(d, p, q); w = wt(a, f(e))
                assert (w == 2) == (P.walk(e, v) == sd)
                if w == 2:
                    kinds[kinds_at(d, e, v, p, q)] += 1
                    samerank[rank(d[p]) == rank(d[q])] += 1
                tot += 1
    print(f'[2] v{v}: {tot} swaps: w==2 <=> unchanged seat sequence (held on all). '
          f'Weight-2 mechanisms (leaving seat p, leaving seat q): {dict(kinds.most_common())}; '
          f'same-rank pairs among weight-2: {samerank[True]}/{sum(samerank.values())}')

# ---------- [3] SumRanks classification
def sr_class(d, i, j, v):
    g = lay_cm(d)
    ri, ci, rj, cj = i % 4, i // 4, j % 4, j // 4
    a, b = d[i], d[j]
    t = [sum(rank(x) for x in g[r]) % 13 for r in range(4)]
    w = (lambda x: rank(x)) if v == 8 else (lambda x: rank(x) + suit(x))
    if ri == rj: return 'row:same-w4' if (w(a) - w(b)) % 4 == 0 else 'row:diff-w4'
    if rank(a) == rank(b):
        # after the row stage a card at column c of row r sits at column (c - t_r) mod 13
        same_col = (ci - t[ri]) % 13 == (cj - t[rj]) % 13
        return 'rows,same-rank:same-col' if same_col else 'rows,same-rank:diff-col'
    return 'rows,diff-rank'

for v in (8, 9):
    f = SR(v); byc = collections.defaultdict(collections.Counter)
    for _ in range(NDECK):
        d = rdeck(rng); a = f(d)
        for i in range(52):
            for j in range(i+1, 52):
                byc[sr_class(d, i, j, v)][wt(a, f(swap(d, i, j)))] += 1
    for k in sorted(byc):
        h = byc[k]; tot = sum(h.values())
        print(f'[3] v{v} SR {k:26s} n={tot:7d} weights min={min(h)} max={max(h)} '
              + ('dist=' + str(dict(sorted(h.items()))) if len(h) <= 3 else f'mean={sum(w*c for w,c in h.items())/tot:.2f}'))

# ---------- [4] anatomy of SRGC weight-2 events
for v in (8, 9):
    st = lambda d: P.stem(d, v); g = GC(v); anat = collections.Counter(); n = 0
    for _ in range(NDECK):
        d = rdeck(rng); s0 = st(d); o0 = g(s0)
        for i in range(52):
            for j in range(i+1, 52):
                e = swap(d, i, j); s1 = st(e)
                if wt(o0, g(s1)) != 2: continue
                n += 1
                diff = [k for k in range(52) if s0[k] != s1[k]]
                assert len(diff) == 2   # SR stage must itself be a swap (GC is a bijection on 2-diffs only)
                p, q = diff
                anat[(sr_class(d, i, j, v), 'tail(50,51)' if (p, q) == (50, 51) else ('q=51' if q == 51 else 'double-overflow'))] += 1
    print(f'[4] v{v} SRGC weight-2 events over {NDECK} decks x 1326 swaps: {n}')
    for k, c in anat.most_common(): print(f'      {c:6d}  SR class {k[0]:26s} GC mechanism {k[1]}')
