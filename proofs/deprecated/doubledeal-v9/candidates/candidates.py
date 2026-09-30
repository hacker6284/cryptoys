"""Python port of DoubleDeal v9 plus candidate patches (analysis only; NOT a spec change).

VARIANTS:
  v9   the frozen cipher (== ../attack/dd_v9.py)
  B4   GridCycle "slide along": when the target seat is taken, scan the TARGET row from the
       blocked column (wrapping), then the next rows down; the marker row counter is gone.
  R2   SumRanks "second row pass": rows, columns, then rows again (same row-total gesture).
  G    GridCycle "step again": a card whose target seat is taken repeats its own step
       (suit rows down, rank columns right) from the blocked seat until it finds a free seat;
       if the steps come back round to its own seat (K♣ at once), the v9 marker-row scan.
  GR2  G and R2.
  A3   SumRanks column weight rank - suit (mod 4) instead of rank + suit.
All variants stay invertible (see CANDIDATES.md). cand.c is the fast C mirror (check_cand.py).
"""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "attack"))
import dd_v9 as V
from dd_v9 import suit, rank, colw, rotl, lay_cm, scoop_cm, scoop_rm, shift_rows, compose, expand_keys

VARIANTS = {"v9": 0, "A3": 8, "R2": 2, "G": 4, "GR2": 6, "B4": 1}

def cw(x, var): return rank(x) - suit(x) if var & 8 else colw(x)
def rows(g): return [rotl(g[i], sum(rank(x) for x in g[i]) % 13) for i in range(4)]
def cols(g, var):
    g = [row[:] for row in g]
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(cw(x, var) for x in col) % 4
        for i in range(4): g[i][j] = col[(i - s) % 4]
    return g
def sum_ranks(g, var):
    g = cols(rows(g), var)
    return rows(g) if var & 2 else g
def walk(d, var):
    occ = [[False] * 13 for _ in range(4)]
    t = 0; seats = []
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            pc = d[i - 1]; pr, pcc = seats[-1]
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            r, c, t = seat_for(occ, t, pc, pr, pcc, tr, tc, var)
        occ[r][c] = True; seats.append((r, c))
    return seats
def seat_for(occ, t, card, pr, pc, tr, tc, var):
    """Seat for the card after `card` (sitting at (pr, pc)); target (tr, tc)."""
    if not occ[tr][tc]: return tr, tc, t
    if var & 1:
        r, c = next(((tr + a) % 4, (tc + k) % 13) for a in range(4) for k in range(13)
                    if not occ[(tr + a) % 4][(tc + k) % 13])
        return r, c, t
    if var & 4:
        hr, hc = tr, tc
        while True:
            hr, hc = (hr + suit(card)) % 4, (hc + rank(card)) % 13
            if (hr, hc) == (pr, pc): break
            if not occ[hr][hc]: return hr, hc, t
    return V.overflow_seat(occ, t, tc)
def mix_columns(d, var):
    grid = [[-1] * 13 for _ in range(4)]
    for card, (r, c) in zip(d, walk(d, var)): grid[r][c] = card
    return scoop_rm(grid)
def stem(m, var): return scoop_cm(shift_rows(sum_ranks(lay_cm(m), var)))
def encrypt_keys(m, keys, var, nfull=5, final=True):
    s = compose(m, keys[0])
    for r in range(1, nfull + 1): s = compose(mix_columns(stem(s, var), var), keys[r])
    return compose(stem(s, var), keys[nfull + 1]) if final else s
def encrypt(m, k0, var): return encrypt_keys(m, expand_keys(k0), var)

# inverses (to show each variant is still a cipher)
def inv_rows(g): return [rotl(g[i], -(sum(rank(x) for x in g[i]) % 13)) for i in range(4)]
def inv_cols(g, var):
    g = [row[:] for row in g]
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(cw(x, var) for x in col) % 4
        for i in range(4): g[i][j] = col[(i + s) % 4]
    return g
def inv_sum_ranks(g, var):
    if var & 2: g = inv_rows(g)
    return inv_rows(inv_cols(g, var))
def inv_mix_columns(d, var):
    grid = [list(d[13 * i:13 * i + 13]) for i in range(4)]
    occ = [[False] * 13 for _ in range(4)]; t = 0; hand = []; seat = None
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            pc = hand[-1]; pr, pcc = seat
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            r, c, t = seat_for(occ, t, pc, pr, pcc, tr, tc, var)
        occ[r][c] = True; seat = (r, c); hand.append(grid[r][c])
    return hand
def inv_stem(m, var):
    return scoop_cm(inv_sum_ranks([rotl(row, -i) for i, row in enumerate(lay_cm(m))], var))
def decrypt(c, k0, var):
    keys = expand_keys(k0)
    inv_compose = lambda x, k: [x[k[i]] for i in range(52)]
    s = inv_stem(inv_compose(c, keys[6]), var)
    for r in range(5, 0, -1): s = inv_stem(inv_mix_columns(inv_compose(s, keys[r]), var), var)
    return inv_compose(s, keys[0])
