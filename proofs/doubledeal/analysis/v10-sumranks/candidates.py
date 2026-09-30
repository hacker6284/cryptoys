"""Python port of DoubleDeal v9 plus candidate patches (analysis only; NOT a spec change).

VARIANTS:
  v9   the frozen cipher (== proofs/deprecated/doubledeal-v9/attack/dd_v9.py)
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
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[3] / "deprecated/doubledeal-v9/attack"))
import dd_v9 as V
from dd_v9 import suit, rank, colw, rotl, lay_cm, scoop_cm, scoop_rm, shift_rows, compose, expand_keys

VARIANTS = {"v9": 0, "A3": 8, "R2": 2, "G": 4, "GR2": 6, "B4": 1, "SP": 16, "PW": 32, "PW2": 64, "PW3": 128, "SR2": 256, "SR3": 512, "W1": 1024, "W2": 2048, "W3": 4096, "W4": 8192,
            "W1x2": 1024 | 16384, "W3x2": 4096 | 16384, "W4x2": 8192 | 16384,
            "W5": 32768, "W5b": 65536, "W5x2": 32768 | 16384, "W5bx2": 65536 | 16384,
            "W5c": 131072, "W5cx2": 131072 | 16384}

def cw(x, var): return rank(x) - suit(x) if var & 8 else colw(x)
def rows(g): return [rotl(g[i], sum(rank(x) for x in g[i]) % 13) for i in range(4)]
def cols(g, var):
    g = [row[:] for row in g]
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(cw(x, var) for x in col) % 4
        for i in range(4): g[i][j] = col[(i - s) % 4]
    return g
def rot_col(g, j, s):
    col = [g[i][j] for i in range(4)]
    for i in range(4): g[i][j] = col[(i - s) % 4]
def cols_rank(g):
    g = [row[:] for row in g]
    for j in range(13): rot_col(g, j, sum(rank(g[i][j]) for i in range(4)) % 4)
    return g
def suit_product(g, inv=False):
    g = [row[:] for row in g]
    for j in range(13):
        p = 1
        for i in range(4): p = p * (suit(g[i][j]) + 1) % 5
        rot_col(g, j, (-1 if inv else 1) * (p % 4))
    return g
def roww(g, i): return sum((c + 1) * rank(g[i][c]) for c in range(13)) % 13
def colwt(g, j): return sum((r + 1) * (rank(g[r][j]) + suit(g[r][j])) for r in range(4)) % 4
def sum_ranks_pw(g):
    g = [row[:] for row in g]
    for a in range(1, 5):
        i = a % 4; g[i] = rotl(g[i], roww(g, (i + 3) % 4))
    for a in range(1, 14):
        j = a % 13; rot_col(g, j, colwt(g, (j + 12) % 13))
    return g
def inv_sum_ranks_pw(g):
    g = [row[:] for row in g]
    for a in range(13, 0, -1):
        j = a % 13; rot_col(g, j, -colwt(g, (j + 12) % 13))
    for a in range(4, 0, -1):
        i = a % 4; g[i] = rotl(g[i], -roww(g, (i + 3) % 4))
    return g
def roww2(g, i): return sum((c + 1) * (rank(g[i][c]) + suit(g[i][c])) for c in range(13)) % 13
def cols_suit(g, sgn=1):
    g = [row[:] for row in g]
    for j in range(13): rot_col(g, j, sgn * (sum(suit(g[i][j]) for i in range(4)) % 4))
    return g
def sum_ranks_pw2(g):
    g = [row[:] for row in g]
    for a in range(1, 5):
        i = a % 4; g[i] = rotl(g[i], roww2(g, (i + 3) % 4))
    return cols_suit(g)
def inv_sum_ranks_pw2(g):
    g = cols_suit(g, -1)
    for a in range(4, 0, -1):
        i = a % 4; g[i] = rotl(g[i], -roww2(g, (i + 3) % 4))
    return g
def colw3(g, j): return (sum((r + 1) * (rank(g[r][j]) + 4 * suit(g[r][j])) for r in range(4)) % 13) % 4
def sum_ranks_pw3(g):
    g = sum_ranks_pw2(g)
    for a in range(1, 14):
        j = a % 13; rot_col(g, j, colw3(g, (j + 12) % 13))
    return g
def inv_sum_ranks_pw3(g):
    g = [row[:] for row in g]
    for a in range(13, 0, -1):
        j = a % 13; rot_col(g, j, -colw3(g, (j + 12) % 13))
    return inv_sum_ranks_pw2(g)
WBITS = 1024 | 2048 | 4096 | 8192 | 32768 | 65536 | 131072
GFMUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
SUITGF = [0, 2, 3, 1]
def gfv(card, b): return SUITGF[suit(card)] ^ (rank(card) % 4 if b else 0)
def gfcol(g, j, b):
    v = 0
    for r in range(4): v ^= GFMUL[r][gfv(g[r][j], b)]
    return v
def wrow(g, i, ws): return sum((13 - c) * (rank(g[i][c]) + (suit(g[i][c]) if ws else 0)) for c in range(13)) % 13
def wcol5(g, j): return sum((4 - r) * (suit(g[r][j]) + 1) for r in range(4)) % 5
def w_colshift(g, j, own): return (wcol5(g, (j + 12) % 13) + (sum(suit(g[i][j]) for i in range(4)) if own else 0)) % 4
def w_pass(g, var, inv=False):
    g = [row[:] for row in g]; ws = bool(var & 2048)
    def rows_(g):
        order = [1, 2, 3, 0]
        for i in (reversed(order) if inv else order):
            g[i] = rotl(g[i], (-1 if inv else 1) * wrow(g, (i + 3) % 4, ws))
        return g
    def cols_(g):
        if var & (1024 | 2048): return inv_cols(g, 0) if inv else cols(g, 0)
        own = bool(var & 8192); order = list(range(1, 13)) + [0]
        gf = var & (32768 | 65536 | 131072); b = bool(var & 65536)
        for j in (reversed(order) if inv else order):
            sh = gfcol(g, (j + 12) % 13, b) if gf else w_colshift(g, j, own)
            if var & 131072:
                for i in range(4): sh ^= gfv(g[i][j], False)
            rot_col(g, j, (-1 if inv else 1) * sh)
        return g
    return rows_(cols_(g)) if inv else cols_(rows_(g))
def sum_ranks_w(g, var, inv=False):
    for _ in range(2 if var & 16384 else 1): g = w_pass(g, var, inv)
    return g
def sr_passes(var): return 3 if var & 512 else 2
def sum_ranks(g, var):
    if var & WBITS: return sum_ranks_w(g, var)
    if var & (256 | 512):
        for _ in range(sr_passes(var)): g = cols(rows(g), 0)
        return g
    if var & 128: return sum_ranks_pw3(g)
    if var & 64: return sum_ranks_pw2(g)
    if var & 32: return sum_ranks_pw(g)
    if var & 16: return suit_product(cols_rank(rows(g)))
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
def inv_cols_rank(g):
    g = [row[:] for row in g]
    for j in range(13): rot_col(g, j, -(sum(rank(g[i][j]) for i in range(4)) % 4))
    return g
def inv_sum_ranks(g, var):
    if var & WBITS: return sum_ranks_w(g, var, inv=True)
    if var & (256 | 512):
        for _ in range(sr_passes(var)): g = inv_rows(inv_cols(g, 0))
        return g
    if var & 128: return inv_sum_ranks_pw3(g)
    if var & 64: return inv_sum_ranks_pw2(g)
    if var & 32: return inv_sum_ranks_pw(g)
    if var & 16: return inv_rows(inv_cols_rank(suit_product(g, inv=True)))
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
