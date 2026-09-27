"""v8/v9 DoubleDeal port for T1 relabelling checks. v8 = frozen dd_v8.py; v9 adds A2 + B3."""
import sys
from pathlib import Path
REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / 'proofs/deprecated/doubledeal-v8/attack'))
import dd_v8 as V8
from dd_v8 import suit, rank, rotl, lay_cm, scoop_cm, scoop_rm, shift_rows, compose, expand_keys

def colw(v, x): return rank(x) if v == 8 else rank(x) + suit(x)

def sum_ranks(g, v):
    g = [row[:] for row in g]
    for i in range(4):
        g[i] = rotl(g[i], sum(rank(x) for x in g[i]) % 13)
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(colw(v, x) for x in col) % 4
        fresh = [col[(i - s) % 4] for i in range(4)]
        for i in range(4): g[i][j] = fresh[i]
    return g

def overflow_seat(occ, t, start):
    for _ in range(4):
        row = t
        for k in range(13):
            col = (start + k) % 13
            if not occ[row][col]: return row, col, (t + 1) % 4
        t = (t + 1) % 4
    raise AssertionError

def walk(d, v):
    """Seat sequence of the GridCycle walk."""
    occ = [[False]*13 for _ in range(4)]
    t = 0; seats = []
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            pc = d[i-1]; pr, pcc = seats[-1]
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if not occ[tr][tc]: r, c = tr, tc
            else: r, c, t = overflow_seat(occ, t, tc if v == 9 else 0)
        occ[r][c] = True; seats.append((r, c))
    return seats

def mix_columns(d, v):
    grid = [[-1]*13 for _ in range(4)]
    for card, (r, c) in zip(d, walk(d, v)): grid[r][c] = card
    return scoop_rm(grid)

def stem(m, v): return scoop_cm(shift_rows(sum_ranks(lay_cm(m), v)))
def full_round(m, k, v): return compose(mix_columns(stem(m, v), v), k)
def final_round(m, k, v): return compose(stem(m, v), k)
def encrypt(m, k0, v):
    keys = expand_keys(k0)
    m = compose(m, keys[0])
    for r in range(1, 6): m = full_round(m, keys[r], v)
    return final_round(m, keys[6], v)
