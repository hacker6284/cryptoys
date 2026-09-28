"""v8/v9/v10/v11 DoubleDeal port for T1 relabelling checks. v8 = frozen dd_v8.py; v9 adds A2 + B3;
v10 replaces SumRanks by the chained index-weighted rows and GF(4) suit columns (SPEC 3.3);
v11 replaces the GridCycle blocked placement (SPEC 3.5: ghost finger, blocker-directed scan).
Every version stays callable (v = 8, 9, 10, 11)."""
import json
import sys
from pathlib import Path
REPO = Path(__file__).resolve().parents[4]   # the repo root; use this instead of parents[n] elsewhere
sys.path.insert(0, str(REPO / 'proofs/deprecated/doubledeal-v8/attack'))
import dd_v8 as V8
from dd_v8 import suit, rank, rotl, lay_cm, scoop_cm, scoop_rm, shift_rows, compose, expand_keys

def colw(v, x): return rank(x) if v == 8 else rank(x) + suit(x)

# v10 SumRanks (SPEC 3.3). GF(4) labels: clubs 0, diamonds 1, hearts w = 2, spades w^2 = 3.
LABEL = [0, 2, 3, 1]                      # by suit index: clubs, hearts, spades, diamonds
TIMES_W = [0, 2, 3, 1]                    # x -> w x on labels
def label(x): return LABEL[suit(x)]
def row_turn(row): return sum((13 - j) * rank(x) for j, x in enumerate(row)) % 13
def column_value(g, p): return label(g[1][p]) ^ TIMES_W[label(g[2][p])] ^ TIMES_W[TIMES_W[label(g[3][p])]]
def column_suits(g, j): return label(g[0][j]) ^ label(g[1][j]) ^ label(g[2][j]) ^ label(g[3][j])
def column_turn(g, j): return column_value(g, (j + 12) % 13) ^ column_suits(g, j)
def turn_column(g, j, s):
    col = [g[i][j] for i in range(4)]
    for i in range(4): g[i][j] = col[(i - s) % 4]

def sum_ranks_v10(g):
    g = [row[:] for row in g]
    for i in (1, 2, 3, 0): g[i] = rotl(g[i], row_turn(g[(i + 3) % 4]))
    for j in list(range(1, 13)) + [0]: turn_column(g, j, column_turn(g, j))
    return g

def inv_sum_ranks_v10(g):
    g = [row[:] for row in g]
    for j in [0] + list(range(12, 0, -1)): turn_column(g, j, -column_turn(g, j))
    for i in (0, 3, 2, 1): g[i] = rotl(g[i], -row_turn(g[(i + 3) % 4]))
    return g

def sum_ranks(g, v):
    if v >= 10: return sum_ranks_v10(g)
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
    if v >= 11: return walk_v11(d)
    occ = [[False]*13 for _ in range(4)]
    t = 0; seats = []
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            pc = d[i-1]; pr, pcc = seats[-1]
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if not occ[tr][tc]: r, c = tr, tc
            else: r, c, t = overflow_seat(occ, t, tc if v >= 9 else 0)
        occ[r][c] = True; seats.append((r, c))
    return seats

def overflow_seat_v11(occ, row, start):
    """v11: first free seat of `row` from column `start` (wrapping); drop a row if full."""
    for _ in range(4):
        for k in range(13):
            col = (start + k) % 13
            if not occ[row][col]: return row, col
        row = (row + 1) % 4
    raise AssertionError

def step(card, r, c): return (r + suit(card)) % 4, (c + rank(card)) % 13

def walk_v11(d, table=None):
    """v11 seat sequence. Forward (table=None) reads blockers from the cards placed so far;
    inverse (table = laid row-major grid) reads them from the table. Same bookkeeping."""
    occ = [[False]*13 for _ in range(4)]
    grid = [[-1]*13 for _ in range(4)]
    t = 0; f = (2, 0); seats = []; prev = None
    for i in range(52):
        if i == 0: r, c = 2, 0
        else:
            tr, tc = step(prev, *f)
            if not occ[tr][tc]: r, c = tr, tc; f = (tr, tc)
            else:
                b = grid[tr][tc] if table is None else table[tr][tc]
                r, c = overflow_seat_v11(occ, (t + suit(b)) % 4, (tc + rank(b)) % 13)
                t = (t + 1) % 4; f = step(b, tr, tc)
        occ[r][c] = True; seats.append((r, c))
        prev = d[i] if table is None else table[r][c]
        grid[r][c] = prev
    return seats

def inv_mix_columns_v11(o):
    table = [o[13*r:13*r+13] for r in range(4)]
    return [table[r][c] for r, c in walk_v11(None, table)]

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


# Known-answer vectors per version (11 = current; 8, 9, 10 frozen).
VECTOR_JSON = {
    11: 'proofs/doubledeal/vectors/doubledeal_vectors.json',
    10: 'proofs/deprecated/doubledeal-v10/vectors/doubledeal_v10_vectors.json',
    9: 'proofs/deprecated/doubledeal-v9/vectors/doubledeal_v9_vectors.json',
    8: 'proofs/deprecated/doubledeal-v8/vectors/doubledeal_v8_vectors.json',
}
def vectors(v):
    """The list of vector dicts in version v's committed JSON."""
    return json.loads((REPO / VECTOR_JSON[v]).read_text())['vectors']


# The relabelling groups (card id -> card id, as a list of 52).
def v9sym(a, b):
    """v9Sym a b: rank + a (mod 13) and suit + b - (rank carry), the 52 relabellings that
    commute with v9 SumRanks (weight shifts of rank mod 13 and rank + suit mod 4)."""
    s = [None] * 52
    for c in range(52):
        r, su = rank(c), suit(c)
        r2 = (r - 1 + a) % 13 + 1
        s[c] = (su + b - (r2 - r)) % 4 * 13 + (r2 - 1)
    return s

SUIT_OF_LABEL = [LABEL.index(l) for l in range(4)]   # [0, 3, 1, 2]
def v10sym(a, x):
    """v10Sym a x: rank index + a (mod 13), GF(4) suit label XOR x (clubs 0, diamonds 1,
    hearts 2, spades 3); the 52 relabellings that commute with v10 SumRanks."""
    return [13 * SUIT_OF_LABEL[LABEL[c // 13] ^ x] + (c % 13 + a) % 13 for c in range(52)]
