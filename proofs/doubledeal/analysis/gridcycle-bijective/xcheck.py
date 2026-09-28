"""Cross-check measure.c against independent Python.
V11, SR, PASSK and the v10 stem are checked against the repo's own port (ddport.py / dd_v8.py on the
doubledeal-v11 branch; pass its checkout root as argv[1], e.g. from
`git archive origin/doubledeal-v11 proofs/doubledeal/security/checks proofs/deprecated/doubledeal-v8/attack | tar -x -C /tmp/v11tree`).
PIVOT, TWIN, PASSM, PASSMR are re-implemented here from the README rule text, with their inverses.
usage: python3 xcheck.py /tmp/v11tree [N]"""
import sys, subprocess
from pathlib import Path
root = Path(sys.argv[1]); N = int(sys.argv[2]) if len(sys.argv) > 2 else 500
sys.path.insert(0, str(root / 'proofs/doubledeal/security/checks'))
sys.path.insert(0, str(root / 'proofs/deprecated/doubledeal-v8/attack'))
import ddport as D, dd_v8 as V8
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
def rotl(x, k): k %= len(x) if x else 1; return x[k:] + x[:k]
def lay_rm(d): return [list(d[13*i:13*i+13]) for i in range(4)]
def scoop_rm(g): return [g[r][c] for r in range(4) for c in range(13)]
def col_down(g, j, s):
    col = [g[i][j] for i in range(4)]
    for i in range(4): g[i][j] = col[(i - s) % 4]
ROWS, COLS = (1, 2, 3, 0), list(range(1, 13)) + [0]
def grid_layer(row_turn, col_turn):
    def fwd(d):
        g = lay_rm(d)
        for i in ROWS: g[i] = rotl(g[i], row_turn(g[(i + 3) % 4]))
        for j in COLS: col_down(g, j, col_turn(g, j))
        return scoop_rm(g)
    def inv(o):
        g = lay_rm(o)
        for j in reversed(COLS): col_down(g, j, -col_turn(g, j))
        for i in reversed(ROWS): g[i] = rotl(g[i], -row_turn(g[(i + 3) % 4]))
        return scoop_rm(g)
    return fwd, inv
pivot = grid_layer(lambda x: rank(x[0]), lambda g, j: suit(g[0][(j + 12) % 13]))
def tw_row(x): return (rank(x[0]) + sum((13 - j) * rank(c) for j, c in enumerate(x))) % 13
def tw_col(g, j):
    p = (j + 12) % 13
    return (suit(g[0][p]) + suit(g[1][p]) + 2*suit(g[2][p]) + 3*suit(g[3][p]) + sum(suit(g[i][j]) for i in range(4))) % 4
twin = grid_layer(tw_row, tw_col)
def passmix(hcut, kcut):
    def fwd(d):
        hand, key = list(d), []
        while hand:
            C = hand.pop(0)
            hand = rotl(hand, hcut(C)); key = rotl(key, kcut(C)); key.insert(0, C)
        return key
    def inv(o):
        key, hand = list(o), []
        while key:
            C = key.pop(0)
            key = rotl(key, -kcut(C)); hand = rotl(hand, -hcut(C)); hand.insert(0, C)
        return hand
    return fwd, inv
passm = passmix(rank, suit); passmr = passmix(suit, rank)
ref = {
    0: (lambda d: D.mix_columns(d, 11), D.inv_mix_columns_v11),
    1: (lambda d: D.scoop_cm(D.sum_ranks_v10(D.lay_cm(d))), None),
    2: pivot, 3: twin,
    5: (V8.passkey, V8.passkey_inv),
    6: passm, 8: passmr,
}
here = Path(__file__).resolve().parent
bad = 0
for L, (fwd, inv) in ref.items():
    out = subprocess.run([str(here / 'measure'), 'vec', str(L), str(N), '7'], capture_output=True, text=True, check=True).stdout.split('\n')
    mism = rt = 0
    for line in out:
        if not line: continue
        a, b = line.split(' '); d = list(map(int, a.split(','))); o = list(map(int, b.split(',')))
        mism += fwd(d) != o
        if inv: rt += inv(o) != d
    print(f'layer {L}: {N} decks, C-vs-Python output mismatches {mism}, Python inverse failures {rt}')
    bad += mism + rt
out = subprocess.run([str(here / 'stemvec'), str(N)], capture_output=True, text=True, check=True).stdout.split('\n')
sm = sum(1 for line in out if line and D.stem(list(map(int, line.split(' ')[0].split(','))), 10) != list(map(int, line.split(' ')[1].split(','))))
print(f'v10 stem: {N} decks, C-vs-ddport mismatches {sm}'); bad += sm
print('OK' if bad == 0 else 'FAIL')
