"""Aggregate survival runs: python3 agg.py value|pos [top]"""
import sys, glob, math
from collections import defaultdict
mode = sys.argv[1]; top = int(sys.argv[2]) if len(sys.argv) > 2 else 25
H = defaultdict(int); N = defaultdict(int)
for f in glob.glob(f'runs/{mode}_*.txt'):
    for line in open(f):
        a, b, h, n = map(int, line.split()); H[a, b] += h; N[a, b] += n
S = 'CHSD'; R = 'A23456789TJQK'
def nm(c): return R[c % 13] + S[c // 13]
def wilson(h, n, z=1.96):
    p = h / n; den = 1 + z*z/n; c = p + z*z/(2*n); r = z*math.sqrt(p*(1-p)/n + z*z/(4*n*n))
    return (c - r) / den, (c + r) / den
rows = sorted(H, key=lambda k: -H[k] / N[k])
print(f'{mode}: {len(H)} pairs, N = {N[rows[0]]} decks per pair')
for k in rows[:top]:
    h, n = H[k], N[k]; lo, hi = wilson(h, n)
    lab = f'{nm(k[0])}<->{nm(k[1])}' if mode == 'value' else f'pos {k[0]},{k[1]}'
    print(f'{lab:14s} {h:7d}/{n}  p={h/n:.5f} (1/{n/max(h,1):.1f})  95% CI [{lo:.5f},{hi:.5f}]')
tot = sum(H.values()); ntot = sum(N.values())
print(f'mean over pairs p={tot/ntot:.3e}; pairs with 0 hits: {sum(1 for k in H if H[k]==0)}')
if mode == 'value':
    # by class
    cls = defaultdict(lambda: [0, 0])
    for (a, b) in H:
        key = ('same-rank' if a % 13 == b % 13 else 'same-suit' if a // 13 == b // 13 else 'other')
        cls[key][0] += H[a, b]; cls[key][1] += N[a, b]
    for key, (h, n) in cls.items(): print(f'class {key}: mean p={h/n:.3e}')
