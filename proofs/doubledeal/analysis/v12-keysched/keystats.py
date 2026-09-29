"""Merge keystats.c raw counts and summarise (MEASUREMENT). Usage: python3 keystats.py raw/ks*.txt"""
import sys, math, collections
T = collections.defaultdict(int); C = collections.defaultdict(int)
FX = collections.defaultdict(int); CY = collections.defaultdict(int)
for f in sys.argv[1:]:
    for line in open(f):
        p = line.split()
        if p[0] == 'T': T[int(p[1]), int(p[2]), int(p[3])] += int(p[4])
        elif p[0] == 'C': C[int(p[2]), int(p[3]), int(p[4])] += int(p[5])
        elif p[0] == 'FX': FX[int(p[1]), int(p[2])] += int(p[3])
        elif p[0] == 'CY': CY[int(p[1]), int(p[2])] += int(p[3])
N = sum(T[1, 0, j] for j in range(52))
print(f'N = {N} uniform K0')
H52 = sum(1 / k for k in range(1, 53))
for s in (1, 2, 3):
    e = N / 52
    chi = sum((T[s, i, j] - e) ** 2 / e for i in range(52) for j in range(52))
    mx = max(((T[s, i, j] / e, i, j) for i in range(52) for j in range(52)))
    mn = min(((T[s, i, j] / e, i, j) for i in range(52) for j in range(52)))
    # mutual information (bits) of (seat of a card in K0, its seat in K_s), pooled over cards
    mi = sum((T[s, i, j] / (52 * N)) * math.log2((T[s, i, j] / (52 * N)) / (1 / 52 ** 2))
             for i in range(52) for j in range(52) if T[s, i, j])
    fx = sum(f * c for (ss, f), c in FX.items() if ss == s) / N
    cy = sum(k * c for (ss, k), c in CY.items() if ss == s) / N
    print(f's={s}: seat-transition chi2 = {chi:.0f} (df 2601; 99.9% point of chi2_2601 ~ 2840); '
          f'max cell/uniform = {mx[0]:.3f} at seat {mx[1]}->{mx[2]}, min = {mn[0]:.3f} at {mn[1]}->{mn[2]}; '
          f'pooled MI = {mi:.2e} bits (sampling bias ~ {2601 / (2 * 52 * N * math.log(2)):.1e}); '
          f'mean fixed seats {fx:.4f} (random perm: 1); mean cycles of relative perm {cy:.4f} (random: {H52:.4f})')
# per-card dependence, s = 1
worst = []
for c in range(52):
    n_c = N
    e = n_c / 52 ** 2
    chi = sum((C[c, i, j] - e) ** 2 / e for i in range(52) for j in range(52))
    worst.append((chi, c))
worst.sort()
names = [r + s for s in 'CHSD' for r in 'A23456789TJQK']
print('per-card seat-transition chi2 (s=1, df ~2601 each; uniform-joint null):',
      'min', f'{worst[0][0]:.0f} ({names[worst[0][1]]})', 'median', f'{worst[26][0]:.0f}', 'max', f'{worst[-1][0]:.0f} ({names[worst[-1][1]]})')
