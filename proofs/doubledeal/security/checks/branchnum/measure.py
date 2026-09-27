"""Exhaustive-over-swaps measurement: for N random decks, apply all C(52,2)=1326 swaps and record
the output difference weight after each layer / combination, for v8 and v9.

usage: python3 measure.py N seed  > measure.log
Analysis only: empirical distributions over random decks, not a bound.
"""
import sys, random, collections
from multiprocessing import Pool
from common import FIXED_KEY_SEED, LAYERS, rdeck, swap, wt
from dd_v8 import mix_columns as v8_mix

N, SEED = int(sys.argv[1]), int(sys.argv[2])
PAIRS = [(i, j) for i in range(52) for j in range(i + 1, 52)]
KEYS = ['GC', 'SR', 'SRGC', 'SRGC_noSh', 'RK']

def work(args):
    seed, v = args
    rng = random.Random(seed)
    d = rdeck(rng)
    fs = {k: LAYERS[k](v) for k in KEYS}
    base = {k: f(d) for k, f in fs.items()}
    if v == 8: assert base['GC'] == v8_mix(d)      # ddport v8 path == frozen dd_v8
    hist = {k: collections.Counter() for k in KEYS}
    by_p = collections.defaultdict(lambda: 10**9)   # GC: min weight by first walk index p
    by_q = collections.defaultdict(lambda: 10**9)   # GC: min weight by last walk index q
    best = {k: (99, None) for k in KEYS}
    for (i, j) in PAIRS:
        e = swap(d, i, j)
        for k, f in fs.items():
            w = wt(base[k], f(e))
            hist[k][w] += 1
            if w < best[k][0]: best[k] = (w, (d, i, j))
            if k == 'GC':
                by_p[i] = min(by_p[i], w); by_q[j] = min(by_q[j], w)
        assert wt(base['RK'], fs['RK'](e)) == wt(base['SRGC'], fs['SRGC'](e))
    return v, hist, dict(by_p), dict(by_q), best

if __name__ == '__main__':
    jobs = [(SEED * 100000 + n, v) for v in (8, 9) for n in range(N)]
    agg = {v: {k: collections.Counter() for k in KEYS} for v in (8, 9)}
    bp = {v: collections.defaultdict(lambda: 10**9) for v in (8, 9)}
    bq = {v: collections.defaultdict(lambda: 10**9) for v in (8, 9)}
    best = {v: {k: (99, None) for k in KEYS} for v in (8, 9)}
    with Pool() as pool:
        # imap keeps job order, so a tie in the best weight goes to the lowest seed
        for v, h, p, q, b in pool.imap(work, jobs, chunksize=4):
            for k in KEYS:
                agg[v][k].update(h[k])
                if b[k][0] < best[v][k][0]: best[v][k] = b[k]
            for i, w in p.items(): bp[v][i] = min(bp[v][i], w)
            for j, w in q.items(): bq[v][j] = min(bq[v][j], w)
    print(f'# {N} random decks per version x all 1326 swaps (seed {SEED}); fixed key seed {FIXED_KEY_SEED}')
    print('# RK weight == SRGC weight asserted on every pair (Compose is a fixed seat permutation)')
    for v in (8, 9):
        for k in KEYS:
            h = agg[v][k]; tot = sum(h.values())
            mean = sum(w * c for w, c in h.items()) / tot
            lows = ' '.join(f'{w}:{h[w]}' for w in sorted(h) if w <= 12)
            cdf = lambda t: sum(c for w, c in h.items() if w <= t) / tot
            print(f'v{v} {k:10s} n={tot} min={min(h)} mean={mean:.2f} max={max(h)} '
                  f'P(w<=4)={cdf(4):.2e} P(w<=8)={cdf(8):.2e} P(w<=16)={cdf(16):.2e} | low counts {lows}')
        full = ' '.join(f'{w}:{agg[v]["SRGC"][w]}' for w in sorted(agg[v]['SRGC']))
        print(f'v{v} SRGC full histogram: {full}')
        print(f'v{v} GC min weight by first swapped walk index p: ' + ' '.join(f'{i}:{bp[v][i]}' for i in range(51)))
        print(f'v{v} GC min weight by second swapped walk index q: ' + ' '.join(f'{j}:{bq[v][j]}' for j in range(1, 52)))
        for k in KEYS:
            w, (d, i, j) = best[v][k]
            print(f'v{v} {k} best w={w}: swap positions ({i},{j}) deck={d}')
