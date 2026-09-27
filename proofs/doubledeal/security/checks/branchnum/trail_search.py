"""Guided search for multi-round swap trails (analysis only).

Objective for R keyed rounds: lexicographic (number of leading rounds whose output difference is
still a swap, negated; then the weight after the first round that is not). This rewards pairs that
keep the swap alive for more rounds, which plain final-weight hill climbing (search.py) cannot see.
Moves: transpositions of the deck; swap positions resampled occasionally, preferring value pairs
that the round-1 analysis shows can survive (same rank, or a = b mod 4 in v9).

usage: python3 trail_search.py v R seconds nproc seed > trail_vV_R.log
  R = number of keyed full rounds (K1..KR), or R = 'enc' for the whole cipher
  (whitening K0, full rounds K1..K5, final round K6; whitening is a seat permutation).
"""
import sys, time, random
from multiprocessing import Pool
from common import *
import ddport
from dd_v8 import expand_keys
V, RA, SECS, NPROC, SEED = int(sys.argv[1]), sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
KS = expand_keys(FIXED_KEY)
if RA == 'enc':
    STEPS = [lambda x: compose(x, KS[0])] + [lambda x, k=KS[r]: ddport.full_round(x, k, V) for r in range(1, 6)] \
            + [lambda x: ddport.final_round(x, KS[6], V)]
    assert ddport.encrypt(list(range(52)), FIXED_KEY, V) == __import__('functools').reduce(lambda a, f: f(a), STEPS, list(range(52)))
else:
    STEPS = [lambda x, k=KS[r]: ddport.full_round(x, k, V) for r in range(1, int(RA) + 1)]
R = len(STEPS)

def profile(d, i, j):
    a, b = d, swap(d, i, j); ws = []
    for f in STEPS:
        a = f(a); b = f(b)
        ws.append(wt(a, b))
        if ws[-1] != 2: break
    alive = sum(1 for w in ws if w == 2)
    return (-alive, ws[-1]), ws

def run(seed):
    rng = random.Random(seed); t_end = time.time() + SECS; best = ((1, 99), None)
    while time.time() < t_end:
        d = rdeck(rng); i, j = rng.sample(range(52), 2)
        s, ws = profile(d, i, j); stale = 0
        while stale < 4000 and time.time() < t_end:
            d2, i2, j2 = list(d), i, j
            if rng.random() < 0.85:
                a, b = rng.sample(range(52), 2); d2[a], d2[b] = d2[b], d2[a]
            else:
                i2, j2 = rng.sample(range(52), 2)
            s2, ws2 = profile(d2, i2, j2)
            if s2 <= s:
                stale = 0 if s2 < s else stale + 1
                d, i, j, s, ws = d2, i2, j2, s2, ws2
            else: stale += 1
            if s < best[0]: best = (s, (list(d), i, j, ws))
            if s[0] == -R: return best
    return best

if __name__ == '__main__':
    with Pool(NPROC) as pool: res = pool.map(run, [SEED + k for k in range(NPROC)])
    res.sort(key=lambda x: x[0])
    what = 'full encrypt (steps: whitening, 5 full rounds, final round)' if RA == 'enc' else f'{R} keyed rounds (PassKey K1..K{R} of fixed master)'
    print(f'# v{V}, {what}, {SECS:.0f}s x {NPROC} processes, seed {SEED}')
    for s, (d, i, j, ws) in res:
        print(f'rounds alive as a swap: {-s[0]}/{R}; per-round weights {ws}; swap ({i},{j}) cards {NAMES[d[i]]},{NAMES[d[j]]}')
        print(f'    deck={d}')
