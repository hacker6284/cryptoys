"""DoubleDeal v8 (deprecated) same-rank relabelling distinguisher. Evidence script.

For a fixed tau (default KC<->KD) and random keys, count pairs (M, tau M) with
E_K(tau M) == tau E_K(M), for full_rounds = 1..5 (5 = the real Nr=6 cipher:
whitening, 5 full rounds, final round). Also a control tau (two different ranks).
Usage: python3 relabel_attack.py [pairs_per_setting] [keys] [rounds,...]
"""
import random
import sys
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402


def swap(x, y):
    t = list(range(52))
    t[x], t[y] = y, x
    return t


TAUS = {'KC-KD': swap(12, 51), 'control-KC-QD': swap(12, 50)}


def work(a):
    tname, rounds, n, seed = a
    R = random.Random(seed)
    t = TAUS[tname]
    K = list(range(52))
    R.shuffle(K)
    keys = dd.expand_keys(K)
    hits = 0
    for _ in range(n):
        M = list(range(52))
        R.shuffle(M)
        C = dd.encrypt_keys(M, keys, rounds)
        C2 = dd.encrypt_keys([t[c] for c in M], keys, rounds)
        hits += C2 == [t[c] for c in C]
    return hits

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 64000
    nkeys = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    rounds = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else '1,2,3,5').split(',')]
    with Pool() as p:
        for tname in TAUS:
            for r in rounds:
                h = sum(p.map(work, [(tname, r, n // nkeys, 7919 * k + r) for k in range(nkeys)]))
                print(f'tau={tname:14s} full_rounds={r} pairs={n} keys={nkeys} hits={h} rate={h / n:.2e}', flush=True)
