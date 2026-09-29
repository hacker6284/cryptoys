"""Monte Carlo: full GridCycle survival of every value transposition (a b).

MEASUREMENT (random sampling, fixed seed), not a proof. For each of the 1326
transpositions s = (a b), estimates P_u[ walk_v11(s.u) == walk_v11(u) ]
(= P[mix_columns commutes with s at u], Lean mixColumns_rel_iff_walk) over
uniform decks u. Exact prefix upper bounds A_2, A_3 are in prefix_survival.log.

Usage: python3 transposition_survival.py [decks]   (default 2000)
"""
import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

N = [r + s for s in 'CHSD' for r in 'A23456789TJQK']


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    rng = random.Random(20260929)
    decks = []
    for _ in range(n):
        d = list(range(52))
        rng.shuffle(d)
        decks.append((d, P.walk_v11(d)))
    res = []
    for a, b in itertools.combinations(range(52), 2):
        k = 0
        for d, w in decks:
            sd = [b if c == a else a if c == b else c for c in d]
            k += P.walk_v11(sd) == w
        res.append((k / n, a, b))
    res.sort(reverse=True)
    mean = sum(r[0] for r in res) / len(res)
    print(f'decks: {n} (same decks for every transposition), transpositions: {len(res)}')
    print(f'MEASURED mean full survival over transpositions: {mean:.4f}')
    print(f'MEASURED max: {res[0][0]:.4f} ({N[res[0][1]]} {N[res[0][2]]}); min: {res[-1][0]:.4f}')
    print('top 10:', [(N[a], N[b], round(p, 4)) for p, a, b in res[:10]])
    hist = {}
    for p, _, _ in res:
        key = min(int(p * 10), 9)
        hist[key] = hist.get(key, 0) + 1
    print('histogram of survival (deciles):', {f'{k / 10:.1f}-{(k + 1) / 10:.1f}': v for k, v in sorted(hist.items())})


if __name__ == '__main__':
    main()
