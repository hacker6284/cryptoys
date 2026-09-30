"""Single-card position correlation of one UNKEYED v12 round (a "linear-like"
statistic for permutation-valued state; see NOTES.md for why and what it is not).

MEASUREMENT (random sampling, fixed seed), not a proof, not a bound.
U(x) = mix_columns(stem(x)) (lay_cm, SumRanks, ShiftRows, scoop_cm, GridCycle; no
key). For uniform decks x, M[i][j] = P[the card at input seat i ends at output seat j].
M is doubly stochastic; M = J/52 would mean the input seat of a card carries no
information about its output seat. Reported: the largest singular value of
M - J/52, i.e. the best "correlation" of a seat-indicator pair through the round,
next to the SAME statistic for a control: N uniformly random seat permutations
(sampling noise only). Also the largest single entry deviation.

Usage: python3 position_correlation.py [decks]   (default 2000000)
"""
import random
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

V = 12


def stats(M, n):
    D = M / n - 1.0 / 52
    sv = np.linalg.svd(D, compute_uv=False)
    i, j = np.unravel_index(np.argmax(np.abs(D)), D.shape)
    return sv[:3], (int(i), int(j), float(D[i, j]))


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    rng = random.Random(20260929)
    M = np.zeros((52, 52))
    C = np.zeros((52, 52))
    for _ in range(n):
        x = list(range(52))
        rng.shuffle(x)
        y = P.mix_columns(P.stem(x, V), V)
        where = [0] * 52
        for j, c in enumerate(y):
            where[c] = j
        for i, c in enumerate(x):
            M[i, where[c]] += 1
        p = list(range(52))
        rng.shuffle(p)
        for i in range(52):
            C[i, p[i]] += 1
    assert np.allclose(M.sum(axis=1), n) and np.allclose(M.sum(axis=0), n)
    for name, A in (('one unkeyed v12 round', M), ('control: uniform random seat permutations', C)):
        sv, (i, j, d) = stats(A, n)
        print(f'{name}: top singular values of M - J/52: {np.round(sv, 4).tolist()}; '
              f'largest |entry deviation| {d:+.4f} at seat {i} -> {j} (1/52 = {1 / 52:.4f})')
    print(f'decks: {n}, seed 20260929, port version {V}. MEASURED; the control shows the noise level.')


if __name__ == '__main__':
    main()
