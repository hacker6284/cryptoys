"""Monte Carlo: one-round characteristic probability P[RoundChar(tau, x)] for a few
relabellings tau, over uniform decks x (= the state after Compose with a uniform key).

MEASUREMENT (random sampling, fixed seed), not a proof. RoundChar (Lean,
DoubleDealSecurity/TrailBound.lean): the stem (lay_cm, SumRanks, ShiftRows, scoop_cm)
commutes with tau at x, AND GridCycle commutes with tau at stem(x). The proved
per-round bounds are 1/64 (tau outside v10Sym) and 1/4420 (nontrivial v10Sym; heavy).
Here "stem commutes" is tested directly on the port as stem(tau.x) == tau.stem(x),
which is implied by (and in the Lean statement replaced by) SumRanks commuting.

Usage: python3 round_char.py [decks]   (default 1000000)
"""
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P  # noqa: E402

V = 12
N = [r + s for s in 'CHSD' for r in 'A23456789TJQK']


def swap(a, b):
    s = list(range(52))
    s[a], s[b] = b, a
    return s


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    cases = {
        'AC<->2C (same-suit swap; SumRanks-alone exact 1/221)': swap(0, 1),
        'KC<->KD': swap(12, 51),
        '5D<->8D': swap(43, 46),
        'v10Sym 0 3': P.v10sym(0, 3),
    }
    def decks():
        rng = random.Random(20260929)
        for _ in range(n):
            d = list(range(52))
            rng.shuffle(d)
            yield d
    print(f'decks: {n} (same decks for every tau), seed 20260929, port version {V}')
    for name, s in cases.items():
        st = sr = both = 0
        for x in decks():
            sx = [s[c] for c in x]
            a = P.stem(x, V)
            if P.stem(sx, V) != [s[c] for c in a]:
                continue
            sr += 1
            if P.mix_columns([s[c] for c in a], V) == [s[c] for c in P.mix_columns(a, V)]:
                both += 1
        print(f'{name}: stem commutes {sr}/{n} = {sr / n:.3e}; '
              f'RoundChar {both}/{n} = {both / n:.3e}' +
              (f'  (0 observed; rule-of-three 95% bound {3 / n:.1e})' if both == 0 else ''))


if __name__ == '__main__':
    main()
