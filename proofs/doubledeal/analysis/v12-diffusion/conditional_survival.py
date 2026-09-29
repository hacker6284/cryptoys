"""Monte Carlo: full GridCycle survival of v10Sym 0 3, conditioned on the first
three walk cards being one of the 30 surviving triples.

MEASUREMENT (random sampling, fixed seed), not a proof. The proved statement is
only the prefix bound  #survivors <= 52!/4420  (Lean, gc_survival_v10Sym03_le,
heavy library). This script estimates how much further the remaining 49 steps
cut survival down, i.e. P[full survival | first three cards in T03].

Two independent tests per sampled deck u (they must agree, Lean
mixColumns_rel_iff_walk): (a) walk_v11(s.u) == walk_v11(u); (b)
mix_columns(s.u) == s.mix_columns(u) with ddport's v12 mix_columns.

Usage: python3 conditional_survival.py [samples_per_triple]   (default 2000)
"""
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
sys.path.insert(0, str(HERE))
import ddport as P  # noqa: E402
from prefix_survival import seats_prefix  # noqa: E402


def triples(s):
    out = []
    for a in range(52):
        for b in range(52):
            if b == a:
                continue
            for c in range(52):
                if c in (a, b):
                    continue
                if seats_prefix([a, b, c]) == seats_prefix([s[a], s[b], s[c]]):
                    out.append((a, b, c))
    return out


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    s = P.v10sym(0, 3)
    T = triples(s)
    print(f'surviving first-card triples for v10Sym 0 3: {len(T)} (expected 30, exact enumeration)')
    assert len(T) == 30
    rng = random.Random(20260929)
    total = surv = 0
    per = []
    for t in T:
        rest = [c for c in range(52) if c not in t]
        k = 0
        for _ in range(n):
            rng.shuffle(rest)
            u = list(t) + rest
            su = [s[c] for c in u]
            a = P.walk_v11(su) == P.walk_v11(u)
            b = P.mix_columns(su, 12) == [s[c] for c in P.mix_columns(u, 12)]
            assert a == b, (u,)
            k += a
        per.append((t, k))
        total += n
        surv += k
    print(f'samples: {total} ({n} per triple), full survivals: {surv}')
    print(f'MEASURED P[full survival | prefix in T03] ~ {surv / total:.3e}')
    if surv == 0:
        print(f'  (0 observed; ~95% upper bound by rule of three: {3 / total:.3e})')
    print('per-triple survivals (nonzero only):', [(t, k) for t, k in per if k])


if __name__ == '__main__':
    main()
