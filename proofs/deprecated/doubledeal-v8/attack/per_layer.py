"""Per-layer tau-commutation probabilities (DoubleDeal v8, frozen), per tau family, plus
per-rank breakdown for same-rank swaps in GridCycle, and agreement-count histogram for the
full cipher (is the relation all-or-nothing?)."""
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402
from gen_attack import KINDS, make_tau, app, tau_swap  # noqa: E402

R = random.Random(4)
N = 6000


def rp():
    p = list(range(52))
    R.shuffle(p)
    return p


kinds = list(KINDS)
print('layer commute prob: stem(SumRanks+ShiftRows) | GridCycle | full unkeyed round')
for kd in kinds:
    s = g = f = 0
    for _ in range(N):
        D = rp()
        t = make_tau(kd, R)
        s+= dd.unkeyed_stem(app(t,D))==app(t,dd.unkeyed_stem(D))
        g+= dd.mix_columns(app(t,D))==app(t,dd.mix_columns(D))
        f+= dd.unkeyed_full(app(t,D))==app(t,dd.unkeyed_full(D))
    print(f'  {kd:16s} {s/N:.4f} | {g/N:.4f} | {f/N:.4f}')
print('GridCycle commute prob for same-rank swap, by rank (N=3000 each):')
row = []
for r in range(13):
    h = 0
    for _ in range(3000):
        D = rp()
        s1, s2 = R.sample(range(4), 2)
        t = tau_swap([(13*s1+r, 13*s2+r)])
        h+= dd.mix_columns(app(t,D))==app(t,dd.mix_columns(D))
    row.append(f'{r+1}:{h/3000:.3f}')
print('  '+' '.join(row))
