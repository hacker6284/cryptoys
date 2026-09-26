"""Per-layer tau-commutation probabilities (CURRENT cipher), per tau family, plus
per-rank breakdown for same-rank swaps in GridCycle, and agreement-count histogram for the
full cipher (is the relation all-or-nothing?)."""
import random, sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import dd_v8 as dd
from gen_attack import make_tau, app, tau_swap
from collections import Counter
R=random.Random(4); N=6000
def rp(): p=list(range(52)); R.shuffle(p); return p
kinds=['same_rank_swap','same_suit_swap','suit_perm_swap','rank_shift','id_plus4','id_plus13','diff_rank_swap']
print('layer commute prob: stem(SumRanks+ShiftRows) | GridCycle | full unkeyed round')
for kd in kinds:
    s=g=f=0
    for _ in range(N):
        D=rp(); t=make_tau(kd,R)
        s+= dd.unkeyed_stem(app(t,D))==app(t,dd.unkeyed_stem(D))
        g+= dd.mix_columns(app(t,D))==app(t,dd.mix_columns(D))
        f+= dd.unkeyed_full(app(t,D))==app(t,dd.unkeyed_full(D))
    print(f'  {kd:16s} {s/N:.4f} | {g/N:.4f} | {f/N:.4f}')
print('GridCycle commute prob for same-rank swap, by rank (N=3000 each):')
row=[]
for r in range(13):
    h=0
    for _ in range(3000):
        D=rp(); s1,s2=R.sample(range(4),2); t=tau_swap([(13*s1+r,13*s2+r)])
        h+= dd.mix_columns(app(t,D))==app(t,dd.mix_columns(D))
    row.append(f'{r+1}:{h/3000:.3f}')
print('  '+' '.join(row))
