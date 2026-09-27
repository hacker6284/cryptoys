"""Generalise the relabelling distinguisher on DoubleDeal v8 (frozen, deprecated).
For a family of relabellings tau, measure:
  - exact:   Pr[E_K(tau.M) == tau.E_K(M)]
  - agree:   mean number of seats where E_K(tau.M) and tau.E_K(M) agree (of 52)
A random permutation pair agrees on ~1 seat on average (E[matches]=52*1/52=1) and
exact match ~1/52!. So mean agreement >> 1 is a strong statistical distinguisher.
"""
import random
import sys
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402

KINDS = ('same_rank_swap', 'same_suit_swap', 'suit_perm_swap', 'rank_shift',
         'id_plus4', 'id_plus13', 'diff_rank_swap')

def tau_swap(pairs):
    t = list(range(52))
    for x, y in pairs: t[x], t[y] = t[y], t[x]
    return t
def app(t, D): return [t[c] for c in D]

def make_tau(kind, R):
    if kind == 'same_rank_swap':   # 5C<->5H
        r = R.randrange(13)
        s1, s2 = R.sample(range(4), 2)
        return tau_swap([(13*s1+r, 13*s2+r)])
    if kind == 'same_suit_swap':   # 5C<->6C  (different rank, same suit)
        s = R.randrange(4)
        r1, r2 = R.sample(range(13), 2)
        return tau_swap([(13*s+r1, 13*s+r2)])
    if kind == 'suit_perm_swap':   # swap two whole suits (13 transpositions, rank-preserving)
        s1, s2 = R.sample(range(4), 2)
        return tau_swap([(13*s1+r, 13*s2+r) for r in range(13)])
    if kind == 'rank_shift':       # r -> r+1 within each suit (id -> id with rank rotated)
        t = list(range(52))
        for c in range(52):
            s, r = c // 13, c % 13
            t[c] = 13*s + (r+1) % 13
        return t
    if kind == 'id_plus4':         # value id -> (id+4) mod 52  (mod-4 column blind)
        return [ (c+4)%52 for c in range(52) ]
    if kind == 'id_plus13':        # id -> (id+13) mod 52 == suit rotate, rank preserved
        return [ (c+13)%52 for c in range(52) ]
    if kind == 'diff_rank_swap':   # control
        while True:
            x,y = R.sample(range(52),2)
            if dd.rank(x)!=dd.rank(y): break
        return tau_swap([(x,y)])
    raise ValueError(kind)

def is_perm(t): return sorted(t)==list(range(52))

def run(args):
    kind, nkeys, npair = args
    exact = 0
    agree_sum = 0
    tot = 0
    for k in range(nkeys):
        # Deterministic per (kind, key). str hash() is salted per process, so it is not used.
        R = random.Random(9000 + 37*k + 1000*KINDS.index(kind))
        K = list(range(52))
        R.shuffle(K)
        keys = dd.expand_keys(K)
        for _ in range(npair):
            M = list(range(52))
            R.shuffle(M)
            t = make_tau(kind, R)
            C1 = dd.encrypt_keys(M, keys)
            C2 = dd.encrypt_keys(app(t, M), keys)
            Ct = app(t, C1)
            exact += (C2==Ct)
            agree_sum += sum(1 for a,b in zip(C2,Ct) if a==b)
            tot+=1
    return kind, exact, agree_sum, tot

if __name__=='__main__':
    nkeys=int(sys.argv[1]) if len(sys.argv)>1 else 6
    npair=int(sys.argv[2]) if len(sys.argv)>2 else 4000
    kinds = list(KINDS)
    # sanity: taus are perms
    Rc=random.Random(0)
    for kd in kinds:
        assert is_perm(make_tau(kd,Rc)), kd
    with Pool(min(8,len(kinds))) as p:
        res=p.map(run,[(kd,nkeys,npair) for kd in kinds])
    print(f'DoubleDeal v8, keys={nkeys}, pairs/key={npair}, random-perm baseline mean-agree~1.0, exact~0')
    for kind,exact,agree_sum,tot in sorted(res,key=lambda r:-r[2]/r[3]):
        print(f'  {kind:16s} exact={exact:6d}/{tot} ({exact/tot:.2e})  mean_agree={agree_sum/tot:6.3f}/52')
