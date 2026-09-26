"""Success rate of the same-rank relabel distinguisher on the REAL encrypt (Nr=6, PassKey schedule),
random keys, fixed query budget; plus a control (different-rank swap) and a CTR variant
(chosen distinct nonces N, tau.N; keystream recovered from known plaintext).
Usage: python3 success_rate.py [pairs_per_key] [n_keys]"""
import random, sys, os
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import dd_v8 as dd
def tau_swap(x, y):
    t = list(range(52)); t[x], t[y] = y, x; return t
def app(t, D): return [t[c] for c in D]
def run_key(args):
    k, npairs, mode = args
    R = random.Random(777 + 31*k + hash(mode) % 1000)
    K = list(range(52)); R.shuffle(K); keys = dd.expand_keys(K)
    hits = 0; first = None
    for q in range(npairs):
        if mode == 'ctr':
            N = list(range(39)); R.shuffle(N)
            r = R.randrange(13); s1, s2 = R.sample(range(3), 2)   # swap within C/H/S only
            t = tau_swap(13*s1 + r, 13*s2 + r)
            N2 = app(t, N)
            i = R.randrange(10**6)
            M = list(range(52)); R.shuffle(M)                        # known plaintext block
            C1 = dd.compose(M, dd.encrypt_keys(dd.counter_deck(N, i), keys))
            C2 = dd.compose(M, dd.encrypt_keys(dd.counter_deck(N2, i), keys))
            # attacker recovers keystreams from (M, C): pos_S(j) = M.index(C[j])
            def ks(C):
                S = [0]*52
                for j in range(52): S[M.index(C[j])] = j
                return S
            S1, S2 = ks(C1), ks(C2)
            hit = S2 == app(t, S1)
        else:
            M = list(range(52)); R.shuffle(M)
            if mode == 'attack':
                r = R.randrange(13); s1, s2 = R.sample(range(4), 2); t = tau_swap(13*s1 + r, 13*s2 + r)
            else:  # control: two cards of different rank
                while True:
                    x, y = R.sample(range(52), 2)
                    if dd.rank(x) != dd.rank(y): break
                t = tau_swap(x, y)
            C1 = dd.encrypt_keys(M, keys); C2 = dd.encrypt_keys(app(t, M), keys)
            hit = C2 == app(t, C1)
        if hit:
            hits += 1
            if first is None: first = q + 1
    if mode != 'ctr':  # sanity: encrypt_keys == public encrypt
        assert dd.encrypt_keys(M, keys) == dd.encrypt(M, K)
    return k, hits, first
if __name__ == '__main__':
    npairs = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 14
    nkeys = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    with Pool(8) as pool:
        for mode in ('attack', 'control', 'ctr'):
            res = pool.map(run_key, [(k, npairs, mode) for k in range(nkeys)])
            succ = sum(1 for _, h, _ in res if h > 0); tot = sum(h for _, h, _ in res)
            firsts = sorted(f for _, _, f in res if f)
            print(f'[{mode}] keys={nkeys} pairs/key={npairs} queries/key={2*npairs}: '
                  f'success={succ}/{nkeys} total_hits={tot} rate/pair={tot/(nkeys*npairs):.2e} '
                  f'median first-hit pair#={firsts[len(firsts)//2] if firsts else None}', flush=True)
