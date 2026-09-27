"""How often does a swap stay a swap through consecutive keyed full rounds? (analysis only)

For N random decks (real PassKey keys K1..K3 of the fixed master key), apply all 1326 swaps,
push each through round 1; for every pair whose round-1 outputs differ by a swap (weight 2),
continue to rounds 2 and 3. Reports P(w1=2) and the conditionals P(w_{r+1}=2 | w_r=2), and where
the surviving swaps sit (walk indices of the GC input), to test whether the per-round events
behave independently.

usage: python3 multiround.py N seed > multiround.log
"""
import sys, random, collections
from multiprocessing import Pool
from common import FIXED_KEY, FIXED_KEY_SEED, rdeck, swap, wt
import ddport
from dd_v8 import expand_keys, rank
N, SEED = int(sys.argv[1]), int(sys.argv[2])
KS = expand_keys(FIXED_KEY)

def work(args):
    seed, v = args
    rng = random.Random(seed); d = rdeck(rng)
    R = [lambda x, k=KS[r]: ddport.full_round(x, k, v) for r in (1, 2, 3)]
    a = [d]
    for f in R: a.append(f(a[-1]))
    cnt = [0, 0, 0, 0]; pairs1 = collections.Counter(); rel = collections.Counter()
    for i in range(52):
        for j in range(i + 1, 52):
            cnt[0] += 1
            x = swap(d, i, j)
            for r, f in enumerate(R):
                x = f(x)
                if wt(x, a[r + 1]) != 2: break
                cnt[r + 1] += 1
                rel[(r + 1, relation(d[i], d[j]))] += 1
                if r == 0:
                    diff = tuple(k for k in range(52) if x[k] != a[1][k]); pairs1[diff] += 1
    return v, cnt, pairs1, rel

def relation(a, b):
    """Value relation of the swapped pair; it is preserved while the difference stays a swap
    (every weight-2 step just exchanges the seats of the same two cards)."""
    if rank(a) == rank(b): return 'same rank'
    if (a - b) % 4 == 0: return 'a=b mod 4'
    return 'other'

if __name__ == '__main__':
    jobs = [(SEED * 100000 + n, v) for v in (8, 9) for n in range(N)]
    tot = {8: [0]*4, 9: [0]*4}; where = {8: collections.Counter(), 9: collections.Counter()}
    rels = {8: collections.Counter(), 9: collections.Counter()}
    with Pool() as pool:
        for v, c, p, rl in pool.imap_unordered(work, jobs, chunksize=8):
            tot[v] = [x + y for x, y in zip(tot[v], c)]; where[v].update(p); rels[v].update(rl)
    print(f'# {N} random decks x 1326 swaps per version; keys K1..K3 = PassKey chain of fixed master (seed {FIXED_KEY_SEED})')
    for v in (8, 9):
        n0, n1, n2, n3 = tot[v]
        c = lambda a, b: f'{a}/{b} = {a/b:.3e}' if b else f'{a}/0'
        print(f'v{v}: P(w1=2) {c(n1, n0)} | P(w2=2 | w1=2) {c(n2, n1)} | P(w3=2 | w2=2) {c(n3, n2)}')
        for r in (1, 2, 3):
            h = {k[1]: c for k, c in rels[v].items() if k[0] == r}
            if h: print(f'v{v}: value relation of pairs still a swap after round {r}: {h}  '
                        f'(baseline over all 1326 pairs: same rank 78, a=b mod 4 ~{sum(1 for a in range(52) for b in range(a+1,52) if a%13!=b%13 and (a-b)%4==0)}, other rest)')
        top = where[v].most_common(8)
        print(f'v{v}: most frequent round-1 output swap positions (after K1): {top}')
