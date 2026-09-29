"""Exact c(n) = sum_y r(y)^2 / |H_n|, r(y) = #{x in H_n : x^2 = y}, for the scaled-down edge
groups H_n (even perms of n edges, even total flip).  c(n)/|H_n| is the probability that the
map x -> x^2 merges two independent uniform elements; compared with p2(n) = number of
bipartitions of n = number of conjugacy classes of the hyperoctahedral group B_n."""
import itertools, math
from collections import Counter

def p2(n):
    # number of pairs of partitions (a, b) with |a|+|b| = n
    p = [1] + [0]*n
    for k in range(1, n+1):
        for m in range(k, n+1): p[m] += p[m-k]
    return sum(p[i]*p[n-i] for i in range(n+1))

def parity(p):
    n = len(p); seen = [False]*n; par = 0
    for i in range(n):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]: seen[j] = True; j = p[j]; L += 1
            par ^= (L - 1) & 1
    return par

def c_of(n):
    perms = [p for p in itertools.permutations(range(n)) if parity(p) == 0]
    flips = [f for f in itertools.product((0, 1), repeat=n) if sum(f) % 2 == 0]
    cnt = Counter()
    for p in perms:
        for f in flips:
            # x∘x with the megaminx convention: (x x).p[s] = p[p[s]], (x x).f[s] = f[p[s]] + f[s]
            sq = (tuple(p[p[s]] for s in range(n)), tuple(f[p[s]] ^ f[s] for s in range(n)))
            cnt[sq] += 1
    H = len(perms) * len(flips)
    return sum(v*v for v in cnt.values()) / H, H

if __name__ == '__main__':
    for n in range(3, 9):
        c, H = c_of(n)
        print(f"n={n} |H|={H} c(n)={c:.2f} p2(n)={p2(n)} c/p2={c/p2(n):.3f}")
    print("p2(30) =", p2(30), "log2 =", round(math.log2(p2(30)), 2))
