"""How often is an edge-group element a square?  Needed for the backward
(square-root) half of the preimage meet-in-the-middle (finding F4).
Exact for small n (enumerate H_n and square everything); Monte-Carlo estimate
of the B_n-square criterion (signed cycle types) for n = 30.
Criterion in B_n = Z2 wr S_n: y is a square iff for every length m the number of
NEGATIVE m-cycles is even and, for even m, the number of POSITIVE m-cycles is even."""
import itertools, math, random
from collections import Counter
from toy_attacks import Toy, all_elements

def signed_cycles(p, f):
    n = len(p); seen = [False]*n; out = []
    for i in range(n):
        if seen[i]: continue
        j = i; L = 0; s = 0
        while not seen[j]:
            seen[j] = True; s ^= f[j]; j = p[j]; L += 1
        out.append((L, s))
    return out

def is_Bn_square(p, f):
    c = Counter(signed_cycles(p, f))
    for (L, s), k in c.items():
        if s == 1 and k % 2: return False
        if s == 0 and L % 2 == 0 and k % 2: return False
    return True

def rand_H(n, rng):
    p = list(range(n)); rng.shuffle(p)
    inv = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
    if inv & 1: p[0], p[1] = p[1], p[0]
    f = [rng.randrange(2) for _ in range(n-1)]; f.append(sum(f) & 1)
    return p, f

if __name__ == '__main__':
    for n in range(4, 9):
        T = Toy(1, n); H = list(all_elements(T))
        sq = Counter(T.comp(g, g) for g in H)
        bn = sum(is_Bn_square(*g) for g in H)
        print(f"n={n}: |H|={len(H)}  fraction of squares-in-H_n = {len(sq)/len(H):.4f}"
              f"  (B_n-square criterion: {bn/len(H):.4f}); mean #roots on squares = {len(H)/len(sq):.1f}")
    rng = random.Random(5)
    for n in (12, 20, 30):
        N = 200000
        k = sum(is_Bn_square(*rand_H(n, rng)) for _ in range(N))
        print(f"n={n}: Monte-Carlo B_n-square fraction ~ {k/N:.4f} (2^{math.log2(max(k,1)/N):.2f}), N={N}")
