"""Scaled-down model of the edge phase of the Joux attack.

After a Joux corner multicollision of length t, all 2^t messages share every corner state,
so at step i the edge part updates as e -> e * X * e with X in {A_i, B_i} (proved in Lean:
dmStep_word).  We simulate this in the scaled-down edge group H_n = {(perm, flips) : perm
even, sum(flips) even} (n edges; n = 30 is the real MegaDreifach edge group) with random
A_i, B_i and count distinct leaf values, versus a baseline where e*X*e is replaced by an
ideal random map.  Excess coalescence = the squaring map x -> x^2 merging states."""
import random, sys, math

def comp(g, h, n):     # megaminx convention: apply h first then g
    gp, gf = g; hp, hf = h
    return (tuple(hp[gp[s]] for s in range(n)), tuple((hf[gp[s]] + gf[s]) & 1 for s in range(n)))

def parity(p):
    n = len(p); seen = [False]*n; par = 0
    for i in range(n):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]: seen[j] = True; j = p[j]; L += 1
            par ^= (L - 1) & 1
    return par

def rand_elem(n, rng):
    while True:
        p = list(range(n)); rng.shuffle(p)
        if parity(p) == 0: break
    f = [rng.randrange(2) for _ in range(n - 1)]; f.append(sum(f) & 1)
    return (tuple(p), tuple(f))

def order_H(n):
    return math.factorial(n) // 2 * 2 ** (n - 1)

def run(n, t, rng, ideal=False):
    e0 = rand_elem(n, rng)
    level = {e0}
    oracle = {}
    for i in range(t):
        A, B = rand_elem(n, rng), rand_elem(n, rng)
        nxt = set()
        for e in level:
            for X in (A, B):
                if ideal:
                    key = (e, X)
                    if key not in oracle: oracle[key] = rand_elem(n, rng)
                    nxt.add(oracle[key])
                else:
                    nxt.add(comp(comp(e, X, n), e, n))
        level = nxt
    return len(level)

if __name__ == '__main__':
    rng = random.Random(5)
    for n, t, reps in ((6, 12, 20), (7, 13, 10), (8, 14, 6)):
        H = order_H(n)
        real = [run(n, t, rng) for _ in range(reps)]
        ideal = [run(n, t, rng, ideal=True) for _ in range(reps)]
        print(f"n={n} |H|={H} (2^{math.log2(H):.1f}) t={t} leaves=2^{t}: "
              f"distinct(real e X e)={sum(real)/reps:.0f}  distinct(ideal random map)={sum(ideal)/reps:.0f}")
