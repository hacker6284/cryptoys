"""When does the Joux edge tree produce its first merge (= a full chaining collision)?
Real update e -> e X e versus an ideal random map, in the scaled-down edge groups H_n.
Reports the mean number of leaves 2^t generated when the first merge appears, and the
implied 'effective size' N_eff = (#states generated)^2 / 2."""
import random, math, sys
from exp_edge_tree import comp, rand_elem, order_H

def first_merge(n, rng, ideal=False, tmax=40):
    level = [rand_elem(n, rng)]
    oracle = {}; generated = 1
    for i in range(tmax):
        A, B = rand_elem(n, rng), rand_elem(n, rng)
        seen = set(); nxt = []
        for e in level:
            for X in (A, B):
                if ideal:
                    key = (e, X)
                    if key not in oracle: oracle[key] = rand_elem(n, rng)
                    y = oracle[key]
                else:
                    y = comp(comp(e, X, n), e, n)
                generated += 1
                if y in seen: return generated
                seen.add(y); nxt.append(y)
        level = nxt
    return None

if __name__ == '__main__':
    rng = random.Random(9)
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    for n in (6, 7, 8, 9, 10):
        H = order_H(n)
        r = [first_merge(n, rng) for _ in range(reps)]
        i = [first_merge(n, rng, ideal=True) for _ in range(reps)]
        mr = sum(r)/reps; mi = sum(i)/reps
        print(f"n={n:2d} log2|H|={math.log2(H):5.1f}  states to 1st merge: real={mr:8.0f} "
              f"(log2 {math.log2(mr):4.1f})  ideal={mi:8.0f} (log2 {math.log2(mi):4.1f})  "
              f"sqrt(pi|H|/2)=2^{math.log2(math.sqrt(math.pi*H/2)):4.1f}  gain=2^{math.log2(mi/mr):.1f}")
