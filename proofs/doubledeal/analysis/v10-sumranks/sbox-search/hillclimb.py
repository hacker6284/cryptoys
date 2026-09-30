"""Hill-climb over low-weight permutations maximising survival through v10 SumRanks.
mode V: value differences, score = same-difference survival (same_only).
mode P: position differences, score = count of the most common output difference (survey).
Moves: compose with a random transposition (one end inside the current support with prob 3/4), keep support
<= SMAX, never the identity. Scores use a fixed seed per climb (common random numbers); the final best of each
climb is re-measured on fresh decks. Usage: python3 hillclimb.py MODE RESTARTS STEPS NDECKS SMAX"""
import sys, random, sb
from multiprocessing import Pool
from sb import name
MODE, R, STEPS, ND, SMAX = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
def score(p, seed):
    if MODE == "V": return sb.same_only(p, ND, seed)
    return sb.survey(1, p, ND, seed)["top"]
def support(p): return [i for i in range(52) if p[i] != i]
def compose_t(p, a, b): q = p[:]; q[a], q[b] = p[b], p[a]; return q
def desc(p):
    seen, out = set(), []
    for i in range(52):
        if i in seen or p[i] == i: continue
        c, j = [], i
        while j not in seen: seen.add(j); c.append(j); j = p[j]
        out.append("(" + " ".join(name(x) if MODE == "V" else f"{x//13},{x%13}" for x in c) + ")")
    return "".join(out)
def climb(k):
    rng = random.Random(k); seed = 100 + k
    a, b = rng.sample(range(52), 2); p = compose_t(list(range(52)), a, b); s = score(p, seed)
    for _ in range(STEPS):
        sup = support(p)
        a = rng.choice(sup) if sup and rng.random() < 0.75 else rng.randrange(52)
        b = rng.randrange(52)
        if a == b: continue
        q = compose_t(p, a, b); sq = support(q)
        if not sq or len(sq) > SMAX: continue
        t = score(q, seed)
        if t >= s: p, s = q, t
    fresh = score(p, 999_000 + k) if MODE == "V" else sb.survey(1, p, ND * 10, 999_000 + k)["top"] / 10
    return (fresh, s, len(support(p)), desc(p))
if __name__ == "__main__":
    with Pool(8) as pool: res = pool.map(climb, range(R))
    res.sort(reverse=True)
    print(f"hill-climb mode {MODE}: {R} climbs x {STEPS} steps, {ND} decks per score, support <= {SMAX}")
    for f, s, n, d in res: print(f"  fresh {f:7.0f}/{ND} = {f/ND:.4g}   (climb score {s})  support {n:2d}  {d}")
