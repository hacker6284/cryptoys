"""Physical simulation of the candidate BUILD rule 'grow' (re-roll whenever it bumps; not the
SPEC rule) with a d6, counting every roll, plus walk statistics for the READ rule, and a
chi-square check that the physical procedure has exactly the modelled distribution
(rules['grow']).  combined.py and sim_bump.py import its model_logp."""
import random, math, sys, json, collections
from read_rule import encode, bs_decode_exponent, bs_exponent, KL
from rules import make_rules

def build_grow(rng, n=10, m=10, stats=None):
    """The 'grow' rule as a player does it.  Returns ship list in encode() format."""
    occ = [[None] * m for _ in range(n)]      # None = open hole; '.' = miss peg; kind letter = ship
    ships = []
    rolls = 0
    def d6():
        nonlocal rolls; rolls += 1; return rng.randint(1, 6)
    while True:
        # next open hole: first hole in reading order with neither ship nor miss peg
        pos = next(((r, c) for r in range(n) for c in range(m) if occ[r][c] is None), None)
        if pos is None: break
        r, c = pos
        while True:
            if d6() <= 2:                     # sea
                occ[r][c] = "."; break
            across = d6() <= 3                # heading: low across, high down
            step = (0, 1) if across else (1, 0)
            cells = [(r, c)]
            ok = True
            def grow():
                a, b = cells[-1][0] + step[0], cells[-1][1] + step[1]
                if a >= n or b >= m or occ[a][b] is not None: return False
                cells.append((a, b)); return True
            if not grow(): ok = False          # a ship is at least 2 holes
            elif d6() >= 4:                    # 2 -> 3 on a high roll
                if not grow(): ok = False
                elif d6() == 6:                # 3 -> 4 only on a six
                    if not grow(): ok = False
                    elif d6() == 6:            # 4 -> 5 only on a six
                        if not grow(): ok = False
            if not ok: continue                # take it back, roll again for this hole
            L = len(cells)
            if L == 2: K = "D"
            elif L == 3: K = "S" if d6() <= 3 else "C"
            elif L == 4: K = "B"
            else: K = "A"
            bow = 0 if d6() <= 3 else 1        # bow: low = at the first hole, high = far end
            for a, b in cells: occ[a][b] = K
            ships.append((K, "H" if across else "V", (r, c), bow))
            break
    if stats is not None:
        stats["rolls"] += rolls; stats["ships"] += len(ships)
        stats["miss"] += sum(row.count(".") for row in occ)
    return ships

def model_logp(rule, ships, n=10, m=10):
    """log2 probability of a layout under the Rule model (product of local probs)."""
    start = {s[2]: s for s in ships}
    occ = [[False] * m for _ in range(n)]
    lp = 0.0
    for r in range(n):
        for c in range(m):
            if occ[r][c]: continue
            run = 0
            while c + run < m and not occ[r][c + run] and run < 5: run += 1
            opts, Z = rule.local(run, n - r)
            if (r, c) in start:
                K, o, _, bow = start[(r, c)]
                p = next(p for p, k, oo in opts if k == K and oo == o) / 2
                for t in range(KL[K]):
                    a, b = (r, c + t) if o == "H" else (r + t, c); occ[a][b] = True
            else:
                p = next(p for p, k, oo in opts if k is None); occ[r][c] = True
            lp += math.log2(p)
    return lp

if __name__ == "__main__":
    rule = make_rules()["grow"]
    rng = random.Random(2026)
    # 1. chi-square: physical procedure vs model on a 2x3 grid (139 layouts)
    from brute_build import enumerate_build
    for g in [(2, 3), (3, 3)]:
        exact = enumerate_build(rule, *g)
        N = 400000
        cnt = collections.Counter()
        for _ in range(N):
            sh = build_grow(rng, *g)
            key = tuple(sorted((K, o, cells, bow) for K, o, cells, bow in
                               [(K, o, [(r, c + t) if o == "H" else (r + t, c) for t in range(KL[K])][0], bow)
                                for K, o, (r, c), bow in sh]))
            cnt[key] += 1
        # map exact keys the same way
        ex = {}
        for k, p in exact.items():
            kk = tuple(sorted((K, o, cell0, bow) for K, o, cell0, bow in k))
            ex[kk] = ex.get(kk, 0) + p
        chi = sum((cnt[k] - N * p) ** 2 / (N * p) for k, p in ex.items())
        assert set(cnt) <= set(ex)
        print(f"chi-square {g}: {chi:.1f} on {len(ex)-1} df (physical procedure vs model)")
    # 2. 10x10 statistics
    st = collections.Counter(); N = 20000
    cells = hits = n3 = 0; lps = []; kinds = collections.Counter(); maxk = collections.Counter()
    for _ in range(N):
        sh = build_grow(rng, stats=st)
        t = encode(sh); assert bs_decode_exponent(bs_exponent(t)) == sorted(sh)
        cells += len(t); hits += sum(t)
        kc = collections.Counter(s[0] for s in sh); kinds.update(kc)
        for k, v in kc.items(): maxk[k] = max(maxk[k], v)
        lps.append(-model_logp(rule, sh))
    import statistics
    res = {"N": N, "rolls_per_grid": st["rolls"] / N, "ships_per_grid": st["ships"] / N,
           "miss_pegs_per_grid": st["miss"] / N, "cells_walked": cells / N, "hit_units": hits / N,
           "kinds_per_grid": {k: v / N for k, v in kinds.items()}, "max_kind_seen": dict(maxk),
           "MC_shannon": statistics.mean(lps), "MC_shannon_se": statistics.stdev(lps) / math.sqrt(N)}
    print(json.dumps(res, indent=1))
    json.dump(res, open("sim_build_results.json", "w"), indent=1)
