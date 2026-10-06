"""Brute-force check of build_dp.analyse on small grids: enumerate the build process
tree explicitly (every layout with its exact probability)."""
import math, itertools
from build_dp import Rule, analyse, KIND_LEN

def enumerate_build(rule, n, m):
    out = {}
    grid = [[None] * m for _ in range(n)]
    def rec(pos, prob, ships):
        while pos < n * m and grid[pos // m][pos % m] is not None: pos += 1
        if pos == n * m:
            key = tuple(sorted(ships)); out[key] = out.get(key, 0) + prob; return
        i, j = divmod(pos, m)
        r = 0
        while j + r < m and grid[i][j + r] is None and r < 5: r += 1
        opts, Z = rule.local(r, n - i)
        for p, K, o in opts:
            if K is None:
                grid[i][j] = "."; rec(pos + 1, prob * p, ships); grid[i][j] = None
            else:
                L = KIND_LEN[K]
                cells = [(i, j + t) if o == "H" else (i + t, j) for t in range(L)]
                for bow in (0, 1):
                    for a, b in cells: grid[a][b] = K
                    rec(pos + 1, prob * p / 2, ships + [(K, o, cells[0], bow)])
                    for a, b in cells: grid[a][b] = None
    rec(0, 1.0, [])
    return out

if __name__ == "__main__":
    from rules import make_rules, extra_rules
    rules = [Rule("flat", 1, {"D": 1, "S": 1, "C": 1, "B": 1, "A": 1}),
             Rule("skew", 2, {"D": 2, "S": 0.5, "C": 0.5, "B": 0.25, "A": 0.1}, p_across=0.5),
             make_rules()["grow"], make_rules()["grow_w"], extra_rules()["bump_reroll"], extra_rules()["bump_turn"]]
    for rule in rules:
        for g in ([(2, 2), (2, 3), (3, 3), (3, 4), (4, 4), (2, 6), (5, 3)] if rule.name in ('flat', 'skew') else [(2, 3), (3, 3), (3, 4), (2, 6), (5, 3)]):
            dist = enumerate_build(rule, *g)
            P = list(dist.values())
            H = -sum(p * math.log2(p) for p in P); H2 = -math.log2(sum(p * p for p in P)); Hm = -math.log2(max(P))
            n3 = sum(p * sum(1 for s in k if KIND_LEN[s[0]] == 3) for k, p in dist.items())
            a = analyse(rule, *g)
            ok = all(abs(x - y) < 1e-9 for x, y in [(H, a["H"]), (H2, a["H2"]), (Hm, a["Hmin"]), (n3, a["n3"])])
            print(rule.name, g, f"layouts={len(P)} H={H:.6f} H2={H2:.6f} Hmin={Hm:.6f} n3={n3:.6f}", "DP agrees" if ok else ("MISMATCH", a))
            assert ok
