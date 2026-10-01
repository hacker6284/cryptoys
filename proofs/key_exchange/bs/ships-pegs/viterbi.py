"""Find the single most likely layout (argmax probability) of a BUILD rule, by a
max-product DP with stored float32 tables and traceback."""
import math, numpy as np, sys, json
from build_dp import KIND_LEN
from rules import make_rules, extra_rules
from pathlib import Path
HERE = Path(__file__).resolve().parent            # every file path is anchored on this script's directory

def viterbi(rule, n=10, m=10):
    base = 5; size = base ** m
    idx = np.arange(size, dtype=np.int64)
    dig = [((idx // base ** (m - 1 - k)) % base).astype(np.int8) for k in range(m)]
    del idx
    run = [None] * m; nxt = np.zeros(size, dtype=np.int8)
    for j in range(m - 1, -1, -1):
        run[j] = np.where(dig[j] == 0, np.minimum(nxt + 1, 5), 0).astype(np.int8); nxt = run[j]
    NEG = np.float32(-1e30)
    lg = np.full(size, NEG, dtype=np.float32); lg[0] = 0
    store = {}
    for i in range(n):
        rl = n - i
        pend = {0: lg}
        get = lambda k: pend.setdefault(k, np.full(size, NEG, dtype=np.float32))
        for j in range(m):
            G = pend.pop(j); store[(i, j)] = G
            Gn = get(j + 1)
            d = dig[j]
            src = np.nonzero(d > 0)[0]
            dst = src - base ** (m - 1 - j); Gn[dst] = np.maximum(Gn[dst], G[src])
            free = np.nonzero((d == 0) & (G > -1e29))[0]
            rr = run[j][free]
            for r in range(1, 6):
                sel = free[rr == r]
                if len(sel) == 0: continue
                opts, Z = rule.local(min(r, m - j), rl)
                Gs = G[sel]
                for p, K, o in opts:
                    if p == 0: continue
                    if K is None: T, dd, pb = Gn, sel, p
                    else:
                        L = KIND_LEN[K]; pb = p / 2
                        if o == "V": T, dd = Gn, sel + (L - 1) * base ** (m - 1 - j)
                        else: T, dd = get(j + L), sel
                    T[dd] = np.maximum(T[dd], Gs + np.float32(math.log2(pb)))
        lg = pend.pop(m)
    best = float(lg[0])
    # traceback
    pw = [base ** (m - 1 - k) for k in range(m)]
    s, i, jp = 0, n - 1, m
    cur = best; ships = []
    def val(i, j, st): return float(store[(i, j)][st])
    while not (i == 0 and jp == 0):
        if jp == 0: i, jp = i - 1, m; continue
        j = jp - 1; d = (s // pw[j]) % base; rl = n - i
        cands = []
        if d + 1 < base: cands.append((val(i, j, s + pw[j]), j, s + pw[j], None))
        def locp(jj, st):
            r = 0
            while jj + r < m and (st // pw[jj + r]) % base == 0 and r < 5: r += 1
            return rule.local(r, rl)[0]
        if d == 0:
            for p, K, o in locp(j, s):
                if K is None: cands.append((val(i, j, s) + math.log2(p), j, s, None))
        for p, K, o in (locp(j, s - d * pw[j]) if d > 0 else []):
            if K and o == "V" and KIND_LEN[K] - 1 == d:
                s2 = s - d * pw[j]; cands.append((val(i, j, s2) + math.log2(p / 2), j, s2, (K, "V", i, j)))
        for L in range(2, 6):
            j0 = jp - L
            if j0 >= 0 and all((s // pw[k]) % base == 0 for k in range(j0, jp)):
                for p, K, o in locp(j0, s):
                    if K and o == "H" and KIND_LEN[K] == L:
                        cands.append((val(i, j0, s) + math.log2(p / 2), j0, s, (K, "H", i, j0)))
        c = max(cands, key=lambda t: t[0])
        _, jp, s, sh = c
        if sh: ships.append(sh)
    grid = [["." for _ in range(m)] for _ in range(n)]
    for K, o, r, c in ships:
        for t in range(KIND_LEN[K]):
            a, b = (r, c + t) if o == "H" else (r + t, c)
            grid[a][b] = K.lower() if o == "V" else K
    return -best, ["".join(row) for row in grid]

if __name__ == "__main__":
    R = {**make_rules(), **extra_rules()}[sys.argv[1]]     # bump_reroll (the SPEC rule) is in extra_rules
    h, g = viterbi(R)
    print(sys.argv[1], "Hmin", h); print("\n".join(g))
    json.dump({"rule": sys.argv[1], "Hmin": h, "grid": g}, open(HERE / f"viterbi_{sys.argv[1]}.json", "w"))
