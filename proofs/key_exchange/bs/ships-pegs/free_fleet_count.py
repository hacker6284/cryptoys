#!/usr/bin/env python3
"""
Exact count of "free fleet" Battleship layouts on an n x m grid (default 10x10).

Kinds: Destroyer 2, Submarine 3, Cruiser 3, Battleship 4, Carrier 5 (Sub != Cruiser).
Any number of ships, straight, inside the grid, non-overlapping, touching allowed,
empty holes allowed (except in variant D).

  A : ships carry a bow (direction)  -> each ship weight 2
  B : ships are unordered cell sets + kind -> weight 1
  C : B, but no two ships of the SAME kind may lie end-to-end in the same line
      (same orientation, collinear, touching end cell to end cell).
      Computed by inclusion-exclusion: a chain of m same-kind collinear ships is a
      single "piece" of length m*L with weight (-1)^(m-1).  Net piece weights:
      len2:+1 len3:+2 len4:0 len5:+1 len6:-1 len7:0 len8:-2 len9:+2 len10:0
  D : B restricted to full tilings (no empty holes).  (D_A = same with bows.)

Method: row-major broken-profile DP.  Profile digit for column j = number of cells a
vertical ship still has to cover BELOW the current row (the kind was already paid for
when the ship was started, so the kind need not be stored -> only 5 values 0..4,
5^10 = 9.8M states for 10 wide).  A horizontal ship started at (i,j) checks that the
next L-1 columns are free in the not-yet-processed part of the profile and jumps
directly to position j+L.  Arithmetic is done modulo several ~2^58 primes with numpy
int64 arrays and recombined by CRT (big integers).  Independent checks: a pure Python
big-int dict DP and a brute-force enumeration of placements/labellings on tiny grids.
"""
import math, sys, time, itertools, json
from functools import reduce
import numpy as np

KINDS = [("D", 2), ("S", 3), ("C", 3), ("B", 4), ("A", 5)]

def pieces_for(variant):
    """length -> weight"""
    if variant in ("A", "DA"):
        w = 2
    else:
        w = 1
    if variant in ("A", "B", "D", "DA"):
        pw = {}
        for _, L in KINDS:
            pw[L] = pw.get(L, 0) + w
        return pw
    if variant == "C":
        pw = {}
        for _, L in KINDS:
            m = 1
            while m * L <= 10:           # longest possible chain on 10-long line
                pw[m * L] = pw.get(m * L, 0) + (-1) ** (m - 1)
                m += 1
        return {k: v for k, v in pw.items() if v != 0}
    raise ValueError(variant)

def allow_empty_for(variant):
    return variant not in ("D", "DA")

# ---------------------------------------------------------------- primes / CRT
def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def primes_below(start, k):
    out, q = [], start
    while len(out) < k:
        q -= 1
        if is_prime(q): out.append(q)
    return out

PRIMES = primes_below(2 ** 58, 40)

def crt(residues, mods):
    M = reduce(lambda a, b: a * b, mods)
    x = 0
    for r, q in zip(residues, mods):
        Mi = M // q
        x += r * Mi * pow(Mi, -1, q)
    x %= M
    if x > M // 2:          # allow signed (never needed for final counts, all >= 0)
        x -= M
    return x, M

# ---------------------------------------------------------------- numpy DP
def dp_numpy(n, m, pieces, allow_empty, p=None, as_float=False):
    """Returns count mod p (int) or, if as_float, log2 of count (float estimate)."""
    vert = {L: w for L, w in pieces.items() if L <= n}
    maxrem = max([L - 1 for L in vert] + [0])
    base = maxrem + 1
    size = base ** m
    dt = np.float64 if as_float else np.int64
    cur = np.zeros(size, dtype=dt); cur[0] = 1
    logscale = 0.0
    for i in range(n):
        if as_float:
            mx = np.abs(cur).max()
            if mx == 0: return float("-inf")
            cur /= mx; logscale += math.log2(mx)
        pend = {0: cur}
        def get(k):
            if k not in pend:
                pend[k] = np.zeros(size, dtype=dt)
            return pend[k]
        for j in range(m):
            A = pend.pop(j)
            Av = A.reshape(base ** j, base, base ** (m - 1 - j))
            B = get(j + 1)
            Bv = B.reshape(base ** j, base, base ** (m - 1 - j))
            for v in range(1, base):                       # continuing vertical ship
                Bv[:, v - 1, :] += Av[:, v, :]
            free = Av[:, 0, :]
            if allow_empty:
                Bv[:, 0, :] += free
            for L, w in vert.items():                     # start vertical ship here
                if L <= n - i:
                    if w > 0: Bv[:, L - 1, :] += w * free
                    else:     Bv[:, L - 1, :] -= (-w) * free
            if not as_float:
                np.remainder(B, p, out=B)
            for L, w in pieces.items():                   # start horizontal ship here
                if j + L <= m:
                    T = get(j + L)
                    Ah = A.reshape(base ** j, base ** L, base ** (m - j - L))[:, 0, :]
                    Th = T.reshape(base ** j, base ** L, base ** (m - j - L))
                    if w > 0: Th[:, 0, :] += w * Ah
                    else:     Th[:, 0, :] -= (-w) * Ah
                    if not as_float:
                        Th[:, 0, :] %= p
            del A, Av
        cur = pend.pop(m)
    if as_float:
        v = cur[0]
        return (math.log2(v) + logscale) if v > 0 else float("nan")
    return int(cur[0]) % p

def _worker(args):
    n, m, variant, p = args
    return dp_numpy(n, m, pieces_for(variant), allow_empty_for(variant), p=p)

def exact_count(n, m, variant, procs=4, verbose=True):
    pieces, ae = pieces_for(variant), allow_empty_for(variant)
    est = dp_numpy(n, m, pieces, ae, as_float=True)
    need_bits = (est if est == est else 0) + 64
    k = max(2, math.ceil(need_bits / 57) + 1)          # +1 prime = consistency check
    mods = PRIMES[:k]
    t = time.time()
    if procs > 1 and base_size(n, m, pieces) > 10 ** 5:
        from multiprocessing import Pool
        with Pool(min(procs, k)) as pool:
            res = pool.map(_worker, [(n, m, variant, q) for q in mods])
    else:
        res = [_worker((n, m, variant, q)) for q in mods]
    x_all, _ = crt(res, mods)
    x_less, _ = crt(res[:-1], mods[:-1])
    assert x_all == x_less, "CRT not stable - need more primes"
    assert x_all >= 0
    if verbose:
        print(f"  {n}x{m} {variant}: {k} primes, {time.time()-t:.1f}s, float est log2={est:.4f}", flush=True)
    return x_all

def base_size(n, m, pieces):
    vert = [L for L in pieces if L <= n]
    return (max(vert + [1])) ** m

# ---------------------------------------------------------------- pure python exact DP
def dp_dict(n, m, pieces_list, allow_empty, need_mask=None):
    """pieces_list: list of (L, weight, bit).  bit != 0 -> each bit used at most once and
    final mask must equal need_mask (for the standard-fleet count)."""
    states = {((0,) * m, 0, 0): 1}          # (profile, h, mask)
    for i in range(n):
        for j in range(m):
            new = {}
            for (prof, h, mask), c in states.items():
                if h > 0:
                    if prof[j] != 0: continue
                    key = (prof, h - 1, mask)
                    new[key] = new.get(key, 0) + c
                    continue
                if prof[j] > 0:
                    pl = list(prof); pl[j] -= 1
                    key = (tuple(pl), 0, mask)
                    new[key] = new.get(key, 0) + c
                    continue
                if allow_empty:
                    key = (prof, 0, mask)
                    new[key] = new.get(key, 0) + c
                for L, w, bit in pieces_list:
                    if bit and (mask & bit): continue
                    nm = mask | bit
                    if L <= n - i:
                        pl = list(prof); pl[j] = L - 1
                        key = (tuple(pl), 0, nm)
                        new[key] = new.get(key, 0) + c * w
                    if j + L <= m:
                        key = (prof, L - 1, nm)
                        new[key] = new.get(key, 0) + c * w
            states = {k: v for k, v in new.items() if v != 0}
    tot = 0
    for (prof, h, mask), c in states.items():
        if h == 0 and not any(prof) and (need_mask is None or mask == need_mask):
            tot += c
    return tot

def dict_count(n, m, variant):
    pw = pieces_for(variant)
    return dp_dict(n, m, [(L, w, 0) for L, w in pw.items()], allow_empty_for(variant))

# ---------------------------------------------------------------- brute force
def brute(n, m):
    """Enumerate every placement explicitly (kinds, orientation, bow).  Returns dict of
    counts A, B, C, D, DA and checks that labellings are pairwise distinct."""
    grid = [[None] * m for _ in range(n)]
    ships = []
    labA, labB = set(), set()
    labKP = {}
    cnt = dict(A=0, B=0, C=0, D=0, DA=0)
    def first_free():
        for r in range(n):
            for c in range(m):
                if grid[r][c] is None: return r, c
        return None
    def record():
        full = all(grid[r][c] != "." for r in range(n) for c in range(m))
        # labelling without bow: cell -> (kind, index of cell from top/left end, orientation)
        # (orientation needed: a 2x2 of destroyers H vs V differ)
        lb = tuple(tuple(grid[r][c] for c in range(m)) for r in range(n))
        assert lb not in labB; labB.add(lb)
        k = len(ships)
        cnt["B"] += 1; cnt["A"] += 2 ** k
        if full: cnt["D"] += 1; cnt["DA"] += 2 ** k
        # labelling with bow: each ship has 2 choices -> "part k" counted from the bow
        for bows in itertools.product((0, 1), repeat=k):
            lab = {}
            for (K, L, cells), b in zip(ships, bows):
                seq = cells if b == 0 else cells[::-1]
                for idx, cell in enumerate(seq):
                    lab[cell] = (K, idx + 1)
            key = tuple(lab.get((r, c), ".") for r in range(n) for c in range(m))
            keyo = tuple((lab[(r, c)], grid[r][c][1]) if (r, c) in lab else "."
                         for r in range(n) for c in range(m))
            assert keyo not in labA; labA.add(keyo)      # (kind, part, H/V) labels: injective
            labKP[key] = labKP.get(key, 0) + 1           # (kind, part) labels only
        # variant C: same kind, same orientation, collinear, end-to-end
        ok = True
        ends = {}
        for K, L, cells in ships:
            o = "H" if (len(cells) > 1 and cells[0][0] == cells[1][0]) else "V"
            ends[(K, o, cells[0])] = True
        for K, L, cells in ships:
            o = "H" if cells[0][0] == cells[1][0] else "V"
            r, c = cells[-1]
            nxt = (r, c + 1) if o == "H" else (r + 1, c)
            if (K, o, nxt) in ends: ok = False
        if ok: cnt["C"] += 1
    def rec():
        ff = first_free()
        if ff is None:
            record(); return
        r, c = ff
        grid[r][c] = "."; rec(); grid[r][c] = None
        for K, L in KINDS:
            for o in "HV":
                cells = [(r, c + t) if o == "H" else (r + t, c) for t in range(L)]
                if all(0 <= a < n and 0 <= b < m and grid[a][b] is None for a, b in cells):
                    for t, (a, b) in enumerate(cells): grid[a][b] = (K, o, t)
                    ships.append((K, L, cells)); rec(); ships.pop()
                    for a, b in cells: grid[a][b] = None
    rec()
    assert len(labB) == cnt["B"] and len(labA) == cnt["A"]
    cnt["A_KPlabels"] = len(labKP)
    brute.last_labKP = labKP
    return cnt

# ---------------------------------------------------------------- standard fleet
def standard_fleet(n=10, m=10):
    pl = [(L, 1, 1 << idx) for idx, (K, L) in enumerate(KINDS)]
    return dp_dict(n, m, pl, True, need_mask=31)

def brute_standard_small(n, m, kinds):
    """brute force: place each listed kind exactly once (no bow)."""
    placements = []
    for K, L in kinds:
        ps = []
        for r in range(n):
            for c in range(m):
                for o in "HV":
                    cells = frozenset((r, c + t) if o == "H" else (r + t, c) for t in range(L))
                    if all(a < n and b < m for a, b in cells):
                        ps.append(cells)
        placements.append(set(ps))
    tot = 0
    def rec(k, used):
        nonlocal tot
        if k == len(placements): tot += 1; return
        for cells in placements[k]:
            if not (cells & used): rec(k + 1, used | cells)
    rec(0, frozenset()); return tot


# ---------------------------------------------------------------- exact sampler (Monte Carlo)
def forward_store(n, m, pieces, allow_empty):
    """float32 forward DP, storing the complete array at every cell position.
    S[i][j] = weights of partial layouts just before cell (i,j) (row-scaled)."""
    vert = {L: w for L, w in pieces.items() if L <= n}
    base = max([L - 1 for L in vert] + [0]) + 1
    size = base ** m
    cur = np.zeros(size, dtype=np.float64); cur[0] = 1
    S = []
    for i in range(n):
        cur = cur / cur.max()
        pend = {0: cur.astype(np.float32)}
        get = lambda k: pend.setdefault(k, np.zeros(size, dtype=np.float32))
        row = []
        for j in range(m):
            A = pend.pop(j); row.append(A)
            Av = A.reshape(base ** j, base, base ** (m - 1 - j))
            Bv = get(j + 1).reshape(base ** j, base, base ** (m - 1 - j))
            for v in range(1, base): Bv[:, v - 1, :] += Av[:, v, :]
            free = Av[:, 0, :]
            if allow_empty: Bv[:, 0, :] += free
            for L, w in vert.items():
                if L <= n - i: Bv[:, L - 1, :] += w * free
            for L, w in pieces.items():
                if j + L <= m:
                    Th = get(j + L).reshape(base ** j, base ** L, base ** (m - j - L))
                    Th[:, 0, :] += w * A.reshape(base ** j, base ** L, base ** (m - j - L))[:, 0, :]
        S.append(row)
        cur = pend.pop(m).astype(np.float64)
    return S, base

def sample_layout(S, base, n, m, pieces, allow_empty, rng):
    """Draw one placement (list of (L, orientation, r, c)) with probability proportional
    to its weight (product of piece weights)."""
    vert = {L: w for L, w in pieces.items() if L <= n}
    pw = [base ** (m - 1 - k) for k in range(m)]
    s = 0                               # final profile must be all zero
    ships = []
    i, jp = n - 1, m                    # position (i, jp) = before cell (i,jp)
    while not (i == 0 and jp == 0):
        if jp == 0:
            i, jp = i - 1, m; continue
        j = jp - 1
        d = (s // pw[j]) % base
        cands = []                      # (weight, pred_j, pred_state, ship)
        if d + 1 < base:
            s2 = s + pw[j]; cands.append((float(S[i][j][s2]), j, s2, None))
        if d == 0 and allow_empty:
            cands.append((float(S[i][j][s]), j, s, None))
        for L, w in vert.items():
            if d == L - 1 and L <= n - i and d > 0:
                s2 = s - d * pw[j]
                cands.append((w * float(S[i][j][s2]), j, s2, (L, "V", i, j)))
        for L, w in pieces.items():
            j0 = jp - L
            if j0 >= 0 and all((s // pw[k]) % base == 0 for k in range(j0, jp)):
                cands.append((w * float(S[i][j0][s]), j0, s, (L, "H", i, j0)))
        tot = sum(c[0] for c in cands)
        x = rng.random() * tot
        for c in cands:
            x -= c[0]
            if x <= 0: break
        _, jp, s, sh = c
        if sh: ships.append(sh)
    assert s == 0
    return ships

def kp_labelling(ships, n, m, rng, bows=True):
    """Assign kinds (uniform among kinds of that length) and bows; return (K,part) grid
    and list of kinded ships."""
    lab = [["."] * m for _ in range(n)]
    kinded = []
    for L, o, r, c in ships:
        K = rng.choice([k for k, l in KINDS if l == L])
        cells = [(r, c + t) if o == "H" else (r + t, c) for t in range(L)]
        if bows and rng.random() < 0.5: cells = cells[::-1]
        for t, (a, b) in enumerate(cells): lab[a][b] = (K, t + 1)
        kinded.append((K, o, cells))
    return lab, kinded

def kp_multiplicity(lab, n, m):
    """Number of (placement, bow) pairs producing this (kind, part) labelling."""
    Ld = dict(KINDS)
    used = [[lab[r][c] == "." for c in range(m)] for r in range(n)]
    def rec(pos):
        while pos < n * m and used[pos // m][pos % m]: pos += 1
        if pos == n * m: return 1
        r, c = divmod(pos, m)
        K, t = lab[r][c]; L = Ld[K]
        tot = 0
        for o in "HV":
            cells = [(r, c + u) if o == "H" else (r + u, c) for u in range(L)]
            if not all(a < n and b < m and not used[a][b] and lab[a][b][0] == K for a, b in cells):
                continue
            parts = [lab[a][b][1] for a, b in cells]
            for want in (list(range(1, L + 1)), list(range(L, 0, -1))):
                if parts == want:
                    for a, b in cells: used[a][b] = True
                    tot += rec(pos + 1)
                    for a, b in cells: used[a][b] = False
        return tot
    return rec(0)

def violates_C(kinded):
    starts = {(K, o, min(cells)) for K, o, cells in kinded}
    for K, o, cells in kinded:
        r, c = max(cells)
        nxt = (r, c + 1) if o == "H" else (r + 1, c)
        if (K, o, nxt) in starts: return True
    return False

def monte_carlo(n, m, nsamp, seed=1):
    """Returns (mean of 1/multiplicity under A-distribution, stderr,
                fraction of B-distribution layouts satisfying C, stderr)."""
    import random
    rng = random.Random(seed)
    out = {}
    for variant in ("A", "B"):
        pieces = pieces_for(variant)
        S, base = forward_store(n, m, pieces, True)
        vals = []
        for _ in range(nsamp):
            ships = sample_layout(S, base, n, m, pieces, True, rng)
            if variant == "A":
                lab, _ = kp_labelling(ships, n, m, rng, bows=True)
                vals.append(1.0 / kp_multiplicity(lab, n, m))
            else:
                _, kinded = kp_labelling(ships, n, m, rng, bows=False)
                vals.append(0.0 if violates_C(kinded) else 1.0)
        del S
        v = np.array(vals)
        out[variant] = (v.mean(), v.std(ddof=1) / math.sqrt(len(v)))
    return out

# ---------------------------------------------------------------- main
def lg(x): return math.log2(x) if x > 0 else float("-inf")

def fmt(x):
    return f"{x}"

def run_mc(N=10, NS=100000):
    """Monte Carlo stage (separate process: needs ~4 GB for the stored float32 DP)."""
    A = int(json.load(open("results_exact.json"))["exact"]["A"])
    B = int(json.load(open("results_exact.json"))["exact"]["B"])
    print(f"== Monte Carlo on {N}x{N} (exact sampler, {NS} samples per distribution) ==", flush=True)
    mc = monte_carlo(N, N, NS, seed=12345)
    print(f"  E_A[1/multiplicity of (kind,part) labelling] = {mc['A'][0]:.5f} +- {mc['A'][1]:.5f}", flush=True)
    print(f"  P_B[layout satisfies C]                     = {mc['B'][0]:.5f} +- {mc['B'][1]:.5f}", flush=True)
    kpl = lg(A) + math.log2(mc["A"][0]); kpe = mc["A"][1] / mc["A"][0] / math.log(2)
    cl = lg(B) + math.log2(mc["B"][0]); ce = mc["B"][1] / mc["B"][0] / math.log(2)
    print(f"  => log2 #(kind,part)-labellings ~ {kpl:.4f} +- {kpe:.4f};  log2 C ~ {cl:.4f} +- {ce:.4f}", flush=True)
    json.dump({"nsamp": NS, "inv_mult": mc["A"], "C_frac": mc["B"], "log2_KP_labellings": [kpl, kpe],
               "log2_C": [cl, ce]}, open("results_mc.json", "w"), indent=1, default=float)

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "mc":
    run_mc()
elif __name__ == "__main__":
    # usage: python3 free_fleet_count.py        -> exact stage, then MC stage in a fresh process
    #        python3 free_fleet_count.py mc     -> MC stage only (needs results_exact.json)
    N = 10
    out = {"grid": N}
    T0 = time.time()
    print("== brute-force sanity checks ==", flush=True)
    checks = []
    for (n, m) in [(1, 2), (2, 1), (2, 2), (1, 5), (2, 3), (3, 2), (1, 7), (1, 10), (3, 3), (2, 5), (2, 6), (3, 4), (4, 4)]:
        bf = brute(n, m)
        for v in ["A", "B", "C", "D", "DA"]:
            d1 = dict_count(n, m, v)
            d2 = exact_count(n, m, v, procs=1, verbose=False)
            assert bf[v] == d1 == d2, (n, m, v, bf[v], d1, d2)
        checks.append({"grid": f"{n}x{m}", **bf})
        print(f"  {n}x{m}: {bf}  (dict DP and numpy DP agree)", flush=True)
    out["checks"] = checks
    for (n, m) in [(5, 5), (6, 4), (4, 7)]:
        for v in ["A", "B", "C", "D"]:
            assert dict_count(n, m, v) == exact_count(n, m, v, procs=1, verbose=False)
    print("  numpy DP == big-int dict DP on 5x5, 6x4, 4x7 (A,B,C,D)", flush=True)
    std_checks = []
    for (n, m, ks) in [(4, 4, KINDS[:3]), (5, 5, KINDS[:4]), (5, 6, KINDS)]:
        a = brute_standard_small(n, m, ks)
        b = dp_dict(n, m, [(L, 1, 1 << q) for q, (K, L) in enumerate(ks)], True, need_mask=(1 << len(ks)) - 1)
        assert a == b; std_checks.append((f"{n}x{m}", [k for k, _ in ks], a))
    print("  standard-fleet DP == brute force on", std_checks, flush=True)

    print(f"== {N}x{N} exact counts ==", flush=True)
    res = {}
    for v in ["A", "B", "D", "DA"]:
        res[v] = exact_count(N, N, v, procs=4)
        print(f"  {v} = {res[v]}   log2 = {lg(res[v]):.6f}", flush=True)
    res["STD"] = standard_fleet(N, N)
    print(f"  standard fleet (one of each kind, no bow) = {res['STD']}  log2={lg(res['STD']):.6f}", flush=True)

    print("== variant C: exact on small squares, 10 x w strips ==", flush=True)
    Csq = {}
    for k in range(2, 8):
        Csq[k] = (exact_count(k, k, "C", procs=4, verbose=False), exact_count(k, k, "B", procs=4, verbose=False))
        print(f"  {k}x{k}: C={Csq[k][0]}  B={Csq[k][1]}  C/B={Csq[k][0]/Csq[k][1]:.6f}", flush=True)
    strip = {}
    for w in range(1, 9):
        if w <= 7:
            c = lg(exact_count(N, w, "C", procs=2, verbose=False)); b = lg(exact_count(N, w, "B", procs=4, verbose=False))
        else:
            c = dp_numpy(N, w, pieces_for("C"), True, as_float=True)
            b = dp_numpy(N, w, pieces_for("B"), True, as_float=True)
        strip[w] = (c, b)
        print(f"  10x{w}: log2 C={c:.6f} log2 B={b:.6f}", flush=True)
    def extrap(vals):     # vals[w] for w=1..8 -> estimate at w=10 (Aitken on increments)
        d = {w: vals[w] - vals[w - 1] for w in range(2, 9)}
        d6, d7, d8 = d[6], d[7], d[8]
        q = (d8 - d7) / (d7 - d6) if d7 != d6 else 0.0
        dinf = d8 + (d8 - d7) * q / (1 - q) if abs(q) < 1 else d8
        # sum of the next two increments assuming geometric convergence
        inc9 = dinf + (d8 - dinf) * q; inc10 = dinf + (d8 - dinf) * q * q
        return vals[8] + inc9 + inc10, vals[8] + 2 * d8
    cE, cN = extrap({w: strip[w][0] for w in strip})
    bE, bN = extrap({w: strip[w][1] for w in strip})
    print(f"  strip extrapolation: log2 C(10x10) ~ {cE:.4f} (naive {cN:.4f}); same method on B gives {bE:.4f} (naive {bN:.4f}) vs exact {lg(res['B']):.4f}", flush=True)

    out.update({
        "exact": {k: str(v) for k, v in res.items()},
        "log2": {k: lg(v) for k, v in res.items()},
        "C_squares": {f"{k}x{k}": [str(a), str(b)] for k, (a, b) in Csq.items()},
        "C_strips_log2": strip, "C_strip_extrap": [cE, cN, bE, bN],
        "runtime_s": time.time() - T0,
    })
    json.dump(out, open("results_exact.json", "w"), indent=1, default=float)
    print("exact stage done", time.time() - T0, flush=True)
    import subprocess
    subprocess.run([sys.executable, __file__, "mc"], check=True)
