#!/usr/bin/env python3
"""ECBS key-encoding entropy after Frobenius aliasing (min-entropy of the scalar k mod l).

Model: walking M cells with one Frobenius per cell puts cell j's digit on tau^(M-1-j); on <P>
tau acts as lambda with lambda^n = 1, so k = sum_r c_r lambda^r (mod l), c_r = sum of the digits
that land on residue r = exponent mod n.

LEMMA A (certificate, proof in ECBS_MATH_REVIEW.md): let d_r be a digit-sum difference supported on
a residue set W, |d_r| <= D_r.  Rotate: position p_r = (r + s) mod n.  If B = sum D_r 3^(p_r/2)
satisfies B^2 < l and no nonzero Q in Z[x] makes (x^2+x+3)Q(x) have coefficients bounded by D at
those positions (checked by the DP below), then sum d_r lambda^r = 0 (mod l) forces d = 0.
COROLLARY: with the c_r independent, H_inf(k) >= sum_{r in W} H_inf(c_r)   (condition on the rest).
UPPER BOUNDS: an explicit key kappa with Pr[k = kappa] >= 2^-U proves H_inf(k) <= U.
"""
import math, random, json, sys, itertools, functools
from math import comb, log2
from ecbs_ref import TIERS, V
import ecbs_keys as K

LOG3 = log2(3)
def ell(n): return (3 ** n + 1 - V(n)) // 5

# ------------------------------------------------------------------ Lemma A machinery
def B2_less_than_l(D_at_pos, l):
    """exact test of (sum_p D_p 3^(p/2))^2 < l.  D_at_pos: dict position -> bound."""
    A = sum(d * 3 ** (p // 2) for p, d in D_at_pos.items() if p % 2 == 0)
    C = sum(d * 3 ** (p // 2) for p, d in D_at_pos.items() if p % 2 == 1)
    rhs = l - A * A - 3 * C * C
    return rhs > 0 and 12 * A * A * C * C < rhs * rhs

def dp_no_multiple(D_at_pos):
    """True iff no nonzero Q in Z[x] has (x^2+x+3)Q with |coef_p| <= D_p (0 where unspecified)."""
    if not D_at_pos: return True
    top = max(D_at_pos); Qm = max(D_at_pos.values())
    states = {(0, 0, False)}
    for p in range(top + 3):
        Dp = D_at_pos.get(p, 0); new = set()
        for a, b, nz in states:
            lo = -((Dp + a + b) // 3); hi = (Dp - a - b) // 3
            for q in range(max(lo, -Qm), min(hi, Qm) + 1):
                new.add((q, a, nz or q != 0))
        states = new
    return not any(a == 0 and b == 0 and nz for a, b, nz in states)

def certify(D_by_res, n, l, s):
    pos = {(r + s) % n: d for r, d in D_by_res.items() if d > 0}
    return B2_less_than_l(pos, l) and dp_no_multiple(pos)

def best_window(D, h, n, l, need_dp=True):
    """D[r], h[r]: difference bound and min-entropy of digit sum at residue r.
       Tries every rotation s and the longest prefix of positions 0..t (all residues there included)
       that is certified; returns (best sum h, s, t)."""
    best = (0.0, None, None)
    for s in range(n):
        res_at = [None] * n
        for r in range(n): res_at[(r + s) % n] = r
        # binary search the largest t with B^2 < l, then walk down until the DP also passes
        lo, hi = -1, n - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            pos = {p: D[res_at[p]] for p in range(mid + 1) if D[res_at[p]] > 0}
            if B2_less_than_l(pos, l): lo = mid
            else: hi = mid - 1
        t = lo
        while t >= 0:
            pos = {p: D[res_at[p]] for p in range(t + 1) if D[res_at[p]] > 0}
            if not need_dp or max(pos.values(), default=0) <= 2 or dp_no_multiple(pos): break
            t -= 1
        val = sum(h[res_at[p]] for p in range(t + 1))
        if val > best[0]: best = (val, s, t)
    return best

# ------------------------------------------------------------------ fleets
SHIPS = K.SHIPS
PLM = {L: [sum(1 << c for c in pl) for pl in K.POS[L]] for L in set(SHIPS)}
NLAB = 30093975536        # re-verified by fleet_count.c (see fleet_count_results.txt)

@functools.lru_cache(maxsize=None)
def multiplicity(T):
    """number of labelled fleets (5,4,3a,3b,2) whose union is exactly the 17-cell mask T."""
    inside = {L: [m for m in PLM[L] if m & T == m] for L in PLM}
    def rec(i, rem):
        if i == len(SHIPS): return 1 if rem == 0 else 0
        return sum(rec(i + 1, rem & ~m) for m in inside[SHIPS[i]] if m & rem == m)
    return rec(0, T)

def fleet_mask(ships): return sum(1 << c for s in ships for c in s)

def mc_patterns(N, rnd):
    Ms = []
    for _ in range(N):
        Ms.append(multiplicity(fleet_mask(K.dice_fleet(rnd))))
    H = log2(NLAB) - sum(log2(m) for m in Ms) / N
    return H, max(Ms), Ms

def box_search(rows, cols):
    """every fleet confined to the rows x cols corner box; returns max multiplicity and its pattern.
       (M(T) = number of fleets with union T; all of them lie in T's bounding box.)"""
    inside = {L: [m for m, pl in zip(PLM[L], K.POS[L]) if all(c // 10 < rows and c % 10 < cols for c in pl)] for L in PLM}
    counts = {}
    def rec(i, occ):
        if i == len(SHIPS): counts[occ] = counts.get(occ, 0) + 1; return
        for m in inside[SHIPS[i]]:
            if not m & occ: rec(i + 1, occ | m)
    rec(0, 0)
    T, M = max(counts.items(), key=lambda kv: kv[1])
    return M, T, len(counts)

def show(T):
    return "\n".join("   " + "".join('#' if T >> (10 * r + c) & 1 else '.' for c in range(10)) for r in range(10))

# ------------------------------------------------------------------ residues of a layout
def residues_three_state(masks, n):
    """masks: one 100-bit mask per grid; returns m_r (ship cells per residue)."""
    G = len(masks); M = 100 * G; m = [0] * n
    for g, T in enumerate(masks):
        for p in range(100):
            if T >> p & 1: m[(M - 1 - (100 * g + p)) % n] += 1
    return m

def hsum(mr):   # min-entropy of a sum of mr independent signs
    return mr - log2(comb(mr, mr // 2)) if mr else 0.0

def sign_bound(masks, n, l):
    """H_inf(k | patterns) >= certified window of sign sums (differences are even: bound m_r)."""
    m = residues_three_state(masks, n)
    one = [1 if x else 0 for x in m]
    odd = [x if x % 2 else max(x - 1, 0) for x in m]
    return max(best_window(one, [float(x) for x in one], n, l)[0],
               best_window(odd, [hsum(x) for x in odd], n, l)[0])

def heavy_bound(masks, n, G):
    """H_inf <= -log2( prod_g M_g/NLAB * prod_r C(m_r, m_r//2)/2^m_r )."""
    m = residues_three_state(masks, n)
    return sum(log2(NLAB) - log2(multiplicity(T)) for T in masks) + sum(hsum(x) for x in m)

def anneal_heavy(n, G, rnd, steps, seeds):
    """search for fleets minimising heavy_bound (i.e. aligned, high-multiplicity fleets)."""
    best_overall = (1e9, None)
    for seed_fleets in seeds:
        fleets = [list(f) for f in seed_fleets]
        masks = [fleet_mask(f) for f in fleets]
        cur = heavy_bound(masks, n, G); best = (cur, masks[:])
        for it in range(steps):
            Tmp = 2.0 * (1 - it / steps) + 0.02
            g = rnd.randrange(G); i = rnd.randrange(5); L = SHIPS[i]
            occ = set(c for j, s in enumerate(fleets[g]) if j != i for c in s)
            cand = rnd.choice(K.POS[L])
            if occ & set(cand): continue
            old = fleets[g][i]; fleets[g][i] = cand; masks[g] = fleet_mask(fleets[g])
            new = heavy_bound(masks, n, G)
            if new <= cur or rnd.random() < math.exp((cur - new) / Tmp):
                cur = new
                if cur < best[0]: best = (cur, masks[:])
            else:
                fleets[g][i] = old; masks[g] = fleet_mask(fleets[g])
        if best[0] < best_overall[0]: best_overall = best
    return best_overall

def shift_fleet(fleet, dr, dc):
    out = []
    for s in fleet:
        cells = [(c // 10 + dr, c % 10 + dc) for c in s]
        if any(not (0 <= r < 10 and 0 <= c < 10) for r, c in cells): return None
        out.append(tuple(10 * r + c for r, c in cells))
    return out

# ------------------------------------------------------------------ main
def main():
    out = {}; rnd = random.Random(20260930)
    print("=" * 78); print("1. Fleet counts and covered-pattern multiplicities"); print("=" * 78)
    print(f"NLAB (labelled fleets, touching allowed) = {NLAB:,} = 2^{log2(NLAB):.4f}  [fleet_count.c]")
    Nmc = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    H, Mmax_mc, Ms = mc_patterns(Nmc, rnd)
    hist = {}
    for m in Ms: hist[m] = hist.get(m, 0) + 1
    print(f"Monte Carlo ({Nmc:,} dice fleets): Shannon entropy of covered pattern ~= {H:.3f} bits; "
          f"multiplicity range {min(Ms)}..{Mmax_mc}")
    print("   multiplicity histogram:", dict(sorted(hist.items())))
    boxes = [(3, 6), (6, 3), (3, 9), (9, 3), (4, 8), (8, 4), (5, 5), (4, 6), (6, 4), (3, 7), (7, 3), (5, 6), (6, 5), (4, 7), (7, 4), (3, 8), (8, 3), (2, 9), (9, 2), (2, 10), (10, 2)]
    boxres = []
    for rows, cols in boxes:
        M, T, npat = box_search(rows, cols); boxres.append((M, rows, cols, T, npat))
        print(f"   exhaustive over fleets inside a {rows}x{cols} box: {npat:,} patterns, max multiplicity {M}")
    Mbox, rr, cc, Tbox, _ = max(boxres)
    Mmax = max(Mmax_mc, Mbox)
    print(f"max multiplicity found: {Mmax}  (NOT proven to be the global max); a maximal pattern:")
    print(show(Tbox))
    out["fleet"] = dict(NLAB=NLAB, shannon_pattern=H, mc_samples=Nmc, mc_max=Mmax_mc, box_max=Mbox, hist=hist)
    Hinf_fleet = log2(NLAB) - log2(Mmax) + 17
    print(f"single-fleet min-entropy (no aliasing) = log2(NLAB/Mmax) + 17 = {Hinf_fleet:.3f} bits "
          f"(valid if Mmax={Mmax} is the true max; Shannon: {H + 17:.3f})")

    print("\n" + "=" * 78); print("2. Pegs-only: exact min-entropy via Lemma A"); print("=" * 78)
    out["pegs"] = {}
    for name, (n, k, G) in TIERS.items():
        l = ell(n); m = 0
        while m + 1 <= n and B2_less_than_l({p: 2 for p in range(m + 1)}, l): m += 1
        # D <= 2 everywhere: the lowest nonzero coefficient of any multiple of x^2+x+3 is divisible by 3,
        # so the DP is automatically satisfied; check it anyway
        assert dp_no_multiple({p: 2 for p in range(m)})
        print(f"{name:8s} n={n:3d} log2 l={log2(l):8.3f}: pegs-only walk provably injective for m <= {m} cells "
              f"-> H_inf = m log2 3 = {m * LOG3:.2f} bits at m={m}")
        out["pegs"][name] = dict(max_injective_cells=m, Hinf_at_max=m * LOG3, log2l=log2(l))
    n = 179; l = ell(n)
    for m in (162, 167, 168, 173, 175):
        print(f"   Serious pegs-only m={m}: H_inf = {m * LOG3:.2f} bits exactly (m <= 175); expected additions {2*m/3:.1f}")
    # 200 cells: residue r gets 2 trits for r in 0..20 (exponents 179..199)
    def pegs_many(Mcells, n, l, stride=1, offset=0):
        cnt = [0] * n
        for j in range(Mcells): cnt[(stride * (Mcells - 1 - j) + offset) % n] += 1
        # keep ONE peg cell free per residue and condition on every other cell: D = 2, h = log2 3
        D = [2 if c else 0 for c in cnt]
        h = [LOG3 if c else 0.0 for c in cnt]
        assert all(c <= 2 for c in cnt)
        return best_window(D, h, n, l)
    v, s, t = pegs_many(200, n, l)
    print(f"   Serious pegs-only 200 cells (2 full grids): H_inf >= {v:.2f} bits (rotation {s}, positions 0..{t}); "
          f"<= log2 l = {log2(l):.2f}")
    out["pegs"]["Serious_200"] = v
    v6, s6, t6 = pegs_many(200, n, l, stride=2, offset=1)
    print(f"   Serious six-state, peg part alone (pegs on odd exponents 1..399): H_inf >= {v6:.2f} bits "
          f"(rotation {s6}, positions 0..{t6}); the ship part is independent, so H_inf(k) >= {v6:.2f}; <= {log2(l):.2f}")
    out["six_state_lower"] = v6

    print("\n" + "=" * 78); print("3. Six-state wording check"); print("=" * 78)
    # correct: per cell  F, add peg*P, F, add ship*P   -> digit peg*tau + ship (distinct mod tau^2)
    # literal 'F, add +-P for peg, F, add phi(P) if ship' -> tau^2 Q + tau*peg + tau*ship: collapses
    digits_ok = {(pg, sh): (pg, sh) for pg in (-1, 0, 1) for sh in (0, 1)}      # (a + b tau) as (b, a)
    lit = {}
    for pg in (-1, 0, 1):
        for sh in (0, 1): lit.setdefault(pg + sh, []).append((pg, sh))
    print("   'F, +-P for peg, F, +P if ship' : digit = peg*tau + ship, 6 distinct residues mod tau^2 (checked:",
          len(set(digits_ok.values())) == 6, ")")
    print("   literal 'F, +-P for peg, F, +phi(P) if ship': digit = tau*(peg + ship); collisions:",
          {v: c for v, c in lit.items() if len(c) > 1})
    print("   'F, F, +-P for peg, +phi(P) if ship' (or add P then phi(P) after ONE F pair): digit = peg + ship*tau, OK")

    print("\n" + "=" * 78); print("4. Three-state (fleets + sign pegs): bounds after aliasing"); print("=" * 78)
    out["three"] = {}
    for name, Gs, NS in (("Toy", (1,), 400), ("Hobby", (2, 3), 300), ("Serious", (6, 7), 300)):
        n = TIERS[name][0]; l = ell(n)
        for G in Gs:
            hs = []
            for _ in range(NS):
                masks = [fleet_mask(K.dice_fleet(rnd)) for _ in range(G)]
                hs.append(sign_bound(masks, n, l))
            avg = sum(2 ** -h for h in hs) / NS
            lb = -log2(avg)
            ub_naive = G * (log2(NLAB) - log2(Mmax) + 17)
            print(f"{name} G={G}: signs-only certified bound H_inf(k) >= -log2 E_T[2^-h(T)] ~= {lb:.1f} bits "
                  f"(Monte Carlo over {NS} fleet layouts; min h seen {min(hs):.1f}, mean {sum(hs)/NS:.1f})")
            out["three"][f"{name}_G{G}"] = dict(lower_signs_mc=lb, h_min=min(hs), h_mean=sum(hs) / NS, naive=ub_naive)
    # heavy keys
    print("\n   Explicit heavy keys (rigorous UPPER bounds on H_inf):")
    heavy = {}
    # structured seed: the best box pattern, copied along the 21-offset chain (up 2 rows, left 1 col)
    n = 179
    # find a fleet realising Tbox
    def fleet_for(T):
        inside = {L: [pl for pl in K.POS[L] if all(T >> c & 1 for c in pl)] for L in PLM}
        def rec(i, rem, acc):
            if i == 5: return acc if rem == 0 else None
            for pl in inside[SHIPS[i]]:
                mm = sum(1 << c for c in pl)
                if mm & rem == mm:
                    r = rec(i + 1, rem & ~mm, acc + [pl])
                    if r: return r
            return None
        return rec(0, T, [])
    f0s = [fleet_for(T) for M_, r_, c_, T, _ in sorted(boxres, reverse=True) if r_ <= 6 and c_ <= 8][:6]
    for name, G, steps in (("Toy", 1, 20000), ("Hobby", 2, 20000), ("Serious", 6, 60000), ("Serious", 7, 60000)):
        n = TIERS[name][0]
        seeds = [[K.dice_fleet(rnd) for _ in range(G)] for _ in range(2)]
        # hand-built seeds: the box pattern copied so that grids g, g+2, g+4, ... land on the same residues
        # (grid g+2 cell p has the residue of grid g cell p+21: two rows down, one column right)
        for f0, extra in itertools.product(f0s, ((0, 0), (1, 1))):
            seed = []
            for g in range(G):
                cls = list(range(g % 2, G, 2)); i = cls.index(g); c = len(cls)
                f = shift_fleet(f0, 2 * (c - 1 - i) + extra[0], (c - 1 - i) + extra[1])
                seed.append(f if f is not None else K.dice_fleet(rnd))
            seeds.append(seed)
        U, masks = anneal_heavy(n, G, rnd, steps, seeds)
        mr = residues_three_state(masks, n)
        Mg = [multiplicity(T) for T in masks]
        print(f"   {name} G={G}: heavy key with Pr >= 2^-{U:.2f}  => H_inf <= {U:.2f} bits "
              f"(fleet multiplicities {Mg}; residue loads {dict(sorted({x: mr.count(x) for x in set(mr) if x}.items()))})")
        heavy[f"{name}_G{G}"] = dict(U=U, M=Mg, masks=[hex(T) for T in masks])
        if name == "Serious" and G == 6:
            for g, T in enumerate(masks): print(f"     grid {g}:"); print(show(T))
    out["heavy"] = heavy

    print("\n" + "=" * 78); print("5. Meet-in-the-middle / BSGS costs (group operations, generic)"); print("=" * 78)
    Hp = log2(NLAB) - sum(log2(m) for m in Ms) / len(Ms)     # log2 #patterns is <= this? report both
    npat = sum(1 / m for m in Ms) / len(Ms) * NLAB            # E[1/M] * NLAB = number of distinct patterns
    print(f"   distinct covered patterns ~= NLAB * E[1/M] = {npat:.4g} = 2^{log2(npat):.3f}")
    for G in (6, 7):
        half = (G + 1) // 2
        print(f"   three-state G={G}: split by grids ({half} vs {G - half}): table 2^{half * (log2(npat) + 17):.1f}, "
              f"time ~2^{max(half, G - half) * (log2(npat) + 17):.1f} (upper estimate; dedup of aliases only lowers it)")
    for m in (162, 175, 200):
        print(f"   pegs-only m={m}: BSGS on halves 3^{m//2}+3^{m - m//2}: ~2^{log2(3 ** (m // 2) + 3 ** (m - m // 2)):.1f}")
    print(f"   six-state G=2: split at the grid boundary: each side 3^100 * #patterns: ~2^{100 * LOG3 + log2(npat):.1f}")
    out["mitm"] = dict(npat=npat)
    json.dump(out, open("ecbs_entropy.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
