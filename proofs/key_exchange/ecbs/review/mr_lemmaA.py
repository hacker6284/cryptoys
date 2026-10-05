#!/usr/bin/env python3
"""mr_lemmaA.py -- Mathematician review of Lemma A (C4/C5) and an EXACT injectivity threshold.

Fact used (proved in REVIEW.md, Q2): for d in Z^m (m <= n), sum d_e lambda^e = 0 (mod l)  iff
alpha := sum d_e tau^e lies in the prime ideal  I = (l, tau - lambda)  of Z[tau] = O_K.
If alpha = 0 and |d_e| <= 2 then d = 0 (lowest coefficient argument).  So the pegs-only walk on
m cells is injective  iff  no NONZERO alpha in I has a tau-adic expansion of length <= m with digits
in [-2, 2].  Every such alpha has |alpha| <= B_m := 2 sum_{e<m} 3^(e/2), so it suffices to
(1) enumerate every alpha in I with N(alpha) <= B_n^2 (a 2-D lattice, a handful of points), and
(2) for each, compute the minimal length of a [-2,2]-digit expansion by breadth-first search with
    exact norm pruning (complete).  m* = min length; injective iff m < m*.
Cross-checks: brute force at Demo; meet-in-the-middle at Toy.
Run: python mr_lemmaA.py"""
import math, itertools, sys
from sympy.ntheory import sqrt_mod
import numpy as np
TIERS = {"Demo": 7, "Toy": 23, "Hobby": 59, "Serious": 179}
def V(n, t=-1, q=3):
    a, b = 2, t
    for _ in range(n - 1): a, b = b, t * b - q * a
    return b
def ell(n): return (3 ** n + 1 - V(n)) // 5
def lam_of(n):
    l = ell(n)
    rts = [((-1 + s) * pow(2, -1, l)) % l for s in sqrt_mod(-11 % l, l, all_roots=True)]
    g = [x for x in rts if pow(x, n, l) == 1]; assert len(g) == 1
    return g[0]
def N(a, b): return a * a - a * b + 3 * b * b
def B_parts(D, m):        # B = D sum_{e<m} 3^(e/2) = A + C sqrt3
    A = sum(D * 3 ** (e // 2) for e in range(m) if e % 2 == 0)
    C = sum(D * 3 ** (e // 2) for e in range(m) if e % 2 == 1)
    return A, C
def norm_le_B2(nv, A, C):  # exact test nv <= (A + C sqrt3)^2
    lhs = nv - A * A - 3 * C * C
    return lhs <= 0 or lhs * lhs <= 12 * A * A * C * C
def B2_lt(l, A, C):        # (A + C sqrt3)^2 < l
    rhs = l - A * A - 3 * C * C
    return rhs > 0 and 12 * A * A * C * C < rhs * rhs

def lattice_points(l, lam, A, C):
    """all (a,b) != 0 with a + b*lam = 0 mod l and N(a,b) <= (A + C sqrt3)^2."""
    # basis w1 = (l, 0), w2 = (-lam, 1); Gauss-reduce w.r.t. the form N
    def ip(u, v):   # bilinear form with N(u) = ip(u,u): N(a,b) = a^2 - ab + 3b^2
        return u[0] * v[0] - (u[0] * v[1] + u[1] * v[0]) / 2 + 3 * u[1] * v[1]
    w1, w2 = (l, 0), (-lam, 1)
    while True:
        if N(*w1) > N(*w2): w1, w2 = w2, w1
        # mu = round(<w1,w2>/<w1,w1>) using exact rationals
        num = 2 * w1[0] * w2[0] - (w1[0] * w2[1] + w1[1] * w2[0]) + 6 * w1[1] * w2[1]
        den = 2 * N(*w1)
        mu = (2 * num + den) // (2 * den)
        if mu == 0: break
        w2 = (w2[0] - mu * w1[0], w2[1] - mu * w1[1])
    # enumerate x w1 + y w2 ; form Q(x,y) = a x^2 + b xy + c y^2
    a = N(*w1); c = N(*w2); b = N(w1[0] + w2[0], w1[1] + w2[1]) - a - c
    R2 = (A + C * math.sqrt(3)) ** 2 * (1 + 1e-9) + 10
    disc = 4 * a * c - b * b
    ymax = int(math.isqrt(int(4 * a * R2 // disc) + 1)) + 2
    out = []
    for y in range(-ymax, ymax + 1):
        # a x^2 + b y x + c y^2 <= R2
        dd = b * b * y * y - 4 * a * (c * y * y - R2)
        if dd < 0: continue
        s = math.sqrt(dd)
        x0 = int(math.floor((-b * y - s) / (2 * a))) - 1; x1 = int(math.ceil((-b * y + s) / (2 * a))) + 1
        for x in range(x0, x1 + 1):
            p = (x * w1[0] + y * w2[0], x * w1[1] + y * w2[1])
            if p == (0, 0): continue
            if norm_le_B2(N(*p), A, C): out.append(p)
    return out

def min_len(alpha, D, mmax, Bcache):
    """minimal L such that alpha = sum_{e<L} d_e tau^e with |d_e| <= D (None if > mmax); also returns digits."""
    layer = {alpha: []}
    for k in range(mmax + 1):
        if (0, 0) in layer: return k, layer[(0, 0)]
        if k == mmax: return None, None
        rem = mmax - k - 1
        A, C = Bcache[rem]
        new = {}
        for (a, b), digs in layer.items():
            for d in range(-D, D + 1):
                if (a - d) % 3: continue
                t = (a - d) // 3
                nb = (b - t, -t)                       # ((a-d) + b tau)/tau
                if nb in new: continue
                if nb != (0, 0) and not norm_le_B2(N(*nb), A, C): continue
                new[nb] = digs + [d]
        layer = new
    return None, None

def threshold(n, D=2, verbose=True):
    l = ell(n); lam = lam_of(n)
    Bcache = [B_parts(D, r) for r in range(n + 1)]
    A, C = Bcache[n]
    pts = lattice_points(l, lam, A, C)
    best = (None, None, None)
    for p in pts:
        L, digs = min_len(p, D, n, Bcache)
        if L is not None and (best[0] is None or L < best[0]): best = (L, digs, p)
    norm_ok = max(m for m in range(n + 1) if B2_lt(l, *Bcache[m]))
    L, digs, p = best
    if digs is not None:
        chk = sum(d * pow(lam, e, l) for e, d in enumerate(digs)) % l
        assert chk == 0, "found relation does not vanish"
    return dict(n=n, l=l, lam=lam, D=D, n_lattice_pts=len(pts), norm_bound_m=norm_ok, mstar=L, digits=digs, alpha=p,
                alpha_norm_over_l=(N(*p) / l) if p else None)

def brute_demo():
    n = 7; l = ell(n); lam = lam_of(n); res = {}
    for m in range(1, n + 1):
        vals = set(); coll = False
        for c in itertools.product((-1, 0, 1), repeat=m):
            k = sum(ci * pow(lam, e, l) for e, ci in enumerate(c)) % l
            if k in vals: coll = True; break
            vals.add(k)
        res[m] = not coll
    return res

def mitm_toy(m):
    """exact: is there a nonzero d in [-2,2]^m with sum d_e lam^e = 0 mod l (Toy)?"""
    n = 23; l = ell(n); lam = lam_of(n)
    h = m // 2
    def sums(lo, hi):
        pw = np.array([pow(lam, e, l) for e in range(lo, hi)], dtype=object)
        acc = np.zeros(1, dtype=np.int64)
        for p in pw:
            p = int(p)
            acc = (acc[:, None] + np.array([(d * p) % l for d in range(-2, 3)], dtype=np.int64)[None, :]).reshape(-1) % l
        return acc
    Lo = sums(0, h); Hi = (-sums(h, m)) % l
    Lo_s = np.sort(Lo); Hi_s = np.sort(Hi)
    common = np.intersect1d(Lo_s, Hi_s)
    # the zero vector gives the common value 0 once on each side; any other coincidence is a relation
    nz = len(common) > 1 or (len(common) == 1 and (np.count_nonzero(Lo == common[0]) > 1 or np.count_nonzero(Hi == common[0]) > 1))
    if len(common) == 1 and common[0] != 0: nz = True
    return nz

def main():
    print("== Lemma A exact injectivity thresholds (pegs-only windows, digit differences in [-2,2])")
    out = {}
    for name, n in TIERS.items():
        r = threshold(n, 2); out[name] = r
        ms = r['mstar']
        print(f"{name:8s} n={n:3d}: lattice points of I with N <= B_n^2: {r['n_lattice_pts']}; norm certificate (C5) gives m <= {r['norm_bound_m']}; "
              f"EXACT: first relation at length m* = {ms}  => pegs-only injective (H_inf = m log2 3 exactly) iff m <= {ms - 1}")
        print(f"          shortest relation alpha = {r['alpha'][0]} + {r['alpha'][1]} tau, N(alpha)/l = {r['alpha_norm_over_l']:.0f}; digits (e=0 first) = {''.join('%+d' % d if d else '0' for d in r['digits'])}")
        print(f"          => H_inf(m = {ms - 1}) = {(ms - 1) * math.log2(3):.2f} bits exact; m = {ms}: H_inf <= {ms * math.log2(3) - 1:.2f} (a collision exists) and >= {(ms - 1) * math.log2(3):.2f}")
    print("\n== Same with |d| <= 1 (sign-only differences, e.g. halved sign sums)")
    for name, n in TIERS.items():
        r = threshold(n, 1)
        print(f"{name:8s}: norm certificate m <= {r['norm_bound_m']}; exact first relation at m* = {r['mstar']}")
    print("\n== Cross-check 1: Demo brute force (is the m-trit walk injective?)")
    bd = brute_demo(); print("   ", bd, " -> largest injective m =", max(m for m, v in bd.items() if v))
    print("== Cross-check 2: Toy meet-in-the-middle over d in [-2,2]^m")
    for m in (out['Toy']['mstar'] - 1, out['Toy']['mstar']):
        print(f"   m = {m}: nonzero relation exists: {mitm_toy(m)}")

if __name__ == "__main__": main()
