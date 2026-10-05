#!/usr/bin/env python3
"""The x-register 'hash' as a hand recipe: a FOLD (drop rows onto rows, same column), i.e. the
F_3-linear surjection  L_m : F_3^n -> F_3^m,  z_j = sum of x_i over i = j (mod m).
This is a (deterministic, seedless) randomness EXTRACTOR for the x-coordinate of a point that is uniform
on <P> minus O -- NOT a random oracle.  Analysis:
  * XOR lemma (F_3 version):  SD(Z, U_m) <= 1/2 sqrt(sum_{a != 0} |E w^{a.Z}|^2) <= 1/2 sqrt(3^m - 1) * delta,
    delta = max_{c != 0} |(1/(l-1)) sum_{R in <P>, R != O} psi(Tr(c x(R)))|.
  * Constant KS_C = 3 (updated 2026-09-30): for any subgroup H, |sum_{R in H, R != O} psi(c x(R))| <= 3 sqrt(q)
    [Mathematician's review Q11a: Weil II + Grothendieck-Ogg-Shafarevich, Swan conductor 2 at O; not re-derived here].
    The older [lit] Kohel-Shparlinski form 2 deg(f) sqrt(q) = 4 sqrt(q) is weaker.  So delta <= 3 sqrt(q)/(l-1).  Checked here EMPIRICALLY (full spectrum) for the same curve over
    GF(3^7), GF(3^11), GF(3^13), subgroup of prime order.
  * fibre bound (exact, elementary): Pr[Z = z] <= 2 * 3^(n-m) / (l-1)  (3^(n-m) x-values per output, <= 2 points each).
Exact at Demo; Monte-Carlo bias test at Toy; bounds at every tier."""
import json, math, random
import numpy as np
import os as _os, sys as _sys; _sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'oracle'))  # PARI oracle
from ecbs_oracle import TIERS, pari, Tier, fold_mod
KS_C = 3
from mpmath import mp, mpf, log, sqrt
mp.dps = 60

def walsh_max(counts, n):
    """max over nonzero a of |sum_x counts[x] w^{a.x}|, counts indexed by base-3 digits (digit j = coeff of w^j)."""
    A = np.asarray(counts, dtype=np.complex128).reshape((3,) * n, order='F')
    for ax in range(n): A = np.fft.fft(A, axis=ax)
    mag = np.abs(A).ravel(order='F'); mag[0] = 0
    return float(mag.max())

def subgroup_x_hist(n):
    """same curve y^2 = x^3 - x^2 + 1 over GF(3^n) (field from ffinit); histogram of x over the prime-order
       subgroup minus O (largest prime factor of #E), computed in GP."""
    gp = pari
    from ecbs_oracle import V
    N = 3 ** n + 1 - V(n); fa = pari.factor(N); l = int(fa[0][len(fa[0]) - 1]); h = N // l
    res = pari(f"""
      my(w = ffgen(ffinit(3, {n}), 'w), E = ellinit([0,2,0,0,1], w), c = vector(3^{n}), f = vector(3^{n}), tot = 0, q = 3^{n});
      for(i = 0, q - 1,
        my(x = subst(Pol(digits(i, 3)), 'x, w) + 0*w, r = x^3 + 2*x^2 + 1);
        if(r == 0, my(P = [x, 0*w]); f[i+1]++; if(ellmul(E, P, {l}) == [0], c[i+1]++; tot++),
          if(issquare(r), my(y = sqrt(r));
            for(s = 0, 1, my(P = [x, if(s, -y, y)]); f[i+1]++; if(ellmul(E, P, {l}) == [0], c[i+1]++; tot++)))));
      [c, tot, f]""")
    counts = [int(v) for v in res[0]]; tot = int(res[1]); full = [int(v) for v in res[2]]
    assert tot == l - 1, (tot, l)
    return counts, l, N, full

def bounds(n, l, m):
    q = mpf(3) ** n
    delta = KS_C * sqrt(q) / (l - 1)
    sd = mpf(1) / 2 * sqrt(mpf(3) ** m - 1) * delta
    fib = 2 * mpf(3) ** (n - m) / (l - 1)
    four = mpf(3) ** (-m) + delta
    pmax = min(fib, four)
    return dict(delta_log2=float(log(delta, 2)), sd_log2=float(log(sd, 2)) if sd > 0 else None,
                hmin_lower=float(-log(pmax, 2)), hmin_upper=float(m * log(3, 2)),
                trit_sd_log2=float(log(mpf(1) / 2 * sqrt(2) * delta, 2)))

def fold(xreg, m):
    """the SPEC 6 fold to m holes (the oracle's fold_mod), as a list of '.WR' characters."""
    return list(fold_mod(''.join(xreg), m))

RECIPES = {  # (m, spoken recipe on the lane layout)
    "Demo": [(4, "2-wide lane: drop rows C-D onto rows A-B"), (2, "then drop row B onto row A")],
    "Toy": [(16, "8-wide lane: drop row C onto row A"), (8, "drop rows B and C onto row A")],
    "Hobby": [(40, "20-wide double grid: drop row C onto row A"), (20, "drop rows B and C onto row A")],
    "Serious": [(100, "20-wide double grid: drop rows F-I onto rows A-D (keep rows A-E)"),
                (80, "then also drop row E onto row A (keep rows A-D)"),
                (60, "or drop rows D-I onto rows A-C in turn (keep rows A-C)")]}

def main():
    out = {}
    print("== 1. Demo exact (all 420 points of <P> minus O)")
    T = Tier("Demo"); R = T.R; l = T.l; n = 7
    pts = []; Q = T.Pref
    for k in range(1, l):
        pts.append(R.unpt(R.mul(k, T.Pref))[0])
    idx = lambda xr: sum('.WR'.index(c) * 3 ** j for j, c in enumerate(xr))
    counts = [0] * 3 ** n
    for xr in pts: counts[idx(xr)] += 1
    wm = walsh_max(counts, n); q = 3 ** n
    print(f"  max |character sum| over all 2186 nonzero functionals = {wm:.2f} = {wm/math.sqrt(q):.3f} sqrt(q)  (bound 3 sqrt(q) = {3*math.sqrt(q):.1f})")
    out['demo_walsh'] = dict(max=wm, ratio=wm / math.sqrt(q))
    for m in range(1, 8):
        dist = {}
        for xr in pts:
            z = ''.join(fold(xr, m)); dist[z] = dist.get(z, 0) + 1
        probs = [dist.get(z, 0) / (l - 1) for z in (np.base_repr(i, 3).zfill(m) for i in range(3 ** m))]
        sd = 0.5 * sum(abs(p - 3 ** -m) for p in [dist.get(z, 0) / (l - 1) for z in dist] ) + 0.5 * (3 ** m - len(dist)) * 3 ** -m
        hmin = -math.log2(max(dist.values()) / (l - 1))
        b = bounds(n, l, m)
        print(f"  m={m}: exact SD from uniform = {sd:.4f} (bound 2^{b['sd_log2']:.2f}); exact H_inf = {hmin:.3f} bits "
              f"(lower bound {b['hmin_lower']:.3f}, max {m*math.log2(3):.3f})")
        out.setdefault('demo_fold', {})[m] = dict(sd=sd, hmin=hmin, bound=b)
    print("\n== 2. Character-sum constant (bound 3 sqrt(q)), empirical: full character spectrum of prime-order subgroups")
    for nn in (7, 11, 13):
        counts, ll, N, full = subgroup_x_hist(nn)
        q = 3 ** nn; wm = walsh_max(counts, nn); wf = walsh_max(full, nn)
        triv = (ll - 1) <= KS_C * math.sqrt(q)
        print(f"  GF(3^{nn}): #E = {N} = {N // ll} * {ll}; subgroup of order {ll}: max |sum| = {wm:.1f} = {wm/math.sqrt(q):.3f} sqrt(q)"
              f"{' (trivially below 3 sqrt(q): the subgroup is smaller than 3 sqrt(q))' if triv else ''}; "
              f"whole group: max |sum| = {wf:.1f} = {wf/math.sqrt(q):.3f} sqrt(q)", flush=True)
        out.setdefault('ks_empirical', {})[nn] = dict(l=ll, cof=N // ll, max=wm, ratio=wm / math.sqrt(q), trivial=triv,
                                                      full_max=wf, full_ratio=wf / math.sqrt(q))
    print("\n== 3. Bounds per tier, for K uniform on <P> minus O  [model; see review C19]")
    for name, (n, k) in TIERS.items():
        T = Tier(name); l = T.l
        b = bounds(n, l, n)
        print(f"  {name}: no fold (m = n = {n}): H_inf(x) = log2((l-1)/2) = {math.log2((l-1)/2):.2f} bits exactly; per-trit SD <= 2^{b['trit_sd_log2']:.1f}")
        for m, txt in RECIPES[name]:
            b = bounds(n, l, m)
            print(f"    m = {m:3d} trits ({m*math.log2(3):6.1f} bits max) [{txt}]: SD <= 2^{b['sd_log2']:.1f}; H_inf >= {b['hmin_lower']:.1f} bits")
            out.setdefault('tiers', {}).setdefault(name, {})[m] = b
        # the m that gives SD <= 2^-64 and 2^-128
        for tgt in (-40, -64, -128):
            best = max([m for m in range(1, n + 1) if bounds(n, l, m)['sd_log2'] <= tgt], default=None)
            print(f"    largest m with SD bound <= 2^{tgt}: {best}" + (f" ({best*math.log2(3):.1f} bits)" if best else ""))
            out['tiers'][name][f"m_for_{tgt}"] = best
    print("\n== 4. Toy Monte-Carlo bias test (200,000 uniform K = kP), m = 5 fold (i mod 5)")
    T = Tier("Toy"); R = T.R; rnd = random.Random(99); N = 200000; cnt = {}; tri = np.zeros((5, 3))
    for _ in range(N):
        xr = R.unpt(R.mul(rnd.randrange(1, T.l), T.Pref))[0]
        z = fold(xr, 5); key = ''.join(z); cnt[key] = cnt.get(key, 0) + 1
        for j, c in enumerate(z): tri[j, '.WR'.index(c)] += 1
    exp = N / 243; chi = sum((cnt.get(np.base_repr(i, 3).zfill(5).replace('0', '.').replace('1', 'W').replace('2', 'R'), 0) - exp) ** 2 / exp for i in range(243))
    import mpmath
    p = float(mpmath.gammainc(121, chi / 2, mpmath.inf, regularized=True))
    dev = np.abs(tri / N - 1 / 3).max()
    print(f"  chi-square over 243 outputs = {chi:.1f} (df 242, p = {p:.3f}); max per-trit deviation from 1/3 = {dev:.4f} (1/sqrt(N) = {1/math.sqrt(N):.4f})")
    out['toy_mc'] = dict(N=N, chi2=chi, p=p, max_trit_dev=dev)
    json.dump(out, open("ecbs_extractor.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
