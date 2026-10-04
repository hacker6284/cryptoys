#!/usr/bin/env python3
"""Key-limited pegs-only cell counts per tier (Zachary's choice at Serious: 162 cells, "128-bit, key-limited").
For m cells of i.i.d. uniform {empty, white, red} (the all-empty key re-rolled):
  * H_inf(k) = log2(3^m - 1) EXACTLY when m <= n - 3 (Lemma A; exact threshold n - 3 per the 2026-09-30 review).
  * plain BSGS on the key set: 3^floor(m/2) + 3^ceil(m/2) group operations (a concrete attack: an UPPER bound
    on what the attacker needs); with the negation map a factor sqrt(2) less.
  * Frobenius rotation model: c(k) = #{i in Z/n : supp(k) + i inside the window}; E[c] computed exactly here as
    sum_i (3^{|W cap (W - i)|} - 1) / (3^m - 1); saving <= sqrt(E[c])  ("modelled best key search").
  * GGM floor with free +-Frobenius: 2^((H_inf - log2(2n))/2)  (review Q1; a model bound, not an attack).
  * rho on the curve: sqrt(pi l / (4n)) (C3).
"Key-limited" here = the concrete plain-BSGS count is below rho (so the key, not the curve, is the weak link
even for an attacker who uses no negation/Frobenius tricks at all).
Also: pegs-only walks never meet the exceptional case (v empty) for m <= n - 3 -- checked exhaustively at Demo."""
import math, json, sys
sys.dont_write_bytecode = True
import os as _os, sys as _sys; _sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'oracle'))  # PARI oracle
from ecbs_oracle import TIERS, Ref, Tier

def lg(x): return math.log2(x)
def Ec(n, m):
    W = range(m); tot = 0
    for i in range(n):
        inter = sum(1 for e in W if (e + i) % n < m)
        tot += 3 ** inter - 1
    return tot / (3 ** m - 1)
def row(name, n, l, m):
    H = lg(3 ** m - 1); bs = lg(3 ** (m // 2) + 3 ** (-(-m // 2))); ec = Ec(n, m)
    rho = 0.5 * lg(math.pi * l / (4 * n))
    return dict(m=m, H=H, exact=m <= n - 3, bsgs=bs, bsgs_neg=bs - 0.5, Ec=ec, modelled=bs - 0.5 - 0.5 * lg(ec),
                ggm=(H - lg(2 * n)) / 2, rho=rho, key_limited=bs < rho)

def demo_exceptional(m):
    """every nonzero pegs-only key of m cells at Demo: does any addition step have lam*s = +-1 (mod l)?"""
    T = Tier("Demo"); l, lam = T.l, T.lam; bad = 0; tot = 0
    for idx in range(1, 3 ** m):
        d = []; t = idx
        for _ in range(m): d.append((0, 1, -1)[t % 3]); t //= 3
        s = None
        for c in d:
            if s is not None: s = s * lam % l
            if c == 0: continue
            if s is None or s == 0: s = c % l; continue
            if s in (1, l - 1): bad += 1; break          # s*P = +-P before adding +-P  (s already includes the Frobenius)
            s = (s + c) % l
        tot += 1
    return tot, bad

def main():
    out = {}
    cand = {"Demo": [2, 3, 4], "Toy": [15, 16, 17, 18, 20], "Hobby": [50, 51, 52, 53, 56], "Serious": [161, 162, 170, 171, 172, 173, 176]}
    for name, (n, k, _) in TIERS.items():
        l = Ref(n, k).l
        print(f"{name} (n = {n}, log2 l = {lg(l):.2f}, n-3 = {n-3}):")
        for m in cand[name]:
            r = row(name, n, l, m); out[f"{name}_{m}"] = r
            print(f"  m = {m:3d}: H_inf = {r['H']:.2f}{' (exact)' if r['exact'] else ' (NOT exact)'}; plain BSGS 2^{r['bsgs']:.2f}, "
                  f"with negation 2^{r['bsgs_neg']:.2f}; E[c] = {r['Ec']:.3f} -> modelled 2^{r['modelled']:.2f}; GGM floor 2^{r['ggm']:.2f}; "
                  f"rho 2^{r['rho']:.2f}; key-limited (plain BSGS < rho): {r['key_limited']} (margin {r['rho'] - r['bsgs']:+.2f})")
    print("Demo exhaustive exceptional-case check (pegs-only, chord or projective walk):")
    for m in (2, 3, 4):
        tot, bad = demo_exceptional(m); out[f"demo_exc_{m}"] = (tot, bad)
        print(f"  m = {m}: {tot} nonzero keys, {bad} meet lam*s = +-1 at an addition")
    json.dump(out, open("ecbs_tiers.json", "w"), indent=1)

if __name__ == "__main__": main()
