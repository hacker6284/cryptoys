#!/usr/bin/env python3
"""mr_pairs.py -- Q6: rigorous UPPER bounds on H_inf(k) for three-state keys by PAIRED (cancelling) layouts.

Walk: grid g cell p (reading order) carries tau^(M-1-100g-p); on <P> only the residue mod n matters.
Grid g cell p and grid g' cell p' share a residue iff p - p' = delta (mod n), delta = 100(g'-g).
If fleet(g) = fleet(g') translated by (dr, dc) with 10dr + dc = delta (no row wrap), every residue of
the pair holds one cell of each grid.  Sub-event E_pair: fleet(g') = T, fleet(g) = T + delta, and
each partner pair of sign pegs is opposite (prob 2^-17).  Then the pair contributes 0 to k.
  Pr[E_pair] = sum_{T fits} (M(T)/NLAB)^2 2^-17,   sum_{T fits} M(T)^2 = sum_{fleets F fitting} M(T(F))
computed EXACTLY from the S1/S2 tables of mr_fleets.c (all 3.0e10 labelled fleets enumerated).
Nonzero target: in ONE pair require a cell c0 in T and the two pegs at c0, c0+delta both white:
k = 2 lambda^(r0) != 0; Pr >= (17/|box|) * sum M^2/NLAB^2 * 2^-18 (max over c0 >= average).
7 fleets: 3 cancelling pairs + one grid with a fixed max-multiplicity pattern (M = 72) and fixed signs.
Everything is a lower bound on Pr[k = kappa] for one fixed kappa, hence an upper bound on H_inf(k).
Also: Toy (1 fleet) exact value from mr_fleets.c, and a Monte-Carlo check of the construction
(kappa is as predicted; how often the walk hits an exceptional addition, which forces a re-roll).
Run: python mr_pairs.py"""
import math, itertools, random, sys
from math import log2
sys.dont_write_bytecode = True                                # never write __pycache__ into the read-only tree
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'core'))  # import of the dice procedure only
import ecbs_keys as K
from mr_lemmaA import ell, lam_of

def load():
    S1 = {}; S2 = {}; NL = None; toy = {}; maxM = None
    for line in open('mr_fleets_results.txt'):
        f = line.split()
        if f[0] == 'NLAB': NL = int(f[1])
        elif f[0] == 'maxM': maxM = int(f[1])
        elif f[0] == 'S': S1[(int(f[1]), int(f[2]))] = int(f[3]); S2[(int(f[1]), int(f[2]))] = float(f[4])
        elif f[0] == 'TOY': toy[int(f[1])] = float(f[2])
    return NL, maxM, S1, S2, toy

def box_sums(S1, S2, H, W):
    n1 = sum(v * max(0, H - h + 1) * max(0, W - w + 1) for (h, w), v in S1.items())
    n2 = sum(v * max(0, H - h + 1) * max(0, W - w + 1) for (h, w), v in S2.items())
    return n1, n2

def decomps(delta):
    out = []
    for dr in range(-9, 10):
        dc = delta - 10 * dr
        if -9 <= dc <= 9: out.append((dr, dc))
    return out

def pair_terms(delta_mod, n, S1, S2, NL):
    """best representation delta = delta_mod (mod n) in (-100,100); returns (logP_cancel, logP_special, info)."""
    best = None
    for delta in range(-99, 100):
        if (delta - delta_mod) % n: continue
        tot2 = 0.0; spec = 0.0; info = []
        for dr, dc in decomps(delta):
            H, W = 10 - abs(dr), 10 - abs(dc)
            n1, n2 = box_sums(S1, S2, H, W)
            tot2 += n2; spec = max(spec, 17 / (H * W) * n2); info.append((dr, dc, H, W, n1, n2))
        if tot2 == 0: continue
        lc = log2(tot2) - 2 * log2(NL) - 17
        ls = log2(spec) - 2 * log2(NL) - 18
        if best is None or lc > best[0]: best = (lc, ls, delta, info)
    return best

def matchings(items):
    if not items: yield []; return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]; rest = items[1:i] + items[i + 1:]
        for m in matchings(rest): yield [(a, b)] + m

def best_layout(n, G, S1, S2, NL, maxM):
    """G grids: perfect matching into pairs (one special) or, for odd G, pairs + one fixed grid."""
    single = log2(maxM / NL) - 17                  # fixed pattern of multiplicity maxM, fixed signs
    best = None
    grids = list(range(G))
    cands = []
    if G % 2 == 0:
        for m in matchings(grids): cands.append((m, None))
    else:
        for s in grids:
            for m in matchings([g for g in grids if g != s]): cands.append((m, s))
    for m, s in cands:
        terms = [pair_terms((100 * (b - a)) % n, n, S1, S2, NL) for a, b in m]
        if any(t is None for t in terms): continue
        if s is None:
            # one special pair (nonzero kappa), the rest cancel
            tot = max(sum(t[0] for t in terms) - t_sp[0] + t_sp[1] for t_sp in terms)
        else:
            tot = sum(t[0] for t in terms) + single
        if best is None or tot > best[0]: best = (tot, m, s, terms)
    return best

def mc_check(n, G, plan, NL, rnd, N=300):
    """sample the sub-event, run the scalar walk, check kappa and exceptional additions."""
    l = ell(n); lam = lam_of(n); M = 100 * G
    m, s, terms = plan[1], plan[2], plan[3]
    exc = 0; kappas = set(); tries = 0
    sp_idx = 0 if s is not None else max(range(len(terms)), key=lambda i: terms[i][1] - terms[i][0])
    for it in range(N):
        grids = [dict() for _ in range(G)]
        for pi, ((a, b), t) in enumerate(zip(m, terms)):
            delta = t[2]
            # grid b holds T, grid a holds T + delta (p_a - p_b = delta)
            special = (pi == sp_idx and s is None)
            dr0, dc0 = max(decomps(delta), key=lambda x: (10 - abs(x[0])) * (10 - abs(x[1])))
            # fixed special cell: centre of the (dr0, dc0) box, in grid b coordinates
            r_lo, c_lo = max(0, -dr0), max(0, -dc0); H0, W0 = 10 - abs(dr0), 10 - abs(dc0)
            cfix = (r_lo + H0 // 2) * 10 + (c_lo + W0 // 2)
            while True:
                tries += 1
                F = K.dice_fleet(rnd); T = [c for sh in F for c in sh]
                ok = False
                for dr, dc in decomps(delta):
                    if all(0 <= c // 10 + dr <= 9 and 0 <= c % 10 + dc <= 9 for c in T): ok = True; break
                if ok and (not special or cfix in T): break
            c0 = cfix if special else None
            for c in T:
                if c == c0: sb = sa = 1
                else:
                    sb = rnd.choice((1, -1)); sa = -sb
                grids[b][c] = sb; grids[a][c + delta] = sa
        if s is not None:
            # fixed maximal pattern (the L of multiplicity 72), all signs white
            L = [0, 1, 2, 3, 4, 5, 6, 7, 8] + [8 + 10 * i for i in range(1, 9)]
            grids[s] = {c: 1 for c in L}
        # walk: one Frobenius per cell, then add the digit; exceptional iff lam*acc = +-digit (acc != 0)
        acc = None; bad = False
        for g in range(G):
            for p in range(100):
                if acc is not None: acc = acc * lam % l
                d = grids[g].get(p)
                if d is None: continue
                if acc is None: acc = d % l; continue
                if acc == d % l or acc == (-d) % l: bad = True
                acc = (acc + d) % l
        exc += bad; kappas.add(acc)
    return exc, len(kappas), tries

def main():
    NL, maxM, S1, S2, toy = load()
    print(f"NLAB = {NL} (= 2^{log2(NL):.4f});  global max multiplicity over all 17-cell unions = {maxM} (exhaustive)")
    rt = max(toy, key=toy.get)
    print(f"\n== Toy, 1 fleet (exact enumeration): max_r0 Pr[c = e_r0] = {toy[rt]:.6g} = 2^-{-log2(toy[rt]):.2f} (r0 = {rt})"
          f"  => H_inf(k) <= {-log2(toy[rt]):.2f} bits  (spec: <= 34.13 cap; target 2*14.63 = 29.26)")
    rnd = random.Random(2026)
    for name, n, G in (("Hobby", 59, 2), ("Hobby", 59, 3), ("Serious", 179, 6), ("Serious", 179, 7)):
        b = best_layout(n, G, S1, S2, NL, maxM)
        tot, m, s, terms = b
        print(f"\n== {name}, {G} fleets: H_inf(k) <= {-tot:.2f} bits")
        for (a, bb), t in zip(m, terms):
            print(f"   pair (grid {a}, grid {bb}): delta = {t[2]:+d}; cancel term 2^{t[0]:.2f}, special term 2^{t[1]:.2f}; boxes "
                  + ", ".join(f"(dr,dc)=({dr},{dc}) {H}x{W}: fleets fitting {n1:.4g}, sum M {n2:.4g}" for dr, dc, H, W, n1, n2 in t[3] if n1))
        if s is not None: print(f"   grid {s}: fixed L-pattern (M = {maxM}) with fixed signs: 2^{log2(maxM/NL) - 17:.2f}")
        exc, nk, tries = mc_check(n, G, b, NL, rnd, N=200)
        print(f"   MC check of the construction (200 samples): distinct final scalars {nk} (1 = the construction yields a single fixed kappa); "
              f"walks hitting an exceptional addition: {exc}/200")

if __name__ == "__main__": main()
