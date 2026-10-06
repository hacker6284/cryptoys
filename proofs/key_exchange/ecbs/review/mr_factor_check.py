#!/usr/bin/env python3
"""mr_factor_check.py -- primality of every factor in mr_factor_bg_results.txt, product check, bit sizes,
and Pohlig-Hellman / rho cost on the twist, b'=2 curve and node.  Run: python mr_factor_check.py"""
import math, re, cypari2
pari = cypari2.Pari()
V = {59: -237742473477667, 179: 8415761749837112564717203646960402152220333}
for line in open('mr_factor_bg_results.txt'):
    m = re.match(r"n=(\d+) (.+?): (.+?)\s+\[", line)
    if not m: continue
    n = int(m.group(1)); what = m.group(2); fs = m.group(3).split(' * ')
    q = 3 ** n
    N = {"twist q+1+V": q + 1 + V[n], "b'=2 curve": None, "node q+1": q + 1}[what]
    prod = 1; parts = []
    for f in fs:
        p, e = (f.split('^') + ['1'])[:2]; p = int(p); e = int(e); prod *= p ** e
        parts.append((p, e, bool(pari.isprime(p, 2))))   # flag 2: APRCL proof
    ok = (N is None) or (prod == N)
    big = max(p for p, _, _ in parts)
    smooth = math.log2(prod) - math.log2(big)
    print(f"n={n} {what}: product matches order: {ok if N else 'n/a (order from mr_orders)'}; all factors proven prime: {all(t for *_, t in parts)}; "
          f"log2 order {math.log2(prod):.2f}; largest prime {math.log2(big):.2f} bits (rho ~2^{math.log2(big)/2:.1f}); "
          f"part below the largest prime: {smooth:.2f} bits; second-largest prime {math.log2(sorted(p for p,_,_ in parts)[-2]):.2f} bits")
