#!/usr/bin/env python3
"""mr_extractor_recalc.py -- C19 SD / H_inf bounds with the Weil/Deligne constant 3 (this review, Q11a) vs the spec's 4.
delta <= c sqrt(q)/(l-1);  SD <= 1/2 sqrt(3^m - 1) delta;  fibre: Pr[Z=z] <= 2*3^(n-m)/(l-1) (unchanged).
Run: python mr_extractor_recalc.py"""
from mpmath import mp, mpf, sqrt, log
mp.dps = 60
import re
txt = open('mr_orders_results.txt').read()
def ell(n):
    m = re.search(rf"n = {n}, n prime.*?; l = (\d+)", txt, re.S)
    return int(m.group(1))
for name, n in (("Toy", 23), ("Hobby", 59), ("Serious", 179)):
    l = ell(n); q = mpf(3) ** n
    print(f"{name} (n = {n}, log2 l = {float(log(l, 2)):.2f})")
    for c in (4, 3):
        d = c * sqrt(q) / (l - 1)
        sd = lambda m: mpf(1) / 2 * sqrt(mpf(3) ** m - 1) * d
        ms = {"Serious": (100, 94, 80, 60, 13), "Hobby": (40, 20), "Toy": (16, 8)}[name]
        row = "; ".join(f"m={m}: SD<=2^{float(log(sd(m), 2)):.2f}" for m in ms)
        best = {t: max([m for m in range(1, n + 1) if sd(m) <= mpf(2) ** -t], default=None) for t in (64, 128)}
        print(f"  c = {c}: {row}; largest m with SD<=2^-64: {best[64]}, with SD<=2^-128: {best[128]}")
