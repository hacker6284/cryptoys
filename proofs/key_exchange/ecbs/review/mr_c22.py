#!/usr/bin/env python3
"""mr_c22.py -- independent check of C22: (a) how many holes i have x^(3i) mod f a single peg (weight 1);
(b) Gaussian normal basis types t <= 20 for F_{3^n} (criterion: r = nt+1 prime, r != 3, gcd(nt/ord_r(3), n) = 1;
Wassermann / Ash-Blake-Vanstone, I believe; for t = 1 this is the usual 'optimal type I' condition, t = 2 type II).
Also re-checks irreducibility of the taps. Run: python mr_c22.py"""
import math, sympy, flint
T = {7: 5, 23: 15, 59: 39, 179: 59}
for n, k in T.items():
    R = flint.nmod_poly
    f = [0] * (n + 1); f[n] = 1; f[k] = 2; f[0] = 2          # x^n - x^k - 1
    fp = flint.nmod_poly(f, 3)
    fac = fp.factor(); irr = len(fac[1]) == 1 and fac[1][0][1] == 1 and fac[1][0][0].degree() == n
    x = flint.nmod_poly([0, 1], 3)
    single = sum(1 for i in range(n) if sum(1 for c in (pow(x, 3 * i, fp)).coeffs() if int(c) != 0) == 1)
    types = []
    for t in range(1, 21):
        r = n * t + 1
        if not sympy.isprime(r) or r == 3: continue
        o = sympy.n_order(3, r)
        if math.gcd(n * t // o, n) == 1: types.append(t)
    print(f"n = {n:3d}: x^{n} - x^{k} - 1 irreducible over F_3: {irr}; holes i with x^(3i) a single peg: {single}/{n}; GNB types <= 20: {types}")
