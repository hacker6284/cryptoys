#!/usr/bin/env python3
"""mr_invalid_trace.py -- which off-curve inputs would pass the trace check if the on-curve check were skipped (C12, Q9).
Uses the spec-transcribed trace chain from mr_q13_validation (b is never used by the formulas).
 (a) node y^2 = x^3 - x^2 (a6 = 0): predicted (this review): Frobenius acts on the torus parameter as u -> u^(-3), so the
     trace is u^((q+1)/4): exactly the odd-order part (index 4) passes.
 (b) E': y^2 = x^3 - x^2 + 2: exactly the odd part (index 2) passes (C12).
Test: random points P; P_odd = 4P (node) / 2P (E'); expect accept(P_odd) = True, accept(P) = False unless P already odd.
Run: python mr_invalid_trace.py"""
import random
from mr_ec import field, Curve
from mr_q13_validation import MV, trace_spec
rnd = random.Random(11)
for n, k in ((23, 15), (59, 39), (179, 59)):
    F = field(n, k); q = 3 ** n
    for name, a6, cof in (("node b'=0", 0, 4), ("E' b'=2", 2, 2)):
        C = Curve(F, 2, a6)
        res_odd = []; res_raw = []
        for _ in range(4):
            while True:
                x = sum((rnd.randrange(3) * F.gen() ** i for i in range(n)), F(0))
                if x == 0: continue
                r = C.rhs(x); y = r ** ((q + 1) // 4)
                if y * y == r and y != 0: break
            P = (x, y); Po = C.mul(cof, P)
            for pt, lst in ((Po, res_odd), (P, res_raw)):
                m = MV(F); m.load('bx', pt[0]); m.load('by', pt[1])
                try: ok = trace_spec(m, n)
                except (ArithmeticError, ZeroDivisionError): ok = False
                lst.append(ok)
        print(f"n = {n:3d} {name}: accept(cofactor-{cof} multiple) = {res_odd}; accept(raw random point) = {res_raw}", flush=True)
