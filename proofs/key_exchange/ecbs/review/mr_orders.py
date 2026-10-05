#!/usr/bin/env python3
"""mr_orders.py -- independent recomputation of the ECBS curve facts (Mathematician review).
Independent of kx-specs/ecbs: exact Z[tau] arithmetic, brute-force point counts with python-flint,
primality by three different implementations (FLINT fmpz_is_prime [proving], sympy isprime [BPSW],
PARI isprime [APR-CL, proving]).  PARI is used only as one of the cross-checks and for factoring.
Run: python mr_orders.py"""
import math, itertools, time, sys
import flint, sympy
from sympy.ntheory import sqrt_mod
import cypari2
from mr_ec import field, Curve, el_from_digits
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)
TIERS = {"Demo": (7, 5), "Toy": (23, 15), "Hobby": (59, 39), "Serious": (179, 59)}

def zmul(u, v):          # (a + b tau)(c + d tau), tau^2 = -tau - 3
    a, b = u; c, d = v
    return (a * c - 3 * b * d, a * d + b * c - b * d)
def zpow(u, n):
    r = (1, 0)
    while n:
        if n & 1: r = zmul(r, u)
        u = zmul(u, u); n >>= 1
    return r
def ztrace(u): return 2 * u[0] - u[1]          # tau + taubar = -1
def znorm(u): return u[0] ** 2 - u[0] * u[1] + 3 * u[1] ** 2
def V(n, t=-1, q=3):
    a, b = 2, t
    if n == 0: return 2
    for _ in range(n - 1): a, b = b, t * b - q * a
    return b

def prime3(m):
    f = bool(flint.fmpz(m).is_prime()); s = bool(sympy.isprime(m)); p = bool(pari.isprime(m))
    return f, s, p

def brute_count(n, a2, a6):
    F = field(n); C = Curve(F, a2, a6); cnt = 1; e = (3 ** n - 1) // 2
    for digs in itertools.product(range(3), repeat=n):
        x = el_from_digits(F, digs); r = C.rhs(x)
        if r == 0: cnt += 1
        elif r ** e == 1: cnt += 2
    return cnt

def main():
    t0 = time.time()
    print("== 0. Curve over GF(3): y^2 = x^3 + 2x^2 + 1")
    pts = [(x, y) for x in range(3) for y in range(3) if (y * y - x ** 3 - 2 * x * x - 1) % 3 == 0]
    print(f"   affine points {pts}; #E(F_3) = {len(pts) + 1}; trace t = {3 + 1 - len(pts) - 1}")
    # char-3 invariants for y^2 = x^3 + a2 x^2 + a6: Delta = -a2^3 a6, j = -a2^3/a6 (derived in REVIEW.md)
    a2, a6 = 2, 1
    print(f"   Delta = -a2^3 a6 = {(-a2**3*a6) % 3} (mod 3), j = -a2^3/a6 = {(-a2**3 * pow(a6, -1, 3)) % 3} (mod 3): j != 0 => ordinary over every extension")
    print("\n== 1. Trace: exact Z[tau] power vs recurrence vs brute force")
    for n in range(1, 12):
        z = zpow((0, 1), n); tr = ztrace(z); assert znorm(z) == 3 ** n
        NE = 3 ** n + 1 - tr; assert tr == V(n)
        line = f"   n={n:2d}: Tr(tau^n) = {tr:6d} = V_n; #E = {NE}"
        if n <= 11:
            bc = brute_count(n, 2, 1); line += f"; brute force {bc} {'OK' if bc == NE else 'MISMATCH'}"
        if n % 2 == 1 and n <= 9:
            tw = 3 ** n + 1 + tr; btw = brute_count(n, 1, 2)
            line += f"; twist y^2=x^3+x^2+2: formula {tw}, brute {btw} {'OK' if tw == btw else 'MISMATCH'}"
        print(line, flush=True)
    print(f"   ({time.time()-t0:.1f}s)")
    print("\n== 2. Tiers")
    fam = []
    for name, (n, k) in TIERS.items():
        tr = ztrace(zpow((0, 1), n)); q = 3 ** n; NE = q + 1 - tr; l, r5 = divmod(NE, 5)
        print(f"\n-- {name}: n = {n}, n prime {prime3(n)[0]}")
        print(f"   trace V_n = {tr}; V_n mod 3 = {tr % 3} (ordinary iff != 0); |V_n| <= 2 sqrt(q): {tr * tr <= 4 * q}")
        print(f"   #E = {NE}")
        print(f"   #E mod 5 = {r5}, #E mod 25 = {NE % 25}; l = {l}")
        pf = prime3(l); print(f"   l prime? FLINT(proving) {pf[0]}, sympy BPSW {pf[1]}, PARI APR-CL {pf[2]}; bits {l.bit_length()}, log2 l = {math.log2(l):.4f}")
        print(f"   anomalous (#E == q)? {NE == q};  l == 3? {l == 3};  l == 5? {l == 5}")
        # l - 1 factorisation
        fac = pari.factor(l - 1); ps = [int(p) for p in fac[0]]; es = [int(e) for e in fac[1]]
        assert math.prod(p ** e for p, e in zip(ps, es)) == l - 1
        allp = all(all(prime3(p)) for p in ps)
        print(f"   l - 1 = " + " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in zip(ps, es)) + f"  (every factor prime by all three tests: {allp})")
        kk = l - 1
        for p, e in zip(ps, es):
            for _ in range(e):
                if pow(q, kk // p, l) == 1: kk //= p
                else: break
        assert pow(q, kk, l) == 1
        print(f"   embedding degree k = ord_l(q) = {kk}; log2 k = {math.log2(kk):.2f}; (l-1)/k = {(l - 1) // kk}")
        k3 = l - 1
        for p, e in zip(ps, es):
            for _ in range(e):
                if pow(3, k3 // p, l) == 1: k3 //= p
                else: break
        print(f"   ord_l(3) = {'l-1' if k3 == l - 1 else k3}; is 3 in <lambda>? (ord_l(3) | n): {n % k3 == 0 if k3 else None}")
        # lambda
        rts = sorted(set(((-1 + s) * pow(2, -1, l)) % l for s in sqrt_mod(-11 % l, l, all_roots=True)))
        good = [x for x in rts if pow(x, n, l) == 1]
        assert all((x * x + x + 3) % l == 0 for x in rts)
        lam = good[0] if len(good) == 1 else None
        print(f"   roots of x^2+x+3 mod l: {len(rts)}; with lambda^n = 1: {len(good)}; lambdabar = -1-lambda has lambdabar^n = 1? {pow((-1 - lam) % l, n, l) == 1}")
        print(f"   lambdabar = 3/lambda mod l: {((-1 - lam) % l) == (3 * pow(lam, -1, l)) % l}")
        # twist and other curves reachable when b is ignored
        tw = q + 1 + tr; ft = pari.factor(tw, 10 ** 7)
        tws = " * ".join(f"{int(p)}{'^' + str(int(e)) if int(e) > 1 else ''}{'' if pari.isprime(p) else '[C' + str(int(p).bit_length()) + ']'}" for p, e in zip(ft[0], ft[1]))
        print(f"   quadratic twist (y^2 = x^3 + x^2 + 2) order q+1+V_n = {tw} = {tws}")
        N2 = q + 1 - V(n, t=2); f2 = pari.factor(N2, 10 ** 7)
        print(f"   b'=2 curve (trace 2 over F_3) order = " + " * ".join(f"{int(p)}{'^' + str(int(e)) if int(e) > 1 else ''}{'' if pari.isprime(p) else '[C' + str(int(p).bit_length()) + ']'}" for p, e in zip(f2[0], f2[1])))
        fn = pari.factor(q + 1, 10 ** 7)
        print(f"   node (b'=0) nonsingular points: order q+1 = " + " * ".join(f"{int(p)}{'^' + str(int(e)) if int(e) > 1 else ''}{'' if pari.isprime(p) else '[C' + str(int(p).bit_length()) + ']'}" for p, e in zip(fn[0], fn[1])))
        lg = math.log2(l)
        print(f"   rho expected iterations log2: plain sqrt(pi l/2) {0.5*(lg+math.log2(math.pi/2)):.2f}; +-1 classes {0.5*(lg+math.log2(math.pi/4)):.2f}; +-tau^i classes (2n) {0.5*(lg+math.log2(math.pi/(4*n))):.2f}")
        print(f"   2*rho(2n) = {lg + math.log2(math.pi/(4*n)):.2f} bits")
        # base point by the rule (spec 5.1), independent arithmetic in the tap basis
        F = field(n, k); C = Curve(F, 2, 1); tg = F.gen(); e = (q + 1) // 4
        for j in range(1, n):
            x = tg ** j; rr = C.rhs(x); y = rr ** e
            if y * y == rr: break
        R = (x, y); P = C.mul(5, R)
        strip = C.add(C.add(C.add(C.frob(R, 3), C.neg(C.frob(R, 2))), C.frob(R, 1)), C.neg(R))
        ordl = C.mul(l, P) is None and P is not None
        lamP = C.mul(lam, P) == C.frob(P)
        def dg(a):
            L = [int(c) for c in a.to_list()] + [0] * n
            return "".join(".WR"[c] for c in L[:n])
        print(f"   base point rule: first hole j = {j}; P = 5R has order l: {ordl}; strip tau^3-tau^2+tau-1 == 5 on R: {strip == P}; tau(P) == lambda P: {lamP}")
        if n <= 23: print(f"      P: x = {dg(P[0])}  y = {dg(P[1])}")
        else:
            import hashlib
            print(f"      P digits sha256(x|y)[:16] = {hashlib.sha256((dg(P[0]) + '|' + dg(P[1])).encode()).hexdigest()[:16]}  (hash format may differ from the spec's)")
    print("\n== 3. Family scan: prime n < 200 with #E = 5 * prime")
    for n in range(2, 200):
        if not sympy.isprime(n): continue
        NE = 3 ** n + 1 - V(n)
        if NE % 5 == 0 and sympy.isprime(NE // 5) and bool(flint.fmpz(NE // 5).is_prime()): fam.append(n)
    print("   n =", fam)
    print(f"\n(total {time.time()-t0:.1f}s)")

if __name__ == "__main__": main()
