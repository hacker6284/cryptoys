#!/usr/bin/env python3
"""ECBS curve facts from PARI/GP: the tier sizes n and fold exponents k come from the generated
tier() of ecbs.sudo (via ../oracle/ecbs_oracle.py), the trace recurrence V from the oracle; every
curve fact below is computed here.

E : y^2 = x^3 + 2x^2 + 1 over GF(3), then over GF(3^n) for the tier values of n.
Prints: #E(GF(3)), trace recurrence, #E(GF(3^n)) = 5*l with l proven prime (PARI isprime),
ordinary/supersingular, anomalous, embedding degree of <l> (exact when l-1 factors),
quadratic-twist order, Frobenius eigenvalue lambda, 5 = tau^3 - tau^2 + tau - 1,
fold trinomial irreducibility, family scan n < 200, and Pollard-rho cost estimates.
Run: python ecbs_curve.py (Python with cypari2, from this directory)
"""
import math, sys, time, json
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "oracle"))
sys.dont_write_bytecode = True
from ecbs_oracle import pari, V, TIERS as _TIERS
TIERS = {name: n for name, (n, k) in _TIERS.items()}
FOLD_K = {n: k for n, k in _TIERS.values()}          # x^n = x^k + 1 (irreducibility re-checked below)

def hdr(s): print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78, flush=True)

# ---- 1. E(GF(3)) by brute force -------------------------------------------------
def count_F3():
    pts = [None]
    for x in range(3):
        for y in range(3):
            if (y * y - (x ** 3 + 2 * x * x + 1)) % 3 == 0: pts.append((x, y))
    return pts

def is_prime(m): return bool(pari.isprime(m))       # PARI: proven (APR-CL / ECPP) for these sizes

def main():
    t0 = time.time(); out = {}
    hdr("1. E(GF(3)) and the trace recurrence")
    pts = count_F3(); N1 = len(pts); t = 3 + 1 - N1
    print(f"points over GF(3): {pts}  -> #E(GF(3)) = {N1}, trace t = {t}")
    print(f"characteristic polynomial of Frobenius: T^2 - ({t})T + 3 = T^2 + T + 3; disc = {t*t-12}")
    # cross-check the recurrence against PARI's point count over GF(3^n) for small n
    for n in (2, 3, 4, 5, 7):
        ffg = pari(f"ffgen(3^{n}, 'w)")
        E = pari.ellinit([0, 2, 0, 0, 1], ffg)                  # y^2 = x^3 + 2x^2 + 1 (a2=2, a6=1)
        c = int(pari.ellcard(E))
        print(f"  n={n}: 3^n+1-V_n = {3**n + 1 - V(n)}   PARI ellcard over GF(3^{n}) = {c}   agree={c == 3**n+1-V(n)}")

    hdr("2. Tier point counts #E(GF(3^n)) = 3^n + 1 - V_n")
    for name, n in TIERS.items():
        Vn = V(n); NE = 3 ** n + 1 - Vn
        l, r = divmod(NE, 5)
        prime = r == 0 and is_prime(l)
        tw = 3 ** n + 1 + Vn                                         # quadratic twist order
        print(f"\n{name}: n = {n} (n prime: {is_prime(n)})")
        print(f"  V_n (trace over GF(3^n)) = {Vn}")
        print(f"  #E = {NE}")
        print(f"  #E mod 5 = {r};  l = #E/5 = {l}")
        print(f"  l proven prime: {prime};  bits(l) = {l.bit_length()};  log2 l = {math.log2(l):.4f}")
        print(f"  ordinary (3 does not divide V_n): {Vn % 3 != 0};   anomalous (#E == 3^n): {NE == 3**n};  l == 3: {l == 3}")
        # embedding degree: order of q = 3^n in (Z/l)^*
        q = 3 ** n; tt = time.time()
        k = None; fac_ok = False
        try:
            F = pari.factor(l - 1)
            primes = [int(p) for p in F[0]]; exps = [int(e) for e in F[1]]
            fac_ok = all(is_prime(p) for p in primes)
            if fac_ok:
                k = l - 1
                for p, e in zip(primes, exps):
                    for _ in range(e):
                        if pow(q, k // p, l) == 1: k //= p
                        else: break
            print(f"  l-1 = " + " * ".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in zip(primes, exps)) + f"   (all factors proven prime: {fac_ok}) [{time.time()-tt:.1f}s]")
        except Exception as ex:
            print("  factoring l-1 failed:", ex)
        if k is not None:
            print(f"  embedding degree k = ord_l(3^n) = {k}  (log2 k = {math.log2(k):.2f}; k == l-1: {k == l-1}; (l-1)/k = {(l-1)//k})")
        small = [j for j in range(1, 2001) if pow(q, j, l) == 1]
        print(f"  q^j == 1 mod l for some j <= 2000: {small[:3] if small else 'none'}")
        # twist
        tl, tr = divmod(tw, 1)
        Ft = pari.factor(tw, 2**32)       # partial factorisation (trial division to 2^32 + PARI's cheap tests)
        tf = [(int(p), int(e)) for p, e in zip(Ft[0], Ft[1])]
        print(f"  quadratic twist order = {tw} = " + " * ".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in tf)
              + "   (last factor " + ("proven prime" if is_prime(tf[-1][0]) else "composite/unfactored") + f", {tf[-1][0].bit_length()} bits)")
        # Frobenius eigenvalue on <P>: root of x^2 + x + 3 mod l with lambda^n = 1
        roots = [int(z) for z in pari.polrootsmod(pari("x^2+x+3"), l)] if l > 3 else []
        good = [z for z in roots if pow(z, n, l) == 1]
        print(f"  roots of x^2+x+3 mod l: {len(roots)}; roots with lambda^n = 1: {len(good)}")
        # fold trinomial
        k_ = FOLD_K[n]
        irr = bool(pari.polisirreducible(pari(f"Mod(1,3)*(x^{n} - x^{k_} - 1)")))
        print(f"  fold rule x^{n} = x^{k_} + 1: x^{n} - x^{k_} - 1 irreducible over GF(3): {irr}")
        # rho
        lg = math.log2(l)
        plain = 0.5 * (lg + math.log2(math.pi / 2))
        neg = 0.5 * (lg + math.log2(math.pi / 4))
        frob = 0.5 * (lg + math.log2(math.pi / (4 * n)))            # classes {+-lambda^i}: size 2n
        src = 0.5 * (lg + math.log2(math.pi / 4)) - 0.5 * math.log2(2 * n)   # source's formula sqrt(pi l/4)/sqrt(2n)
        print(f"  Pollard rho, expected iterations (log2): plain {plain:.2f}; with negation {neg:.2f}; with negation+Frobenius (class size 2n) {frob:.2f}")
        print(f"  source formula sqrt(pi*l/4)/sqrt(2n) = 2^{src:.2f}  (counts the negation factor twice; {frob-src:.2f} bit lower than sqrt(pi*l/(4n)))")
        out[name] = dict(n=n, Vn=Vn, NE=NE, l=l, log2l=lg, prime=prime, k=k, rho_frob=frob, rho_src=src, twist=tw)

    hdr("3. The cofactor strip: 5 = tau^3 - tau^2 + tau - 1 in Z[tau], tau^2 = -tau - 3")
    # represent a + b tau as (a, b); multiply by tau: tau(a + b tau) = a tau + b tau^2 = -3b + (a - b) tau
    def mt(z): a, b = z; return (-3 * b, a - b)
    one = (1, 0); t1 = mt(one); t2 = mt(t1); t3 = mt(t2)
    s = (t3[0] - t2[0] + t1[0] - one[0], t3[1] - t2[1] + t1[1] - one[1])
    print(f"tau^3 - tau^2 + tau - 1 = {s[0]} + {s[1]}*tau  (== 5: {s == (5, 0)});  N(tau - 1) = {(-1)**2 - (-1)*1 + 3}")

    hdr("4. Family scan: prime n < 200 with #E(GF(3^n)) = 5 * prime")
    fam = []
    for n in range(2, 200):
        if not is_prime(n): continue
        NE = 3 ** n + 1 - V(n)
        if NE % 5 == 0 and is_prime(NE // 5): fam.append(n)
    print("n with cofactor exactly 5 and prime l:", fam)
    comp = [n for n in range(2, 200) if not is_prime(n) and (3 ** n + 1 - V(n)) % 5 == 0 and is_prime((3 ** n + 1 - V(n)) // 5)]
    print("(composite n with the same property, excluded because of subfields:", comp, ")")
    json.dump({k: {kk: (str(vv) if isinstance(vv, int) and abs(vv) > 2**60 else vv) for kk, vv in v.items()} for k, v in out.items()},
              open("ecbs_curve.json", "w"), indent=1)
    print(f"\n(total {time.time()-t0:.1f}s)")

if __name__ == "__main__": main()
