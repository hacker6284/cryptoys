#!/usr/bin/env python3
"""Independent re-check of the review's twist / invalid-curve figures (REVIEW.md item 2, Q5.4-5, C1, C12).
Orders computed here from traces: E (t = -1): q + 1 - V_n;  quadratic twist: q + 1 + V_n;
E' : y^2 = x^3 + 2x^2 + 2 (b' = 2; t' = +2 over GF(3)): q + 1 - V'_n;  node (b' = 0): q + 1.
Cross-check against PARI ellcard at small n.  Hobby: factored here by PARI from scratch.  Serious: the review's
stated factors are checked (divide exactly, product = order, every factor proven prime by PARI isprime),
which verifies the factorisation completely.  The trace check passes exactly the odd part of E' (index 2) and of
the node (index 4) [review, proved]; the leak = the part of that odd order made of primes < 2^60."""
import math, sys
sys.dont_write_bytecode = True
import os as _os, sys as _sys; _sys.path.insert(0, _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', 'oracle'))  # PARI oracle
from ecbs_oracle import pari, V
def lg(x): return math.log2(x)
def orders(n):
    q = 3 ** n
    return dict(E=q + 1 - V(n, -1), twist=q + 1 + V(n, -1), Eprime=q + 1 - V(n, 2), node=q + 1)
# cross-check with PARI at small odd n
for n in (3, 5, 7):
    w = pari(f"ffgen(3^{n}, 'w)")
    o = orders(n)
    cE = int(pari.ellcard(pari.ellinit([0, 2, 0, 0, 1], w)))
    cT = int(pari.ellcard(pari.ellinit([0, 1, 0, 0, 2], w)))          # twist: a2 -> -a2, a6 -> -a6
    cP = int(pari.ellcard(pari.ellinit([0, 2, 0, 0, 2], w)))
    print(f"n={n}: PARI ellcard E {cE == o['E']}, twist y^2=x^3+x^2+2 {cT == o['twist']}, E' {cP == o['Eprime']}")
claimed = {
 179: dict(twist=[3, 1433, 160881263, 76235720288049653, 8922179461560676120351],
           Eprime=[2, 16859153558033], node=[2, 2, 3755779, 47029186391731, 9248363581047133])}
for n in (59, 179):
    o = orders(n)
    for kind in ('twist', 'Eprime', 'node'):
        N = o[kind]
        if n == 59:
            f = pari.factor(N); ps = [int(p) for p, e in zip(f[0], f[1]) for _ in range(int(e))]
        else:
            ps = list(claimed[n][kind]); rest = N
            for p in ps: assert rest % p == 0; rest //= p
            ps.append(rest)
        assert math.prod(ps) == N and all(bool(pari.isprime(p)) for p in ps)
        odd = [p for p in ps if p != 2]
        small = [p for p in odd if p < 2 ** 60]
        leak = lg(math.prod(small)) if small else 0.0
        big = max(ps)
        print(f"n={n} {kind:6s}: order 2^{lg(N):.2f} = " + "*".join(str(p) if p < 10**12 else f"p{p.bit_length()}" for p in ps)
              + f"  [all prime, product = order]; largest prime {lg(big):.2f} bits (rho ~2^{lg(big)/2:.1f})"
              + (f"; odd part passes the trace check: primes < 2^60 give k mod a {leak:.1f}-bit number for ~2^{lg(max(small))/2:.1f} work" if kind != 'twist' else ""))
