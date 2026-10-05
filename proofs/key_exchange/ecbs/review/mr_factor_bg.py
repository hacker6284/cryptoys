#!/usr/bin/env python3
"""Background attempt to factor the unfactored cofactors (twist, b'=2 curve, node) at Serious and Hobby.
PARI factor() (ECM + MPQS/SIQS); a time limit per number.  Result is informational only."""
import cypari2, time, sys
pari = cypari2.Pari(); pari.allocatemem(4 * 10**9)
def V(n, t=-1, q=3):
    a, b = 2, t
    for _ in range(n - 1): a, b = b, t * b - q * a
    return b
jobs = []
for n in (59, 179):
    q = 3 ** n
    jobs += [(f"n={n} twist q+1+V", q + 1 + V(n)), (f"n={n} b'=2 curve", q + 1 - V(n, t=2)), (f"n={n} node q+1", q + 1)]
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
for name, N in jobs:
    t0 = time.time()
    try:
        pari.default("factor_add_primes", 0)
        f = pari(f"alarm({lim}, factor({N}))")
        s = " * ".join(f"{int(p)}{'^'+str(int(e)) if int(e)>1 else ''}{'' if pari.isprime(p) else '[C'+str(int(p).bit_length())+']'}" for p, e in zip(f[0], f[1]))
    except Exception as ex:
        s = f"not finished within {lim}s ({type(ex).__name__})"
    print(f"{name}: {s}   [{time.time()-t0:.0f}s]", flush=True)
