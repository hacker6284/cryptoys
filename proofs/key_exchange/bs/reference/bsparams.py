"""BS parameter search/verification.
Primes have the shape p = 3^n - c  ("toll" c = 3^n - p), so 3^n = c (mod p): a peg that spills past
hole n-1 is replaced by a copy of the toll laid n holes lower.
  * sparse tolls (toy tiers):  c = 3^k + 1        (toll = a white peg at hole 0 and at hole k)
  * long tolls  (real tiers):  c = pi-trits + j   (~n/2 trits, first trits of pi in base 3, smallest
                                                   offset j making p a safe prime with g = 3 of order q)
Requirements checked: p prime, q = (p-1)/2 prime (safe prime), 3^q = 1 mod p (so g = 3 generates the
order-q subgroup of quadratic residues), 3 not = 1.
Primality: gmpy2.is_prime (Miller-Rabin with 50 random bases after trial division); for p < 3.3e24 the
deterministic Miller-Rabin set (first 12 prime bases) is also run; sympy.isprime (BPSW) is run as a
second, independent test for every p and q.  q in the big tiers is a *probable* prime (no ECPP proof)."""
import os
os.chdir(os.path.dirname(os.path.abspath(__file__)))          # every path below is relative to this directory
import gmpy2, sympy, json, sys, math, time
import numpy as np
from mpmath import mp

def det_mr(n):
    """deterministic Miller-Rabin for n < 3.317e24 (bases = first 12 primes; Sorenson-Webster 2015)"""
    assert n < 3317044064679887385961981
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % n == 0: continue
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def verify(n, c):
    p = 3**n - c; q = (p-1)//2
    r = dict(n=n, p_bits=p.bit_length(), c_trits=len(np.base_repr(c,3)) if c < 3**60 else None,
             p_prime_mr50=bool(gmpy2.is_prime(p,50)), q_prime_mr50=bool(gmpy2.is_prime(q,50)),
             p_prime_bpsw=bool(sympy.isprime(p)), q_prime_bpsw=bool(sympy.isprime(q)),
             g3_order_q=(pow(3,q,p)==1 and 3 % p != 1), p_mod_12=p % 12)
    if p < 3317044064679887385961981:
        r['p_prime_deterministic']=det_mr(p); r['q_prime_deterministic']=det_mr(q)
    return p, q, r

def trits(x):
    out=[]
    while x: out.append(x%3); x//=3
    return out

def pi_trits_int(t):
    """integer whose base-3 digits (most significant first) are the first t ternary digits of pi
       (pi = 10.0102110122...(base 3))"""
    mp.dps = int(t*0.48)+50
    return int(mp.floor(mp.pi * mp.mpf(3)**(t-2)))

def search_long(n, t=None, maxj=60_000_000, sieve_to=200_000):
    t = t or (n+1)//2
    c0 = pi_trits_int(t)
    assert len(trits(c0)) == t
    # conditions: c even (p odd), c = 1 mod 3 (p = 2 mod 3, needed for a safe prime > 7)
    j0 = next(j for j in range(6) if (c0+j) % 6 == 4)       # c = 4 mod 6  <=>  even and 1 mod 3
    P0 = 3**n - (c0 + j0)                                   # candidate m: p = P0 - 6m
    primes = list(sympy.primerange(5, sieve_to))
    t0=time.time(); tested=0
    block = 2_000_000
    for base in range(0, maxj//6, block):
        ok = np.ones(block, dtype=bool)
        for r in primes:
            # p = P0 - 6(base+m) = 0 mod r   and   q = (p-1)/2 = 0 mod r   (i.e. p = 1 mod r)
            inv6 = pow(6, -1, r)
            for target in (0, 1):
                m0 = ((P0 - 6*base - target) * inv6) % r
                ok[m0::r] = False
        for m in np.nonzero(ok)[0]:
            m = int(m); p = P0 - 6*(base+m); tested += 1
            if gmpy2.is_prime(p, 2) and gmpy2.is_prime((p-1)//2, 2) and pow(3,(p-1)//2,p)==1:
                c = 3**n - p
                return c, c - c0, tested, time.time()-t0
    raise RuntimeError("not found")

SPARSE = {"T1": (18, 2), "T2": (35, 29)}          # p = 3^n - 3^k - 1
if __name__ == "__main__":
    out = {}
    print("== sparse (two-peg toll) safe primes p = 3^n - 3^k - 1, n = 16..44 ==")
    for n in range(16, 45):
        ks = [k for k in range(1,n) if gmpy2.is_prime(3**n-3**k-1,40) and gmpy2.is_prime((3**n-3**k-2)//2,40)]
        if ks: print(f"  n={n}: k in {ks}")
    for name,(n,k) in SPARSE.items():
        c = 3**k + 1; p,q,r = verify(n,c); r.update(tier=name, k=k, toll=f"3^{k}+1", p=str(p), q=str(q), c=str(c))
        out[name]=r; print(name, json.dumps({kk:v for kk,v in r.items() if kk not in ('p','q')}))
    todo = [int(a) for a in sys.argv[1:]] or [100, 646, 1292, 1938]
    names = {100:"T6demo", 646:"R1024", 1292:"R2048", 1938:"R3072", 4845:"R7680"}
    for n in todo:
        c, j, tested, dt = search_long(n)
        p,q,r = verify(n,c)
        r.update(tier=names.get(n,f"n{n}"), toll=f"pi-trits({(n+1)//2}) + {j}", toll_trits=len(trits(c)),
                 search_offset=j, candidates_tested=tested, search_seconds=round(dt,1), p=str(p), q=str(q), c=str(c))
        out[r['tier']]=r
        print(r['tier'], json.dumps({kk:v for kk,v in r.items() if kk not in ('p','q','c')}), flush=True)
    fn = "params.json" if not sys.argv[1:] else f"params_{'_'.join(sys.argv[1:])}.json"
    json.dump(out, open(fn,"w"), indent=1)
