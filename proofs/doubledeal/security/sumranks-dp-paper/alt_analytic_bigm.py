"""m >= 13 without the computer-checked 1/11 lemma: bound rho_i <= h(z_i) with z_i = number of cards of the
global majority delta-class v* in row i:  h(z) = 1/(z+1) for 0<=z<=12 (one-card switching; z=0 gives the trivial 1),
h(13) = 1 (row constant).  E[prod_{i=0..3} h(z_i)] depends only on n* = |class v*| (multivariate hypergeometric)."""
from fractions import Fraction as Fr
from math import comb
from itertools import product
def h(z): return Fr(1) if z==13 else Fr(1,z+1)
for ns in range(4,51):
    tot=Fr(0)
    for zs in product(range(14),repeat=4):
        if sum(zs)!=ns: continue
        pr=Fr(comb(13,zs[0])*comb(13,zs[1])*comb(13,zs[2])*comb(13,zs[3]),comb(52,ns))
        v=Fr(1)
        for z in zs: v*=h(z)
        tot+=pr*v
    print(f"n*={ns:2d} (m={52-ns:2d})  E[prod h] = {float(tot):.6f}  {'< 1/64' if tot<Fr(1,64) else '>= 1/64'}")
