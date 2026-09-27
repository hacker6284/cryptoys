"""Alternative for 3<=m<=12 that avoids the computer-checked 1/11 lemma: use only the analytic per-row bounds
g(0)=1, g(1)=g(2)=1/13, g(j)=1/(14-j) (j>=3; one-card switching with the majority class, z>=13-j),
and compute E[prod_i g(m_i)] exactly over the multivariate hypergeometric distribution of the m moved cards."""
from fractions import Fraction as Fr
from math import comb
from itertools import product
def g(j): return Fr(1) if j==0 else (Fr(1,13) if j<=2 else Fr(1,14-j))
for m in range(3,13):
    tot=Fr(0)
    for ms in product(range(0,min(m,13)+1),repeat=4):
        if sum(ms)!=m: continue
        pr=Fr(comb(13,ms[0])*comb(13,ms[1])*comb(13,ms[2])*comb(13,ms[3]),comb(52,m))
        v=Fr(1)
        for j in ms: v*=g(j)
        tot+=pr*v
    print(f"m={m:2d}  E[prod g] = {float(tot):.6f} = 1/{float(1/tot):.1f}   {'< 1/64' if tot<Fr(1,64) else '>= 1/64 !!'}")
