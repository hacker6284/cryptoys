"""Exact per-row quantities for Case A.
rho(M): for a row whose multiset of rank changes is M (13 values mod 13):
   P_arrangement[ sum_j j*delta(x_j) == target ]  = 1/13 if D(M)=sum M != 0 (any target), p0(M) if D(M)=0 (target 0)."""
from fractions import Fraction as Fr
from functools import lru_cache
from collections import Counter
def dist(values):
    """exact distribution (list of 13 Fractions) of S = sum_j j*v_{pi(j)} over uniform arrangements of the 13 values."""
    cnt=Counter(v%13 for v in values); keys=sorted(cnt); mult=tuple(cnt[k] for k in keys)
    @lru_cache(None)
    def f(pos, rem):
        if pos==13: return (1,)+(0,)*12
        out=[0]*13
        for i,k in enumerate(keys):
            if rem[i]:
                r=list(rem); r[i]-=1; sub=f(pos+1,tuple(r)); sh=(pos*k)%13
                for c in range(13):
                    if sub[c]: out[(c+sh)%13]+=sub[c]*rem[i]   # rem[i] labelled choices
        return tuple(out)
    res=f(0,mult); tot=sum(res)
    return [Fr(x,tot) for x in res]
def rho(values):
    D=sum(values)%13
    if D: return Fr(1,13)
    return dist(values)[0]
