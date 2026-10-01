"""ENUMERATION ONLY (no theorem uses it; NOTES.md section 5). Cycle type of the support-4 ratio q(t,c,d) by d, and the number of
distinct q of each type (seat maps as in StemPosition.seatMap; script from research-b-union-bound/q4.py)."""
import itertools
def seat(t,s,r,c):
    rho=(r+(4-s[c]%4))%4
    return (rho,(c+t[rho]%13)%13)
SEATS=[(r,c) for r in range(4) for c in range(13)]
IDX={p:i for i,p in enumerate(SEATS)}
def smap(t,s): return [IDX[seat(t,s,r,c)] for (r,c) in SEATS]
def ratio(t,s,s2):
    A=smap(t,s); B=smap(t,s2); Binv=[0]*52
    for i,b in enumerate(B): Binv[b]=i
    return tuple(A[Binv[j]] for j in range(52))
def ctype(q):
    seen=[0]*52; ty=[]
    for i in range(52):
        if seen[i]: continue
        n=0;j=i
        while not seen[j]: seen[j]=1;j=q[j];n+=1
        if n>1: ty.append(n)
    return tuple(sorted(ty))
Q={}
for t in itertools.product(range(13),repeat=4):
    for c in range(13):
        for d in (1,2,3):
            s=[0]*13; s2=[0]*13; s2[c]=d
            q=ratio(t,s,s2)
            Q.setdefault((d,ctype(q)),set()).add(q)
for k,v in sorted(Q.items()): print("d=%d type=%s distinct q: %d"%(k[0],k[1],len(v)))
from math import factorial
F=factorial(48); N=factorial(52)
# StemSupportFour sums over the 13^5 cells (t, c) for each d (each cell has its own row-amount
# condition), not over the distinct q, so the margin uses 13^5 cells per allowed d.
for name,ds,cent in (("4-cycle (d=1,3)",2,4),("double transposition (d=2)",1,8)):
    lhs=64*13**5*ds*cent*81
    print(name,": 64 * 13^5 *",ds,"*",cent,"* 48! * 81/4096 =",lhs/4096,"* 48!  vs 52!/48! =",N//F,
          " margin %.3f"%(4096*N/F/lhs))
