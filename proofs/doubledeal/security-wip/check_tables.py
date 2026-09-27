# Exact rational check of the numeric tables EA_le and EB_le (Standalone.lean),
# using the same definitions as Lean (hA, fB with f(2,0)=1/4). EB via transfer matrix.
# Output: max EA on 13..49 = 0.008416 (n=49) <= 1/100; EB(2)=1/68, EB(3)=1/425, all <= 1/64.
from fractions import Fraction as F
from math import comb
def hA(z): return F(1) if z==13 else F(1,z+1)
def EA(n):
    tot=F(0)
    for a in range(14):
        for b in range(14):
            for c in range(14):
                d=n-a-b-c
                if 0<=d<=13:
                    p=F(1)
                    for z in (a,b,c,d): p*=comb(13,z)*hA(z)
                    tot+=p
    return tot/comb(52,n)
ea=[(n,float(EA(n))) for n in range(13,50)]
print(max(ea,key=lambda t:t[1]), all(EA(n)<=F(1,100) for n in range(13,50)))
def fB(y,yp):
    if y==0: return F(0) if yp==1 else F(1)
    if y==1: return F(1,4)
    if y==2: return F(1,4) if yp==0 else F(1,3)
    if y==3: return F(1,2)
    return F(1)
def EB(m):
    tot=F(0)
    for y0 in range(5):
        # states: (sum, prev) weights
        st={(y0,y0):F(comb(4,y0))}
        for j in range(1,13):
            ns={}
            for (s,pv),w in st.items():
                for y in range(5):
                    if s+y>m: continue
                    k=(s+y,y); ns[k]=ns.get(k,F(0))+w*comb(4,y)*fB(pv,y)
            st=ns
        for (s,pv),w in st.items():
            if s==m: tot+=w*fB(pv,y0)
    return tot/comb(52,m)
eb=[(m,EB(m)) for m in range(2,40)]
print([(m,float(v)) for m,v in eb[:4]], max(float(v) for m,v in eb), all(v<=F(1,64) for m,v in eb))
