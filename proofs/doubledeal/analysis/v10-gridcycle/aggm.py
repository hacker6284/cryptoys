"""Combine per-pair survival files (a b hits N) for one variant: python3 aggm.py label files..."""
import sys, math
from collections import defaultdict
S='CHSD'; R='A23456789TJQK'; nm=lambda c: R[c%13]+S[c//13]
def wil(h,n,z=1.96):
    p=h/n; den=1+z*z/n; c=p+z*z/(2*n); r=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n)); return (c-r)/den,(c+r)/den
lab=sys.argv[1]; H=defaultdict(int); N=defaultdict(int)
for f in sys.argv[2:]:
    for l in open(f):
        a,b,h,n=map(int,l.split()); H[a,b]+=h; N[a,b]+=n
if len(H) < 1326: print(lab, 'incomplete'); sys.exit()
ks=sorted(H,key=lambda k:-H[k]/N[k]); n=N[ks[0]]
cls=defaultdict(lambda:[0,0])
for a,b in H:
    c='same-rank' if a%13==b%13 else 'same-suit' if a//13==b//13 else 'other'; cls[c][0]+=H[a,b]; cls[c][1]+=N[a,b]
lo,hi=wil(H[ks[0]],n)
print(f"{lab}: N={n}/pair  worst {nm(ks[0][0])}<->{nm(ks[0][1])} {H[ks[0]]/n:.4f} (1/{n/H[ks[0]]:.0f}) CI[{lo:.4f},{hi:.4f}]"
      f"  mean {sum(H.values())/sum(N.values()):.4f}  min {H[ks[-1]]/n:.4f}  pairs>1/64: {sum(1 for k in H if H[k]/N[k]>1/64)}"
      "  | "+" ".join(f"{c} {h/m:.4f}" for c,(h,m) in sorted(cls.items())))
print("   next: "+", ".join(f"{nm(a)}<->{nm(b)} {H[a,b]/N[a,b]:.4f}" for a,b in ks[1:6]))
