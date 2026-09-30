"""Aggregate round.c output: per same-suit pair, SumRanks-stage survival and full-round survival."""
import sys, math
S='CHSD'; R='A23456789TJQK'; nm=lambda c: R[c%13]+S[c//13]
def wil(h,n,z=1.96):
    p=h/n; den=1+z*z/n; c=p+z*z/(2*n); r=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n)); return (c-r)/den,(c+r)/den
for f in sys.argv[1:]:
    rows=[tuple(map(int,l.split())) for l in open(f)]
    if not rows: print(f, 'empty'); continue
    n=rows[0][4]; rows.sort(key=lambda x:-x[3])
    hs=sum(r[2] for r in rows); hr=sum(r[3] for r in rows)
    a,b,s,h,_=rows[0]; lo,hi=wil(h,n)
    print(f"{f}: N={n}/pair; SR-stage mean {hs/len(rows)/n:.2e}; round mean {hr/len(rows)/n:.2e}; "
          f"GC|SR mean {hr/max(hs,1):.3f}; worst round {nm(a)}<->{nm(b)} {h}/{n}={h/n:.2e} CI[{lo:.1e},{hi:.1e}]; "
          "next: "+", ".join(f"{nm(x)}<->{nm(y)} {hh/n:.1e}" for x,y,_,hh,_ in rows[1:4]))
