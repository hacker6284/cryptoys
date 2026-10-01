"""ARITHMETIC ONLY (no theorem uses it; NOTES.md section 5). Union bound for support s >= 8 with a crude conjugate-set bound
#{pi | pi^-1 delta pi = q} <= s^floor(s/2) * (52-s)!  (one representative per cycle of q, every
cycle of q has length >= 2; not proved), summed over the q parameters (t, t', e) with
52 - zRows*zCols = s (count nq below: t free, t' agreeing with t mod 13 in exactly a rows,
e = s' - s zero mod 4 in exactly b columns; that q depends only on (t, t', e) is a paper
argument, not proved). Support 4 is not this route (StemSupportFour)."""
from math import comb, factorial
from fractions import Fraction
N=factorial(52)
supp={}
for a in range(5):
    for b in range(14):
        s=52-a*b
        if s==0: continue
        nq=13**4*comb(4,a)*12**(4-a)*comb(13,b)*3**(13-b)
        supp[s]=supp.get(s,0)+nq
worst=(0,None)
for s in sorted(supp):
    crude=Fraction(64*supp[s]*s**(s//2)*factorial(52-s),N)
    worst=max(worst,(float(crude),s))
    print(f"s={s:2d} nq={supp[s]:.3e} 64*nq*s^(s/2)*(52-s)!/52! = {float(crude):.3e} {'OK' if crude<=1 else 'FAILS'}{' (support 4: not this route)' if s==4 else ''}")
print("worst over s >= 8: %.3e at s=%d" % max((w, t) for (w, t) in
    ((float(Fraction(64*supp[t]*t**(t//2)*factorial(52-t),N)), t) for t in supp) if t >= 8))
