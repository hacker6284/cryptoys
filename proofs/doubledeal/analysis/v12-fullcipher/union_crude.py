"""ARITHMETIC ONLY (no theorem uses it; NOTES.md section 5). The arithmetic that sized the
support s >= 8 route now PROVED in Lean (security library, StemUnion): the conjugate-set bound
#{pi | pi^-1 delta pi = q} <= s^floor(s/2) * (52-s)!  (StemUnion.card_conjSet_le_reps), summed
over the q parameters (t, t', e) with 52 - zRows*zCols = s (count nq below: t free, t' agreeing
with t mod 13 in exactly a rows, e = s' - s zero mod 4 in exactly b columns; q depends only on
(t, t', e) by StemUnion.ratio_eq_ratioQ, and the count is StemUnion.card_params; the margin is
StemUnion.paramCount_check). This script recomputes that arithmetic independently. Support 4 is
not this route (StemSupportFour)."""
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
