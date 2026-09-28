"""Case B bound that depends only on m' = number of cards whose eps differs from the majority value eps*.
y_c = number of such cards in column c (of the post-row grid H).  Column factor phi_c <= f(y_c, y_{c+1}):
  y_c = 0 : column is constant eps*, so V = 0 and we need S(M_{c+1}) = 0; a column with y=1 has S != 0  -> f = [y_{c+1} != 1]
  y_c = 1 : type U (S != 0)                           -> 1/4
  y_c = 2 : type P or U                               -> <= 1/3
  y_c = 3 : type F or U                               -> <= 1/2
  y_c = 4 : anything (constant non-majority column)   -> <= 1
E[prod_c f(y_c, y_{c+1 mod 13})] computed EXACTLY (rationals) by a transfer matrix over (cards left, y_first, y_prev)."""
from fractions import Fraction as Fr
from math import comb
import sys
def f(y, ynext):
    if y == 0: return Fr(0) if ynext == 1 else Fr(1)
    return [None, Fr(1, 4), Fr(1, 3), Fr(1, 2), Fr(1)][y]
def bound(mp):
    # state after drawing k columns: (changed cards left, y_first, y_prev) -> accumulated weight (prob * product of settled factors)
    st = {}
    for y in range(5):
        p = Fr(comb(mp, y) * comb(52 - mp, 4 - y), comb(52, 4))
        if p: st[(mp - y, y, y)] = st.get((mp - y, y, y), 0) + p
    for k in range(1, 13):
        rem = 52 - 4*k; nst = {}
        for (left, y0, yp), w in st.items():
            for y in range(5):
                if y > left or 4 - y > rem - left: continue
                p = Fr(comb(left, y) * comb(rem - left, 4 - y), comb(rem, 4))
                fv = f(yp, y)
                if p and fv:
                    key = (left - y, y0, y); nst[key] = nst.get(key, 0) + w * p * fv
        st = nst
    return sum(w * f(yp, y0) for (left, y0, yp), w in st.items() if left == 0)
worst = Fr(0)
for mp in range(2, 40):
    b = bound(mp); worst = max(worst, b)
    print(f"m'={mp:2d}  bound = {float(b):.3e} = 1/{float(1/b) if b else float('inf'):.1f}")
print("max over m' in [2,39]:", float(worst), "  < 1/64:", worst < Fr(1, 64))
