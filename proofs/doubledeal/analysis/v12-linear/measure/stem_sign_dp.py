# M8b SCRIPT-COMPUTED, UNPROVED: the exact sign-character correlation of the v12 stem,
#   eps_stem = E_x[sgn(x) sgn(stem(x))]   over uniform decks x.
# Exact rational arithmetic, but NOT a proof: nothing here is in Lean, and the result rests on
# the model below of the stem's column turns (checked only by stem_sign_check.c, sampled, and
# stem_turn_dp_check.py; see NOTES.md). About 2.5 minutes, one core.
#
# Model. sgn(stem(x)) sgn(x) = (-1)^(sum of the 13 column turns): lay and scoop cancel, the
# row rotations and ShiftRows are powers of 13-cycles (even), and a column rotation by s is a
# 4-cycle to the power s (sign (-1)^s). The grid after the row step is uniform (the row step
# is a bijection), so eps depends only on a uniform suit pattern (13 cards of each suit).
# Transfer-matrix DP over the columns in the stem's order (1, 2, ..., 12, then 0).
from fractions import Fraction
from itertools import product
from math import factorial
from collections import defaultdict

LABEL = [0, 2, 3, 1]; TW = [0, 2, 3, 1]

def vfun(col):   # col = labels (rows 0..3) of the previous column, as used
    return col[1] ^ TW[col[2]] ^ TW[TW[col[3]]]

def rot_down(col, s): return tuple(col[(i - s) % 4] for i in range(4))

cols = list(product(range(4), repeat=4))     # suit tuples (suits 0..3), rows 0..3
lab = lambda c: tuple(LABEL[s] for s in c)

def cnt(c):
    r = [0, 0, 0, 0]
    for s in c: r[s] += 1
    return tuple(r)

def main():
    # Column 0 first (used unrotated by column 1); its own turn/rotation comes last and does
    # not feed any later v, but its turn parity counts: turn_0 = v(col 12 rotated) ^ su(col 0).
    # State: (suit counts, su of column 0, v of the previous column, parity); weight = number
    # of suit patterns.
    st = defaultdict(int)
    for c in cols:
        L = lab(c); su0 = L[0] ^ L[1] ^ L[2] ^ L[3]
        st[(cnt(c), su0, vfun(L), 0)] += 1
    for p in range(1, 13):
        nst = defaultdict(int)
        for (n, su0, vp, par), w in st.items():
            for c in cols:
                m = tuple(n[i] + cc for i, cc in enumerate(cnt(c)))
                if max(m) > 13: continue
                L = lab(c); su = L[0] ^ L[1] ^ L[2] ^ L[3]; turn = vp ^ su
                R = rot_down(L, turn)
                nst[(m, su0, vfun(R), par ^ (turn & 1))] += w
        st = nst
    tot = 0; signed = 0
    for (n, su0, vp, par), w in st.items():
        if n != (13, 13, 13, 13): continue
        turn0 = vp ^ su0; P = par ^ (turn0 & 1)
        tot += w; signed += w if P == 0 else -w
    assert tot == factorial(52) // factorial(13) ** 4
    print("SCRIPT-COMPUTED, UNPROVED (not in Lean):")
    print("suit patterns:", tot)
    print("eps_stem = E[sgn(x)sgn(stem x)] =", Fraction(signed, tot), "~", signed / tot)

if __name__ == "__main__":
    main()
