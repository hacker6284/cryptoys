# M8b SCRIPT-COMPUTED, UNPROVED: the exact sign-character correlation of the v12 stem,
#   eps_stem = E_x[sgn(x) sgn(stem(x))]   over uniform decks x.
# Exact rational arithmetic, but NOT a proof: nothing here is in Lean, and the result rests on
# the model below of the stem's column turns. The model is checked only by sampling
# (stem_sign_check.c: the sign identity on 4*10^6 decks, and the sampled distribution of two
# turns against stem_turn_dp_check.py; stem_turn_dump.c + stem_turn_model_check.py: all 13
# turns, deck by deck, against the C stem on 2*10^5 decks; see NOTES.md). About 2.5 minutes,
# one core.
#
# Model. sgn(stem(x)) sgn(x) = (-1)^(sum of the 13 column turns): lay and scoop cancel, the
# row rotations and ShiftRows are powers of 13-cycles (even), and a column rotation by s is a
# 4-cycle to the power s (sign (-1)^s). Reduction to a uniform suit pattern (argued here, not
# checked independently): the stem is a bijection on decks (ddiff.h inv_stem undoes it; in
# Lean, DoubleDeal.unkeyedNoMix_injective), so its first part, lay followed by the row step,
# is injective, hence a bijection onto the grids; a uniform deck therefore gives a uniform grid
# after the row step, whose suit pattern is uniform over the 52!/(13!)^4 patterns (13 cards of
# each suit). The column turns read only the suits (sr_col_turn uses SUIT only; the model
# below uses only suit labels), so the turn sum, and hence eps, depends only on that pattern.
# Transfer-matrix DP over the columns in the stem's order (1, 2, ..., 12, then 0).
#
# Parametrised by m (m columns, m cards of each suit; the stem is m = 13). For small m the DP
# is compared exactly with a brute force that applies the same column-turn model to every
# suit pattern of the 4 x m grid; this checks the DP's bookkeeping (the transfer matrix, the
# suit counts, the wrap-around of column 0), not the model itself, and for m != 13 it is a
# statement about the model only, not about any cipher. `--small` prints only that check
# (a few seconds; rerun and byte-compared by checks/selftest.py); the default run asserts it
# silently and then prints the m = 13 value.
import sys
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

def patterns(m):   # (4m)! / (m!)^4
    return factorial(4 * m) // factorial(m) ** 4

def dp(m):
    """(number of suit patterns, signed sum) over all 4 x m suit patterns, by the DP."""
    # Column 0 first (used unrotated by column 1); its own turn/rotation comes last and does
    # not feed any later v, but its turn parity counts: turn_0 = v(col m-1 rotated) ^ su(col 0).
    # State: (suit counts, su of column 0, v of the previous column, parity); weight = number
    # of suit patterns.
    st = defaultdict(int)
    for c in cols:
        if max(cnt(c)) > m: continue
        L = lab(c); su0 = L[0] ^ L[1] ^ L[2] ^ L[3]
        st[(cnt(c), su0, vfun(L), 0)] += 1
    for p in range(1, m):
        nst = defaultdict(int)
        for (n, su0, vp, par), w in st.items():
            for c in cols:
                k = tuple(n[i] + cc for i, cc in enumerate(cnt(c)))
                if max(k) > m: continue
                L = lab(c); su = L[0] ^ L[1] ^ L[2] ^ L[3]; turn = vp ^ su
                R = rot_down(L, turn)
                nst[(k, su0, vfun(R), par ^ (turn & 1))] += w
        st = nst
    tot = 0; signed = 0
    for (n, su0, vp, par), w in st.items():
        if n != (m, m, m, m): continue
        turn0 = vp ^ su0; P = par ^ (turn0 & 1)
        tot += w; signed += w if P == 0 else -w
    assert tot == patterns(m)
    return tot, signed

def suit_patterns(m):   # every 4 x m grid (row-major) with m cards of each suit
    left = [m] * 4; g = []
    def rec():
        if len(g) == 4 * m:
            yield tuple(g); return
        for s in range(4):
            if left[s]:
                left[s] -= 1; g.append(s)
                yield from rec()
                g.pop(); left[s] += 1
    yield from rec()

def brute(m):
    """(number of suit patterns, signed sum), applying the model to each pattern directly."""
    tot = signed = 0
    for g in suit_patterns(m):
        L = [lab(tuple(g[r * m + c] for r in range(4))) for c in range(m)]
        su = [l[0] ^ l[1] ^ l[2] ^ l[3] for l in L]
        par = 0; prev = L[0]
        for j in range(1, m):          # the stem's order: columns 1, ..., m-1, then 0
            t = vfun(prev) ^ su[j]; par ^= t & 1; prev = rot_down(L[j], t)
        par ^= (vfun(prev) ^ su[0]) & 1
        tot += 1; signed += -1 if par else 1
    return tot, signed

SMALL = (2, 3)

def small_check(out):
    for m in SMALL:
        d, b = dp(m), brute(m)
        assert d == b, (m, d, b)
        if out:
            print(f"m={m}: DP (patterns, signed) = {d}, brute force = {b}, equal; "
                  f"eps = {Fraction(d[1], d[0])}")

def main():
    if sys.argv[1:] == ["--small"]:
        print("SCRIPT-COMPUTED, UNPROVED (not in Lean): the DP against a brute force over all suit")
        print("patterns of the 4 x m grid, same column-turn model (checks the DP, not the model)")
        small_check(True)
        return
    small_check(False)
    tot, signed = dp(13)
    assert tot == factorial(52) // factorial(13) ** 4
    print("SCRIPT-COMPUTED, UNPROVED (not in Lean):")
    print("suit patterns:", tot)
    print("eps_stem = E[sgn(x)sgn(stem x)] =", Fraction(signed, tot), "~", signed / tot)

if __name__ == "__main__":
    main()
