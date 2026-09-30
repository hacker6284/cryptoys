# M8b SCRIPT-COMPUTED (exact), UNPROVED: a check of the column-turn model of stem_sign_dp.py.
# Exact P(turn of column 1, turn of column 2) for a uniform suit pattern (13 of each suit),
# from the same model; compare with the sampled values of stem_sign_check.c. Columns 0, 1, 2
# are 12 cells drawn without replacement; each column triple is weighted by the number of
# completions of the other 40 cells. A few seconds.
from collections import defaultdict
from math import factorial
from stem_sign_dp import cols, lab, vfun, rot_down

def completions(n):  # the remaining 40 cells with 13 - n_i of each suit
    r = [13 - k for k in n]
    if min(r) < 0: return 0
    return factorial(40) // (factorial(r[0]) * factorial(r[1]) * factorial(r[2]) * factorial(r[3]))

H = defaultdict(int); tot = 0
for c0 in cols:
    L0 = lab(c0); v0 = vfun(L0)
    for c1 in cols:
        L1 = lab(c1); t1 = v0 ^ (L1[0] ^ L1[1] ^ L1[2] ^ L1[3]); R1 = rot_down(L1, t1); v1 = vfun(R1)
        for c2 in cols:
            n = [0, 0, 0, 0]
            for s in c0 + c1 + c2: n[s] += 1
            w = completions(n)
            if not w: continue
            L2 = lab(c2); t2 = v1 ^ (L2[0] ^ L2[1] ^ L2[2] ^ L2[3])
            H[(t1, t2)] += w; tot += w
print("SCRIPT-COMPUTED (exact), UNPROVED: P(turn1, turn2) under the stem_sign_dp.py model")
for k in range(16): print(f"P(turn1={k//4},turn2={k%4}) = {H[(k//4, k%4)]/tot:.5f}")
