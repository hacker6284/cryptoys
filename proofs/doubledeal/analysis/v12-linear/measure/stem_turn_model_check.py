# M8b CHECK of the column-turn model of stem_sign_dp.py, deck by deck (sampled; EMPIRICAL
# ONLY, not a proof). Reads the output of stem_turn_dump.c (suits of the grid after the row
# step, then the 13 turns the C stem applied) and recomputes every turn with the model's own
# functions (lab, vfun, rot_down), in the stem's column order 1, ..., 12, 0: column 1 reads
# column 0 unrotated, column j >= 2 reads column j-1 after its turn, and column 0 reads
# column 12 after its turn. Also prints the parity split of the turn sum (for information).
# Usage: python3 stem_turn_model_check.py FILE
import sys
from stem_sign_dp import lab, vfun, rot_down

decks = bad = 0
hist = [0] * 4
for line in open(sys.argv[1]):
    v = list(map(int, line.split()))
    g, turns = v[:52], v[52:]
    L = [lab(tuple(g[r * 13 + c] for r in range(4))) for c in range(13)]
    su = [l[0] ^ l[1] ^ l[2] ^ l[3] for l in L]
    model = [0] * 13
    prev = L[0]
    for j in range(1, 13):
        model[j] = vfun(prev) ^ su[j]
        prev = rot_down(L[j], model[j])
    model[0] = vfun(prev) ^ su[0]
    decks += 1
    bad += model != turns
    hist[sum(turns) & 1] += 1
print("SAMPLED CHECK, not a proof: the model's 13 column turns vs the C stem's, deck by deck")
print(f"decks: {decks}, decks with any turn mismatch: {bad}")
print(f"parity of the turn sum: even {hist[0]}, odd {hist[1]}")
