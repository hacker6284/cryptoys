#!/usr/bin/env python3
"""Search for covered patterns with high multiplicity M(T) (labelled fleets per pattern).
(1) unions of separated straight segments: exact count by assigning ordered ships to segments;
(2) simulated annealing over whole fleets maximising M(T).  Neither proves a global maximum."""
import itertools, random, math, json
from math import log2
from ecbs_entropy import multiplicity, fleet_mask, show, NLAB
import ecbs_keys as K
SH = [5, 4, 3, 3, 2]
def seg_mult(lengths):
    tot = 0
    for assign in itertools.product(range(len(lengths)), repeat=5):
        sums = [0] * len(lengths); cnt = [0] * len(lengths)
        for s, g in zip(SH, assign): sums[g] += s; cnt[g] += 1
        if sums == list(lengths): tot += math.prod(math.factorial(c) for c in cnt)
    return tot
best = []
def parts(n, maxv, k):
    if n == 0: yield (); return
    if k == 0: return
    for v in range(min(n, maxv), 1, -1):
        for r in parts(n - v, v, k - 1): yield (v,) + r
for p in parts(17, 10, 5):
    best.append((seg_mult(p), p))
best.sort(reverse=True)
print("separated straight segments, top:", best[:6])
rnd = random.Random(5)
top = (0, None)
for run in range(6):
    fleet = K.dice_fleet(rnd); cur = multiplicity(fleet_mask(fleet))
    for it in range(15000):
        T = 3.0 * (1 - it / 15000) + 0.05
        i = rnd.randrange(5); cand = rnd.choice(K.POS[SH[i]])
        occ = set(c for j, s in enumerate(fleet) if j != i for c in s)
        if occ & set(cand): continue
        old = fleet[i]; fleet[i] = cand; new = multiplicity(fleet_mask(fleet))
        if new >= cur or rnd.random() < math.exp((log2(new) - log2(cur)) / T): cur = new
        else: fleet[i] = old
        if cur > top[0]: top = (cur, fleet_mask(fleet))
print(f"annealing max multiplicity found: {top[0]}")
print(show(top[1]))
print(f"=> single-fleet min-entropy (touching allowed, no aliasing) <= log2(NLAB/{top[0]}) + 17 = {log2(NLAB / top[0]) + 17:.3f} bits")
json.dump(dict(segments=best[:10], anneal_max=top[0], mask=hex(top[1])), open("fleet_maxmult.json", "w"))
