"""Related-block / degenerate-block probes (cryptanalysis item 3).
 (a) adjacent-card swap in the deal:        does dm(h, m) change?  corners?  word?
 (b) suit shift (card -> rank*4 + (suit+1)%4 on one card): same questions
 (c) degenerate words: is the shared word W ever trivial or very short (E_m(h) = h)?
 (d) first-card range: phi(block) only reaches deals whose first card is < 18.
"""
import random
from math import factorial
from md import *
def rand_pos(rng, moves=400):
    g = identity()
    for _ in range(moves):
        g = face_turn(g, rng.randrange(12), rng.randrange(1, 5))
    return g

rng = random.Random(7)
N = 1000
eq_full = eq_corner = 0
for _ in range(N):
    h = rand_pos(rng); deal = phi_chunk([rng.randrange(256) for _ in range(28)])
    i = rng.randrange(51); d2 = deal[:]; d2[i], d2[i+1] = d2[i+1], d2[i]
    a, b = dm_step(h, deal), dm_step(h, d2)
    eq_full += a == b; eq_corner += (a[0] == b[0] and a[1] == b[1])
print(f"(a) adjacent swaps: {N} trials, equal outputs {eq_full}, equal corner outputs {eq_corner}")

eq_full = eq_corner = 0
for _ in range(N):
    h = rand_pos(rng); deal = phi_chunk([rng.randrange(256) for _ in range(28)])
    i = rng.randrange(52); d2 = deal[:]; c = d2[i]; d2[i] = (c // 4) * 4 + (c % 4 + 1) % 4
    j = d2.index(d2[i]); 
    if j != i: d2[j] = c                         # keep it a permutation (swap the two cards)
    a, b = dm_step(h, deal), dm_step(h, d2)
    eq_full += a == b; eq_corner += (a[0] == b[0] and a[1] == b[1])
print(f"(b) suit shift of one card: {N} trials, equal outputs {eq_full}, equal corner outputs {eq_corner}")

lens = []; trivial = 0
for _ in range(N):
    h = rand_pos(rng); deal = phi_chunk([rng.randrange(256) for _ in range(28)])
    tr = []; E = em_block(h, deal, tr)
    lens.append(sum(a for _, a in tr)); trivial += (E == h)
print(f"(c) word length (quarter-fifth turns) min/avg/max = {min(lens)}/{sum(lens)/N:.0f}/{max(lens)}, E_m(h) = h in {trivial}/{N}")

print(f"(d) 2^224/51! = {2**224/factorial(51):.2f}: the first card of phi(block) is always one of the first 18 of 52 values")
