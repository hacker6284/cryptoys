"""Finding F1: E_m(h) = W(h_c, m) * h, where the face-turn word W depends only on
the CORNER part h_c of the chaining value.  Hence the corner chain is autonomous.
Test: randomise the edge part of h, check the face-turn trace and the corner output agree."""
import random
from md import *

def rand_pos(rng, moves=400):
    g = identity()
    for _ in range(moves):
        g = face_turn(g, rng.randrange(12), rng.randrange(1, 5))
    return g

rng = random.Random(1)
trials = 200; same_trace = same_corner = 0
for _ in range(trials):
    h1 = rand_pos(rng); h2r = rand_pos(rng)
    h2 = (h1[0], h1[1], h2r[2], h2r[3])        # same corners, independent edges
    deal = list(range(52)); rng.shuffle(deal)
    t1, t2 = [], []
    o1 = dm_step(h1, deal); em_block(h1, deal, t1)
    o2 = dm_step(h2, deal); em_block(h2, deal, t2)
    same_trace += (t1 == t2)
    same_corner += (o1[0] == o2[0] and o1[1] == o2[1])
print(f"trials={trials} identical face-turn words={same_trace} identical corner outputs={same_corner}")
