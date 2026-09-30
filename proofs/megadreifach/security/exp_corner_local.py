"""Corner-only local collisions: reorderings of k consecutive cards that give the same
CORNER state and grip (edges may differ).  Each one is a free corner collision of the
compression function (the rest of the deal, and the F3 rounds, are then identical on corners)."""
import random, itertools, sys
from md import *

def rand_state(rng):
    g = identity()
    for _ in range(300): g = face_turn(g, rng.randrange(12), rng.randrange(1, 5))
    return g, list(ROTS[rng.randrange(60)])

def run(cards, g, o):
    for c in cards: g, o = g2_step(g, o, c)
    return (tuple(g[0]), tuple(g[1]), tuple(o)), (tuple(g[2]), tuple(g[3]))

k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
rng = random.Random(11)
corner_hits = full_hits = tests = 0
for _ in range(N):
    g, o = rand_state(rng)
    cards = rng.sample(range(52), k)
    seen = {}
    for perm in itertools.permutations(cards):
        cs, es = run(perm, g, o); tests += 1
        if cs in seen:
            corner_hits += 1
            full_hits += (seen[cs][1] == es)
        else: seen[cs] = (perm, es)
print(f"k={k} states={N} orderings={tests} corner+grip collisions={corner_hits} full={full_hits}")
