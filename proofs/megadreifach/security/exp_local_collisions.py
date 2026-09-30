"""Search for local (in-block) collisions: reorderings of k consecutive cards that give the
same (position, grip) state, from random mid-block states.  Such a local collision is a full
compression collision (the rest of the deal is shared) and, if reachable from the IV with
phi-rank < 2^224 on both sides, a full Hash collision."""
import random, itertools, sys
from md import *

def rand_state(rng):
    g = identity()
    for _ in range(300): g = face_turn(g, rng.randrange(12), rng.randrange(1, 5))
    o = list(ROTS[rng.randrange(60)])
    return g, o

def run(cards, g, o):
    for c in cards: g, o = g2_step(g, o, c)
    return (tuple(g[0]), tuple(g[1]), tuple(g[2]), tuple(g[3]), tuple(o))

k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
rng = random.Random(7)
hits = 0; tests = 0; ex = []
for _ in range(N):
    g, o = rand_state(rng)
    cards = rng.sample(range(52), k)
    seen = {}
    for perm in itertools.permutations(cards):
        s = run(perm, g, o)
        tests += 1
        if s in seen:
            hits += 1; ex.append((perm, seen[s]))
        else: seen[s] = perm
print(f"k={k} states={N} orderings={tests} collisions={hits}", ex[:3])
