"""Finding F2 (proved in Lean: FreeStart.dmStep_collision_of_sq / dmStep_pseudo_collision).
Universal free-start (pseudo-)collisions of the MegaDreifach compression function
dm(h, m) = h * E_m(h), with E_m(h) = W(h_c, m) * h  (CornerDriven.emBlock_word).

Recipe, for ANY corner part c and ANY block m:
  1. W  := E_m(h0) * h0^{-1}  for any h0 with corners c        (one block encryption)
  2. pick two distinct legal edge involutions u != v (e.g. two different pairs of
     disjoint edge 2-cycles; even permutation, zero flips)
  3. h  := (c, u * W_e^{-1}),  h' := (c, v * W_e^{-1})   (same corners, different edges)
  Then (hW)^2 = u^2 = 1 = v^2 = (h'W)^2 on edges, hence dm(h,m) = dm(h',m).
Cost: 3 block encryptions.  Checked here with the KAT-verified transliteration md.py.
"""
import random, sys
from md import *

def edge_only(ep, eo):
    return (list(range(20)), [0]*20, ep, eo)

def involution(rng):
    # product of two disjoint transpositions of edges (even perm), optionally with 2 flips
    a, b, c, d = rng.sample(range(30), 4)
    ep = list(range(30)); ep[a], ep[b] = ep[b], ep[a]; ep[c], ep[d] = ep[d], ep[c]
    eo = [0]*30
    return edge_only(ep, eo)

def rand_pos(rng, moves=300):
    g = identity()
    for _ in range(moves):
        g = face_turn(g, rng.randrange(12), rng.randrange(1, 5))
    return g

def legal(p):
    cp, co, ep, eo = p
    par = lambda q: sum(q[i] > q[j] for i in range(len(q)) for j in range(i+1, len(q))) % 2
    return par(cp) == 0 and par(ep) == 0 and sum(co) % 3 == 0 and sum(eo) % 2 == 0

def with_edges(c, e):
    return (c[0], c[1], e[2], e[3])

def attack(rng, h0, deal):
    W = compose(em_block(h0, deal), inverse(h0))      # E = compose(W, h0)
    assert compose(W, h0) == em_block(h0, deal)
    Winv = inverse(W)
    while True:
        u, v = involution(rng), involution(rng)
        if u != v: break
    # we need h*W (the sudo's group product, compose(h, W)?) to be an involution on edges;
    # try both conventions and keep the one that verifies.
    for name, mk in (("compose(Winv,u)", lambda x: compose(Winv, x)),
                     ("compose(u,Winv)", lambda x: compose(x, Winv))):
        h1 = with_edges(h0, mk(u)); h2 = with_edges(h0, mk(v))
        if h1 != h2 and dm_step(h1, deal) == dm_step(h2, deal):
            return h1, h2, name
    return None

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    ok = 0; T = 50
    for t in range(T):
        h0 = rand_pos(rng)
        msg = bytes(rng.randrange(256) for _ in range(28))
        deal = phi_chunk(list(msg))
        r = attack(rng, h0, deal)
        if r:
            h1, h2, conv = r
            assert legal(h1) and legal(h2) and h1 != h2
            ok += 1
            if t == 0:
                print("example block:", msg.hex())
                print("h  =", position_to_bytes(h1).hex())
                print("h' =", position_to_bytes(h2).hex())
                print("dm(h,m) = dm(h',m) =", position_to_bytes(dm_step(h1, deal)).hex())
                print("convention:", conv)
    print(f"{ok}/{T} random (corner part, block) pairs gave a verified legal pseudo-collision")
