"""Exact step-action analysis of PassKey F (SPEC 3.7) for card swaps tau = (a b).
At step i (i = 0..51) the controller C is popped; the hand then has n = 51 - i cards and the key pile i.
F's move at that step is determined by C only through
    hand rotation  h(C, i) = (suit(C) mod n) + (rank(C) if rank(C) < n else 0)   (mod n)
    key rotation   k(C, i) = rank(C) if (rank(C) >= n and rank(C) < i) else 0    (mod i)
The two hand cuts are both left rotations of the same packet, so they add: for rank < n only suit + rank mod n matters.
E(a, b) = steps where a and b would make the same move. Every card is controller exactly once and the controller
order is a uniform permutation when the input is uniform (each step is a bijection of (hand, key) states of fixed
sizes, so the state after i steps is uniform), so the steps (i_a, i_b) at which a and b control are a uniform ordered
pair of distinct steps. If both lie in E, F(tau K) = tau F(K) (every step makes the same move, by induction).
Hence  P[F(tau K) = tau F(K)] >= e (e - 1) / 2652,  e = |E(a, b)|   (exact lower bound; equality up to paths that
diverge and later re-merge, measured separately in keysched.c).
usage: python3 colliders.py"""
from fractions import Fraction
from itertools import combinations
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
NAME = lambda c: 'A23456789TJQK'[c % 13] + 'CHSD'[c // 13]
def act(c, i):
    n = 51 - i; s, r = suit(c), rank(c)
    h = (s % n + (r if r < n else 0)) % n if n > 1 else 0
    k = r if (r >= n and r < i) else 0
    return h, k % i if i > 1 else 0
E = {}
for a, b in combinations(range(52), 2):
    E[a, b] = [i for i in range(52) if act(a, i) == act(b, i)]
lb = {p: Fraction(len(e) * (len(e) - 1), 2652) for p, e in E.items()}
over = sorted((p for p in lb if lb[p] > Fraction(1, 64)), key=lambda p: -lb[p])
eq = [p for p in lb if suit(p[0]) + rank(p[0]) == suit(p[1]) + rank(p[1])]
print(f'pairs with lower bound > 1/64: {len(over)};  pairs with suit+rank equal: {len(eq)};  same set: {set(over) == set(eq)}')
rest = max((lb[p], p) for p in lb if p not in set(eq))
print(f'largest lower bound among pairs with suit+rank different: {rest[0]} = {float(rest[0]):.2e} ({NAME(rest[1][0])}<->{NAME(rest[1][1])}, e = {len(E[rest[1]])})')
print('\nclass v = suit+rank (clubs 0, hearts 1, spades 2, diamonds 3; A=1..K=13): pairs, e = |E|, closed-form lower bound')
for v in range(1, 17):
    cards = [c for c in range(52) if suit(c) + rank(c) == v]
    ps = [(a, b) for a, b in combinations(cards, 2)]
    if not ps: continue
    print(f'v={v:2d} cards {" ".join(NAME(c) for c in cards)}')
    for p in ps:
        e = E[p]; m = max(rank(p[0]), rank(p[1]))
        print(f'   {NAME(p[0])}<->{NAME(p[1])}  e={len(e):2d} (steps with hand > max rank {m}: {51 - m}; extra {len(e) - (51 - m)})  '
              f'LB = {lb[p].numerator}/{lb[p].denominator} = {float(lb[p]):.4f} = 1/{float(1 / lb[p]):.2f}')
print('\nall pairs sorted (for keysched.c):', ' '.join(f'{a},{b}' for a, b in over))
