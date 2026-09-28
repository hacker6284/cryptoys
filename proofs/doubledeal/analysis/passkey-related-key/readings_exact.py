"""Exact step-move sets for the DEALB reading (deal x = suit cards off the hand, reversed, under the hand; then the
rank cut with fallback), compared with the current F. Two controllers make the same move at step i iff they induce
the same permutation of (hand, key) seats. Lower bound as in colliders.py: e(e-1)/2652.
usage: python3 readings_exact.py"""
from itertools import combinations
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
NAME = lambda c: 'A23456789TJQK'[c % 13] + 'CHSD'[c // 13]
def rot(xs, k): k %= len(xs) if xs else 1; return xs[k:] + xs[:k]
def move(c, i, dealb):
    n = 51 - i; hand = list(range(n)); key = list(range(100, 100 + i)); x, r = suit(c), rank(c)
    if dealb: m = min(x, n); hand = rot(hand[:m][::-1] + hand[m:], m)
    elif n: hand = rot(hand, x % n)
    if n and r < n: hand = rot(hand, r)
    elif i and r < i: key = rot(key, r)
    return tuple(hand), tuple(key)
for label, dealb in (('CUR', False), ('DEALB', True)):
    lb = {}
    for a, b in combinations(range(52), 2):
        e = sum(move(a, i, dealb) == move(b, i, dealb) for i in range(52)); lb[a, b] = (e, e * (e - 1) / 2652)
    over = sorted((p for p in lb if lb[p][1] > 1 / 64), key=lambda p: -lb[p][1])
    print(f'{label}: pairs with closed-form lower bound > 1/64: {len(over)}: ' + ' '.join(f'{NAME(a)}<->{NAME(b)}(e={lb[a,b][0]},{lb[a,b][1]:.4f})' for a, b in over))
    print(f'   2H<->AS: e = {lb[14, 26][0]}, lower bound {lb[14, 26][1]:.5f}')
