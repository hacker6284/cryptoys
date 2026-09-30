"""Exact per-step move sets for 'deal suit + k cards off the top of the hand (reversed), put them under the hand,
then the unchanged rank cut with key-pile fallback'; deal count m = min(suit + k, hand size) ('min') or (suit + k) mod hand size ('mod').
For each k: pairs whose closed-form lower bound e(e-1)/2652 exceeds 1/64 (e = steps where the two cards make the
same move; see colliders.py for why the bound holds), the top pairs by bound, 2H<->AS, and the exact hand cost
(expected cards dealt per pass = sum over steps of E[min(suit + k, n)], the controller being uniform at each step
because every step is a bijection of fixed-size states).
usage: python3 dealk_exact.py"""
from itertools import combinations
from fractions import Fraction
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
NAME = lambda c: 'A23456789TJQK'[c % 13] + 'CHSD'[c // 13]
def rot(xs, k): k %= len(xs) if xs else 1; return xs[k:] + xs[:k]
def move(c, i, k, mod=False):
    if mod == 'kf': return move_kf(c, i, k)
    n = 51 - i; hand = list(range(n)); key = list(range(100, 100 + i)); r = rank(c)
    if k is None:                       # current F
        if n: hand = rot(hand, suit(c) % n)
    else:
        m = ((suit(c) + k) % n if n else 0) if mod else min(suit(c) + k, n); hand = rot(hand[:m][::-1] + hand[m:], m)
    if n and r < n: hand = rot(hand, r)
    elif i and r < i: key = rot(key, r)
    return tuple(hand), tuple(key)
def deal_under(xs, m): return rot(xs[:m][::-1] + xs[m:], m)
def move_kf(c, i, k):
    # key-pile fallback: deal suit + k under the hand if it is smaller than the hand, else under the key pile if smaller
    n = 51 - i; hand = list(range(n)); key = list(range(100, 100 + i)); r = rank(c); x = suit(c) + k
    if x < n: hand = deal_under(hand, x)
    elif x < i: key = deal_under(key, x)
    if n and r < n: hand = rot(hand, r)
    elif i and r < i: key = rot(key, r)
    return tuple(hand), tuple(key)
for k, mod in [(2, 'kf')] + [(None, False)] + [(k, False) for k in range(5)] + [(k, True) for k in range(5)]:
    lab = 'CUR' if k is None else f'k={k} ' + ({'kf': 'key-pile fallback'}.get(mod) or ('mod' if mod else 'min'))
    mv = {(c, i): move(c, i, k, mod) for c in range(52) for i in range(52)}
    lb = {}
    for a, b in combinations(range(52), 2):
        e = sum(mv[a, i] == mv[b, i] for i in range(52)); lb[a, b] = (e, Fraction(e * (e - 1), 2652))
    srt = sorted(lb, key=lambda p: -lb[p][1])
    over = [p for p in srt if lb[p][1] > Fraction(1, 64)]
    cost = (Fraction(0) if k is None else Fraction(sum(s + k for s in range(4)) * 52, 4) if mod == 'kf' else
            sum(Fraction(sum(((s + k) % n if n else 0) if mod else min(s + k, n) for s in range(4)), 4) for n in range(52)))
    print(f'{lab}: pairs with bound > 1/64: {len(over)};  pairs with e >= 2: {sum(lb[p][0] >= 2 for p in lb)};  '
          f'max bound {float(lb[srt[0]][1]):.4f}; 2H<->AS e={lb[14,26][0]};  expected cards dealt per pass {float(cost):.2f}')
    print('    top 5 by bound: ' + ' '.join(f'{NAME(a)}<->{NAME(b)}(e={lb[a,b][0]},{lb[a,b][1].numerator}/{lb[a,b][1].denominator}={float(lb[a,b][1]):.4f})' for a, b in srt[:5]))
