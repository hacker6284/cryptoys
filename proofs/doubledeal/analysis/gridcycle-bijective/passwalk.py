"""PassMix-F walkthrough (forward and decrypt) on one seeded deck, written from the README rule text.
usage: python3 passwalk.py SEED"""
import sys, random
NAME = lambda c: 'A23456789TJQK'[c % 13] + 'CHSD'[c // 13]
suit = lambda c: c // 13; rank = lambda c: c % 13 + 1
def rotl(x, k): return x[k % len(x):] + x[:k % len(x)] if x else x
def show(p, k=6): return ' '.join(NAME(c) for c in p[:k]) + (' ...' if len(p) > k else '')
def fwd(d, log):
    hand, key = list(d), []
    for step in range(52):
        C = hand.pop(0); n, m = len(hand), len(key)
        if rank(C) < n: hc, kc, how = rank(C), suit(C), f'rank {rank(C)} < hand {n}: cut hand {rank(C)}, key pile {suit(C)}'
        else: hc, kc, how = suit(C), rank(C), f'rank {rank(C)} >= hand {n}: FALLBACK cut key pile {rank(C)}, hand {suit(C)}'
        hand = rotl(hand, hc); key = rotl(key, kc); key.insert(0, C)
        if step < 5 or step > 47: log(f'{step:2d} {NAME(C)}: {how}  -> hand [{show(hand)}]  key [{show(key)}]')
        elif step == 5: log('   ...')
    return key
def inv(o, log):
    key, hand = list(o), []
    for step in range(51, -1, -1):
        C = key.pop(0); n, m = len(hand), len(key)
        if rank(C) < n: hc, kc, how = rank(C), suit(C), f'rank {rank(C)} < hand {n}: uncut key pile {suit(C)}, hand {rank(C)}'
        else: hc, kc, how = suit(C), rank(C), f'rank {rank(C)} >= hand {n}: uncut key pile {rank(C)}, hand {suit(C)}'
        key = rotl(key, -kc); hand = rotl(hand, -hc); hand.insert(0, C)
        if step > 48 or step < 3: log(f'{step:2d} lift {NAME(C)}: {how} (bottom cards back to top) -> hand [{show(hand)}]')
        elif step == 48: log('   ...')
    return hand
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
d = list(range(52)); random.Random(seed).shuffle(d)
print('input (top first):', ' '.join(NAME(c) for c in d))
print('forward (cut = move that many cards from top to bottom; counts wrap round a short pile):')
o = fwd(d, print)
print('output (top first):', ' '.join(NAME(c) for c in o))
print('decrypt (lift the top card of the key pile; undo its two cuts; put it on top of the hand):')
back = inv(o, print)
print('round trip ok:', back == d)
