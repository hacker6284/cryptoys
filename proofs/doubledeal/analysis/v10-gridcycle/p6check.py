"""Independent Python implementation (analysis only) of the Phase 6 anti-resync variants, written from the
rule text: an encryptor and a separate decryptor (the decryptor only reads the table, its visited marks,
the finger, the marker and the card it just recovered). Checks (1) decrypt(encrypt(d)) == d and (2)
encrypt(d) == cand.c's GridCycle output, on random decks.
Card c: suit c//13, rank c%13+1; seats (row, col), output index row*13+col; first card at (2, 0).
33 rule 1: ghost finger; next target = finger + (suit, rank) of the card just placed; if taken by blocker B:
   first free seat scanning right in row marker+suit(B) from column T.col+rank(B), next rows if full; marker +1.
60 A : column move = rank + finger row.        61 A': column move = rank * (finger row + 1).
62 B : after a blocked placement the finger goes to T + (suit(B), rank(B)) instead of T.
63 C : row move = suit + marker.               64 A+B.
usage: python3 p6check.py [decks]"""
import random, subprocess, sys

def target(V, f, t, p):
    s, rk = p // 13, p % 13 + 1
    row = (f[0] + s + (t if V == 63 else 0)) % 4
    if V in (60, 64): col = (f[1] + rk + f[0]) % 13
    elif V == 61: col = (f[1] + rk * (f[0] + 1)) % 13
    else: col = (f[1] + rk) % 13
    return (row, col)

def scan(taken, row, c0):
    for a in range(4):
        for q in range(13):
            s = ((row + a) % 4, (c0 + q) % 13)
            if s not in taken: return s

def after_block(V, T, B):
    """finger after a blocked placement at T with blocker B"""
    if V in (62, 64): return ((T[0] + B // 13) % 4, (T[1] + B % 13 + 1) % 13)
    return T

def encrypt(V, d):
    g = {(2, 0): d[0]}; f = (2, 0); t = 0
    for i in range(1, 52):
        T = target(V, f, t, d[i - 1])
        if T not in g:
            g[T] = d[i]; f = T
        else:
            B = g[T]; s = scan(g, (t + B // 13) % 4, (T[1] + B % 13 + 1) % 13)
            g[s] = d[i]; t = (t + 1) % 4; f = after_block(V, T, B)
    return [g[(k // 13, k % 13)] for k in range(52)]

def decrypt(V, out):
    G = {(k // 13, k % 13): out[k] for k in range(52)}
    seen = {(2, 0)}; hand = [G[(2, 0)]]; f = (2, 0); t = 0
    for i in range(1, 52):
        T = target(V, f, t, hand[-1])
        if T not in seen:
            s = T; f = T
        else:
            B = G[T]; s = scan(seen, (t + B // 13) % 4, (T[1] + B % 13 + 1) % 13); t = (t + 1) % 4; f = after_block(V, T, B)
        seen.add(s); hand.append(G[s])
    return hand

n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
rng = random.Random(3)
decks = [rng.sample(range(52), 52) for _ in range(n)]
for V in (33, 60, 61, 62, 63, 64):
    res = subprocess.run(['./cand', str(V), 'x', '0', '0'], input='\n'.join(' '.join(map(str, d)) for d in decks) + '\n',
                         capture_output=True, text=True, check=True).stdout.strip().split('\n')
    mism = sum(list(map(int, res[k].split('|')[1].split())) != encrypt(V, d) for k, d in enumerate(decks))
    rt = sum(decrypt(V, encrypt(V, d)) != d for d in decks)
    print(f'variant {V}: {n} decks: output mismatches vs cand.c {mism}; Python round-trip failures {rt}')
    assert mism == 0 and rt == 0
