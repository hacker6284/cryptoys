"""Python port of primitives/cipher/doubledeal/v9/doubledeal_v9.sudo (frozen, deprecated v9).

Analysis only. Standalone copy of the v9 path of proofs/doubledeal/security/checks/ddport.py
(A2 column weights rank+suit; B3 overflow scan from the blocked column), so this folder does
not depend on files that will move when a successor lands. check_vectors.py checks it against
the frozen vectors. `encrypt_stages` also returns the intermediate states that the Lean witness
package uses as hints (the kernel re-checks every one; this port is not trusted there).
"""
def suit(c): return c // 13
def rank(c): return c % 13 + 1
def colw(c): return rank(c) + suit(c)
def rotl(xs, k):
    n = len(xs)
    if n == 0: return list(xs)
    k %= n
    return list(xs[k:]) + list(xs[:k])
def lay_cm(d):
    g = [[-1] * 13 for _ in range(4)]
    for k in range(52): g[k % 4][k // 4] = d[k]
    return g
def scoop_cm(g): return [g[r][c] for c in range(13) for r in range(4)]
def scoop_rm(g): return [g[r][c] for r in range(4) for c in range(13)]
def sum_ranks(g):
    g = [row[:] for row in g]
    for i in range(4):
        g[i] = rotl(g[i], sum(rank(x) for x in g[i]) % 13)
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(colw(x) for x in col) % 4
        fresh = [col[(i - s) % 4] for i in range(4)]
        for i in range(4): g[i][j] = fresh[i]
    return g
def shift_rows(g): return [rotl(g[i], i) for i in range(4)]
def overflow_seat(occ, t, start):
    for _ in range(4):
        row = t
        for k in range(13):
            col = (start + k) % 13
            if not occ[row][col]: return row, col, (t + 1) % 4
        t = (t + 1) % 4
    raise AssertionError("grid full")
def walk(d):
    occ = [[False] * 13 for _ in range(4)]
    t = 0; seats = []
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            pc = d[i - 1]; pr, pcc = seats[-1]
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if not occ[tr][tc]: r, c = tr, tc
            else: r, c, t = overflow_seat(occ, t, tc)
        occ[r][c] = True; seats.append((r, c))
    return seats
def mix_columns(d):
    grid = [[-1] * 13 for _ in range(4)]
    for card, (r, c) in zip(d, walk(d)): grid[r][c] = card
    return scoop_rm(grid)
def compose(m, k):
    pos = [0] * 52
    for i, x in enumerate(k): pos[x] = i
    return [m[pos[j]] for j in range(52)]
def passkey(deck):
    hand = list(deck); key = []
    for _ in range(len(deck)):
        c = hand.pop(0)
        if hand:
            k = suit(c) % len(hand)
            if k > 0: hand = rotl(hand, k)
        if hand and rank(c) < len(hand): hand = rotl(hand, rank(c))
        elif key and rank(c) < len(key): key = rotl(key, rank(c))
        key = [c] + key
    return key
def expand_keys(k0, nr=6):
    keys = [list(k0)]
    for _ in range(nr): keys.append(passkey(keys[-1]))
    return keys
def stem(m): return scoop_cm(shift_rows(sum_ranks(lay_cm(m))))
def full_round(m, k): return compose(mix_columns(stem(m)), k)
def final_round(m, k): return compose(stem(m), k)
def encrypt_stages(m, k0):
    """[compose(m,K0), after full round 1..5, after final round] (last = ciphertext)."""
    keys = expand_keys(k0)
    s = [compose(m, keys[0])]
    for r in range(1, 6): s.append(full_round(s[-1], keys[r]))
    s.append(final_round(s[-1], keys[6]))
    return s
def encrypt(m, k0): return encrypt_stages(m, k0)[-1]
def swap(x, y): return lambda c: y if c == x else x if c == y else c
