"""Faithful Python port of primitives/cipher/doubledeal/doubledeal.sudo (analysis only)."""
from math import factorial
def suit(c): return c // 13
def rank(c): return c % 13 + 1
def rotl(xs, k):
    n = len(xs)
    if n == 0: return list(xs)
    k %= n
    return list(xs[k:]) + list(xs[:k])
def rotr(xs, k):
    n = len(xs)
    if n == 0: return list(xs)
    k %= n
    return rotl(xs, n - k) if k else list(xs)
def lay_cm(d):
    g = [[-1]*13 for _ in range(4)]
    for k in range(52): g[k % 4][k // 4] = d[k]
    return g
def scoop_cm(g): return [g[r][c] for c in range(13) for r in range(4)]
def lay_rm(d): return [list(d[13*i:13*i+13]) for i in range(4)]
def scoop_rm(g): return [g[r][c] for r in range(4) for c in range(13)]
def sum_ranks(g, stats=None):
    g = [row[:] for row in g]
    for i in range(4):
        g[i] = rotl(g[i], sum(rank(x) for x in g[i]) % 13)
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(rank(x) for x in col) % 4
        fresh = [col[(i - s) % 4] for i in range(4)]
        for i in range(4): g[i][j] = fresh[i]
    return g
def inv_sum_ranks(g):
    g = [row[:] for row in g]
    for j in range(13):
        col = [g[i][j] for i in range(4)]
        s = sum(rank(x) for x in col) % 4
        fresh = [col[(i + s) % 4] for i in range(4)]
        for i in range(4): g[i][j] = fresh[i]
    for i in range(4):
        g[i] = rotl(g[i], -(sum(rank(x) for x in g[i]) % 13))
    return g
def shift_rows(g): return [rotl(g[i], i) for i in range(4)]
def inv_shift_rows(g): return [rotl(g[i], -i) for i in range(4)]
def overflow_seat(occ, t):
    for _ in range(4):
        row = t
        for col in range(13):
            if not occ[row][col]: return row, col, (t + 1) % 4
        t = (t + 1) % 4
    raise AssertionError
def mix_columns(d, info=None):
    grid = [[-1]*13 for _ in range(4)]
    t = 0; pc = pr = pcc = 0; nover = 0
    for i in range(52):
        card = d[i]; r, c = 2, 0
        if i > 0:
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if grid[tr][tc] < 0: r, c = tr, tc
            else:
                occ = [[grid[a][b] >= 0 for b in range(13)] for a in range(4)]
                r, c, t = overflow_seat(occ, t); nover += 1
        grid[r][c] = card; pc, pr, pcc = card, r, c
    if info is not None: info['overflows'] = nover
    return scoop_rm(grid)
def inv_mix_columns(d):
    grid = lay_rm(d); vis = [[False]*13 for _ in range(4)]
    t = 0; hand = []; pc = pr = pcc = 0
    for i in range(52):
        r, c = 2, 0
        if i > 0:
            tr, tc = (pr + suit(pc)) % 4, (pcc + rank(pc)) % 13
            if not vis[tr][tc]: r, c = tr, tc
            else: r, c, t = overflow_seat(vis, t)
        hand.append(grid[r][c]); vis[r][c] = True
        pc, pr, pcc = hand[-1], r, c
    return hand
def compose(m, k):
    pos = [0]*52
    for i, x in enumerate(k): pos[x] = i
    return [m[pos[j]] for j in range(52)]
def inverse_compose(c, k):
    out = [0]*52
    for j in range(52): out[k.index(j)] = c[j]
    return out
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
def passkey_inv(deck):
    key = list(deck); hand = []
    for _ in range(len(deck)):
        c = key.pop(0); n = len(hand)
        if n > 0 and rank(c) < n: hand = rotr(hand, rank(c))
        elif key and rank(c) < len(key): key = rotr(key, rank(c))
        if n > 0:
            k = suit(c) % n
            if k > 0: hand = rotr(hand, k)
        hand = [c] + hand
    return hand
def expand_keys(k0, nr=6):
    keys = [list(k0)]
    for _ in range(nr): keys.append(passkey(keys[-1]))
    return keys
def unkeyed_stem(m): return scoop_cm(shift_rows(sum_ranks(lay_cm(m))))
def unkeyed_full(m): return mix_columns(unkeyed_stem(m))
def full_round(m, k): return compose(unkeyed_full(m), k)
def final_round(m, k): return compose(unkeyed_stem(m), k)
def inv_full_round(c, k):
    m = inv_mix_columns(inverse_compose(c, k))
    return scoop_cm(inv_sum_ranks(inv_shift_rows(lay_cm(m))))
def inv_final_round(c, k):
    m = inverse_compose(c, k)
    return scoop_cm(inv_sum_ranks(inv_shift_rows(lay_cm(m))))
def encrypt_keys(m, keys, nfull=5, final=True):
    m = compose(m, keys[0])
    for r in range(1, nfull + 1): m = full_round(m, keys[r])
    return final_round(m, keys[nfull + 1]) if final else m
def encrypt(m, k0): return encrypt_keys(m, expand_keys(k0))
def decrypt(c, k0):
    keys = expand_keys(k0)
    m = inv_final_round(c, keys[6])
    for r in range(5, 0, -1): m = inv_full_round(m, keys[r])
    return inverse_compose(m, keys[0])
def unrank(items, r):
    items = list(items); r %= factorial(len(items)); out = []
    for k in range(len(items), 0, -1):
        f = factorial(k - 1); out.append(items.pop(r // f)); r %= f
    return out
def counter_deck(nonce, i):
    assert len(nonce) == 39
    return list(nonce) + unrank(list(range(39, 52)), i)
def ctr_encrypt(blocks, key, nonce):
    return [compose(b, encrypt(counter_deck(nonce, i), key)) for i, b in enumerate(blocks)]
def ecb_encrypt(blocks, key): return [encrypt(b, key) for b in blocks]
# permutation helpers: deck D as function seat->card
def perm_sign(p):
    seen = [False]*len(p); s = 1
    for i in range(len(p)):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]: seen[j] = True; j = p[j]; L += 1
            if L % 2 == 0: s = -s
    return s
