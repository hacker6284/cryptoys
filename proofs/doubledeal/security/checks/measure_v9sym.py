"""T1 measurement: how often do the 51 nontrivial v9Sym(a, b) relabellings commute
with v9 GridCycle, one full round, and the full cipher; plus a distinguisher test
analogous to the v8 same-rank attack (attack/success_rate.py). Deterministic seeds.

Usage: python3 measure_v9sym.py [scale]   (scale=1 is the committed run)
"""
import random
import sys
from multiprocessing import Pool
import ddport as P
from dd_v8 import suit, rank, compose, expand_keys

SCALE = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0


def card(r, su): return su * 13 + (r - 1)


def sig9(a, b):
    s = [None] * 52
    for c in range(52):
        r, su = rank(c), suit(c)
        r2 = (r - 1 + a) % 13 + 1
        s[c] = card(r2, (su + b - (r2 - r)) % 4)
    return s


G = {(a, b): sig9(a, b) for a in range(13) for b in range(4) if (a, b) != (0, 0)}
def app(s, d): return [s[x] for x in d]
def deck(R): d = list(range(52)); R.shuffle(d); return d
def enc_keys(m, keys):
    m = compose(m, keys[0])
    for r in range(1, 6): m = P.full_round(m, keys[r], 9)
    return P.final_round(m, keys[6], 9)


def layer_job(args):
    (a, b), n_mix, n_round, n_enc = args
    s = G[(a, b)]
    R = random.Random(1000 * a + 10 * b + 1)
    mix = sum(P.mix_columns(app(s, m), 9) == app(s, P.mix_columns(m, 9)) for m in (deck(R) for _ in range(n_mix)))
    rnd = 0
    for _ in range(n_round):
        m, k = deck(R), deck(R)
        rnd += P.full_round(app(s, m), k, 9) == app(s, P.full_round(m, k, 9))
    enc = 0
    for i in range(n_enc):
        if i % 256 == 0: keys = expand_keys(deck(R))
        m = deck(R)
        enc += enc_keys(app(s, m), keys) == app(s, enc_keys(m, keys))
    return (a, b), mix, rnd, enc


def first_card_bound(a, b):
    """Per-deck GridCycle commuting needs seat2(s m0) == seat2(m0): only m0 in {K♣, K♠} with s swapping them."""
    s = G[(a, b)]
    KC, KS = card(13, 0), card(13, 2)
    return sum(1 for c in (KC, KS) if {c, s[c]} == {KC, KS}) / 52


MODES = ('suitrot', 'v9sym', 'control')


def dist_job(args):
    k, npairs, mode = args
    R = random.Random(9090 + 31 * k + 1000 * MODES.index(mode))
    keys = expand_keys(deck(R))
    hits = 0
    agree = 0
    for _ in range(npairs):
        if mode == 'suitrot': s = G[(0, 1)]
        elif mode == 'v9sym': s = G[R.choice(sorted(G))]
        else:
            s = deck(R)  # control: a random relabelling
        m = deck(R)
        c1, c2 = enc_keys(m, keys), enc_keys(app(s, m), keys)
        sc1 = app(s, c1)
        hits += c2 == sc1
        agree += sum(x == y for x, y in zip(c2, sc1))
    return mode, k, hits, agree


def enc01_job(args):
    i, n = args
    s = G[(0, 1)]
    R = random.Random(424242 + i)
    hits = 0
    for j in range(n):
        if j % 256 == 0: keys = expand_keys(deck(R))
        m = deck(R)
        hits += enc_keys(app(s, m), keys) == app(s, enc_keys(m, keys))
    return hits


if __name__ == '__main__':
    n_mix, n_round, n_enc = int(20000 * SCALE), int(4000 * SCALE), int(4000 * SCALE)
    n01 = int(1_000_000 * SCALE)
    nkeys, npairs = 24, int(16384 * SCALE)
    with Pool(8) as pool:
        res = pool.map(layer_job, [((a, b), n_mix, n_round, n_enc) for (a, b) in sorted(G)])
        print(f"# [A] per element: GridCycle on {n_mix} random decks, one full round on {n_round} "
              f"(deck, key) pairs, encrypt6 on {n_enc} (deck, random key) pairs")
        tot = [0, 0, 0]
        for (ab, mix, rnd, enc) in res:
            tot[0] += mix; tot[1] += rnd; tot[2] += enc
            print(f"v9Sym{ab}: GridCycle {mix}/{n_mix}  round {rnd}/{n_round}  encrypt {enc}/{n_enc}"
                  f"  (first-card bound {first_card_bound(*ab):.4f})")
        print(f"TOTAL (51 elements): GridCycle {tot[0]}/{51*n_mix}  round {tot[1]}/{51*n_round}  encrypt {tot[2]}/{51*n_enc}")
        h01 = sum(pool.map(enc01_job, [(i, n01 // 8) for i in range(8)]))
        print(f"# [B] suit rotation v9Sym(0,1), full cipher, random keys: {h01}/{n01 // 8 * 8} pairs satisfy E_K(sM) = sE_K(M)"
              f"  (95% upper bound {3 / (n01 // 8 * 8):.2e} if 0)")
        print(f"# [C] distinguisher, {nkeys} keys x {npairs} pairs ({2*npairs} queries/key); hit = E_K(sM) == sE_K(M);"
              f" agree = positions j with E_K(sM)[j] == s(E_K(M)[j]) (random baseline 1/52 = {1/52:.5f})")
        for mode in MODES:
            out = pool.map(dist_job, [(k, npairs, mode) for k in range(nkeys)])
            succ = sum(1 for _, _, h, _ in out if h > 0)
            hits = sum(h for _, _, h, _ in out)
            agree = sum(a for _, _, _, a in out) / (52 * nkeys * npairs)
            print(f"[{mode}] success={succ}/{nkeys} total_hits={hits} mean positional agreement={agree:.5f}")
