"""Lemma M on small decks, with ARBITRARY action tables.
Pass on an N-card deck: pop controller C (hand size n = N-1-k after the pop, key size m = k), cut the hand by
h_k(C) mod n and the key pile by g_k(C) mod m, put C on top of the key pile. Lemma M: a swap tau = (a b) survives
(pass(tau d) == tau pass(d)) only if both runs use the same action sequence. Here the tables h_k(c), g_k(c) are
random (not PassMix-F's), and every deck and every pair is checked exhaustively.
usage: python3 lemmaM_small.py [Nmax] [tables per N] [seed]"""
import sys, random, itertools
Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
T = int(sys.argv[2]) if len(sys.argv) > 2 else 30
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
def rotl(x, k): return x[k % len(x):] + x[:k % len(x)] if x else x
def run(d, H, G):
    hand, key, acts = list(d), [], []
    for k in range(len(d)):
        C = hand.pop(0); n, m = len(hand), len(key)
        h = H[k][C] % n if n else 0; g = G[k][C] % m if m else 0
        hand = rotl(hand, h); key = rotl(key, g); key.insert(0, C); acts.append((h, g))
    return key, acts
for N in range(3, Nmax + 1):
    exc = surv = checks = 0
    for t in range(T):
        H = [[rng.randrange(60) for _ in range(N)] for _ in range(N)]
        G = [[rng.randrange(60) for _ in range(N)] for _ in range(N)]
        for d in itertools.permutations(range(N)):
            o, A = run(d, H, G)
            for a in range(N):
                for b in range(a + 1, N):
                    sw = {a: b, b: a}
                    e = [sw.get(x, x) for x in d]
                    o2, A2 = run(e, H, G)
                    ok = o2 == [sw.get(x, x) for x in o]
                    surv += ok; checks += 1; exc += ok and A2 != A
    print(f'N={N}: {T} random action tables x {N}! decks x all pairs = {checks} checks; survivals {surv}; survive with different actions {exc}')
