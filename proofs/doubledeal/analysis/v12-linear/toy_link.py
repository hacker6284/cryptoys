# Exact 4-card toy check of the M8a identities (DoubleDealSecurity/Linear.lean), on S_4
# instead of S_52. Pure Python, exact integer / Fraction arithmetic, fixed seed; ~6 s.
#
# The toy cipher has the shape of FullCipher.encryptL n: n mix rounds (Compose L_i, then an
# unkeyed layer U), then the finalRound step (Compose L_n, an unkeyed layer V, Compose L_{n+1}).
# U and V are arbitrary (random) bijections of the 4! decks: the identities are generic.
# Conventions as in Lean: Compose is x∘k (composeVec: (x∘k)[j] = x[k[j]]); a relabelling α
# acts on card values ((α·x)[i] = α[x[i]]).
#
# Checked (each for random integer f, g and every deck y where a deck is needed):
#   L1 sumSqCorrU_eq       sum_{k1,k2} corr^2 = sum_{a,b} A_f(a) dpCount_U(a,b) A_g(b)
#   L2 sumSqCorr_eq        N! * sum_L corr^2 = sum_{a,b} A_f(a) fullDiffCount(a,b,n,y) A_g(b)
#   L3 sumSqCorr_eq_final  sum_L corr^2 = sum_{a,b} A_f(a) diffCount(a,b,n,y) sum_c dpF(b,c) A_g(c)
#   L4 sumSqCorr_split     N! * sum_L corr^2 = N!^(n+2) A_f(1) A_g(1) + sum_{a,b != 1} ...
#   fullDiffCount_eq_of_isDeck, fullDiffCount_one_left, fullDiffCount_to_one
# Not a Lean statement (documents the header's "does not apply to the real schedule"):
#   with a DEPENDENT toy schedule L = (k, F k, F(F k)) the L2-shaped equation fails.
# Not formalised (M8b scope, recorded here only): first-order masks f = N[x(s)=c] - 1.
import itertools, random
from fractions import Fraction
from math import factorial

N = 4
random.seed(7)
P = list(itertools.permutations(range(N)))
M = len(P)
ONE = tuple(range(N))
comp = lambda x, k: tuple(x[k[j]] for j in range(N))       # Compose (right multiplication)
rel = lambda a, x: tuple(a[x[i]] for i in range(N))         # relabel (left multiplication)

def randbij():
    q = P[:]; random.shuffle(q); return dict(zip(P, q))

U = randbij(); V = randbij()

def rounds(x, K):                     # TrailBound.rounds with U as the unkeyed round
    for k in K:
        x = U[comp(x, k)]
    return x

def enc(n, x, L):                     # FullCipher.encryptL: rounds, then the finalRound step
    return comp(V[comp(rounds(x, L[:n]), L[n])], L[n + 1])

def A(f, a):
    return sum(f[x] * f[rel(a, x)] for x in P)

def corr(E, f, g):
    return sum(f[x] * g[E(x)] for x in P)

def dpCount(W, a, b):
    return sum(1 for x in P if W[rel(a, x)] == rel(b, W[x]))

def diffCount(a, b, n, y):
    return sum(1 for K in itertools.product(P, repeat=n)
               if rounds(rel(a, y), K) == rel(b, rounds(y, K)))

def fullDiffCount(a, b, n, y, keys):
    return sum(1 for L in keys if enc(n, rel(a, y), L) == rel(b, enc(n, y, L)))

def fullDiff_row(a, n, y, keys):      # all b at once
    row = {}
    for L in keys:
        e, e2 = enc(n, y, L), enc(n, rel(a, y), L)
        b = [0] * N
        for i in range(N):
            b[e[i]] = e2[i]
        b = tuple(b); row[b] = row.get(b, 0) + 1
    return row

def rnd():
    return {x: random.randint(-3, 3) for x in P}

ok = True
def check(name, lhs, rhs):
    global ok
    good = lhs == rhs
    ok &= good
    print(f"{name}: {lhs} {'==' if good else '!='} {rhs}")

# L1, for U and for V
for W, nm in ((U, "U"), (V, "V")):
    dp = {(a, b): dpCount(W, a, b) for a in P for b in P}
    for _ in range(2):
        f, g = rnd(), rnd()
        lhs = sum(corr(lambda x: comp(W[comp(x, k1)], k2), f, g) ** 2 for k1 in P for k2 in P)
        rhs = sum(A(f, a) * dp[(a, b)] * A(g, b) for a in P for b in P)
        check(f"L1 sumSqCorrU_eq ({nm})", lhs, rhs)

dpF = {(a, b): dpCount(V, a, b) for a in P for b in P}
for n in (0, 1):
    keys = list(itertools.product(P, repeat=n + 2))
    y0 = P[5]
    D = {a: fullDiff_row(a, n, y0, keys) for a in P}
    Dc = lambda a, b: D[a].get(b, 0)
    # deck independence, one-left, to-one
    for y in (P[0], P[17], P[23]):
        for a in P[:6]:
            row = fullDiff_row(a, n, y, keys)
            if any(row.get(b, 0) != Dc(a, b) for b in P):
                ok = False; print("fullDiffCount_eq_of_isDeck FAILED", n, y, a)
    print(f"fullDiffCount_eq_of_isDeck n={n}: rows of 6 differences agree on 3 more decks:", ok)
    check(f"fullDiffCount_one_left n={n}", [Dc(ONE, b) for b in P],
          [M ** (n + 2) if b == ONE else 0 for b in P])
    check(f"fullDiffCount_to_one n={n}", [Dc(a, ONE) for a in P if a != ONE],
          [0] * (M - 1))
    dc = {(a, b): diffCount(a, b, n, y0) for a in P for b in P}
    for _ in range(2):
        f, g = rnd(), rnd()
        S = sum(corr(lambda x: enc(n, x, L), f, g) ** 2 for L in keys)
        check(f"L2 sumSqCorr_eq n={n}", M * S,
              sum(A(f, a) * Dc(a, b) * A(g, b) for a in P for b in P))
        check(f"L3 sumSqCorr_eq_final n={n}", S,
              sum(A(f, a) * dc[(a, b)] * sum(dpF[(b, c)] * A(g, c) for c in P)
                  for a in P for b in P))
        check(f"L4 sumSqCorr_split n={n}", M * S,
              M ** (n + 2) * A(f, ONE) * A(g, ONE) +
              sum(A(f, a) * Dc(a, b) * A(g, b) for a in P if a != ONE for b in P if b != ONE))

# Dependent toy schedule (NOT the Lean model): L = (k, F k, F(F k)), n = 1, one master key k.
F = randbij()
dkeys = [(k, F[k], F[F[k]]) for k in P]
Dd = {a: fullDiff_row(a, 1, P[5], dkeys) for a in P}
print("dependent schedule (expected to FAIL, documents the header's limit):")
for _ in range(3):
    f, g = rnd(), rnd()
    S = sum(corr(lambda x: enc(1, x, L), f, g) ** 2 for L in dkeys)
    R = Fraction(sum(A(f, a) * Dd[a].get(b, 0) * A(g, b) for a in P for b in P), M)
    print(f"  sum_k corr^2 = {S}, (1/N!) sum A D A = {R}, equal: {S == R}")

# First-order masks (M8b scope; not formalised): with f = N[x(s)=c] - 1, g = N[x(t)=c'] - 1,
# the key-averaged normalised squared correlation equals (N/(N-1)^2)(q - 1/N), where
# q = sum_{a(c)=c} sum_{b(c')=c'} D(a,b) / (#{a : a(c)=c} * #keys), for every seat s, t.
print("first-order masks (not formalised):")
keys = list(itertools.product(P, repeat=3))
D1 = {a: fullDiff_row(a, 1, P[5], keys) for a in P}
for (s, c, t, c2) in [(0, 0, 0, 0), (1, 0, 3, 0), (2, 1, 0, 3), (3, 2, 1, 1)]:
    f = {x: N * (x[s] == c) - 1 for x in P}; g = {x: N * (x[t] == c2) - 1 for x in P}
    Sf = sum(v * v for v in f.values()); Sg = sum(v * v for v in g.values())
    pot = Fraction(sum(corr(lambda x: enc(1, x, L), f, g) ** 2 for L in keys), len(keys) * Sf * Sg)
    stab = [a for a in P if a[c] == c]
    q = Fraction(sum(D1[a].get(b, 0) for a in stab for b in P if b[c2] == c2),
                 len(stab) * len(keys))
    pred = Fraction(N, (N - 1) ** 2) * (q - Fraction(1, N))
    print(f"  s={s} c={c} -> t={t} c'={c2}: potential {pot} vs {pred}")

print("ALL M8a IDENTITIES HOLD" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
