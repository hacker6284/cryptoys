# Exact 4-card toy check of the M8b identities (DoubleDealSecurity/LinearMasks.lean), on S_4
# instead of S_52. Pure Python, exact integer arithmetic, fixed seed; a few seconds.
# This checks the TOY, not the Lean: the same-shape identities on S_4, not the Lean
# statements or proofs.
#
# Toy cipher and conventions as in toy_link.py (shape of FullCipher.encryptL n: n rounds of
# (Compose, U), then (Compose, V, Compose); U, V random bijections of the 4! decks; Compose
# is x∘k; a relabelling acts on card values). N = 4 plays the role of 52.
#
# Checked:
#   L5  autoCorr_cardMask          A(mask_{s,c}, a) = N! (N [a c = c] - 1), all s, c, a
#   L9-shape                       for every fixed-point-free a: A(mask_{s,c}, a) = -N!
#   rows/columns                   sum_b fullDiffCount(a,b) = sum_a fullDiffCount(a,b) = N!^(n+2)
#   L7  alignCount_eq              alignCount(c,c') = #{(a, L) | c same seat in (y, a y),
#                                                    c' same seat in (E y, E (a y))}
#   L6  fullSumSqCorr_cardMask     sum_L corr^2 = N! (N^2 alignCount - N!^(n+3))
#       (and, from it, that the seats s, t do not matter: fullSumSqCorr_cardMask_seat)
#   L7 and L6 are checked for 3 card pairs (c, c') = (0,0), (1,3), (2,1), and L6 for
#   3 seat pairs (s, t) = (0,0), (1,2), (3,1) each, with n = 0, 1 (not all s, c, t, c').
#   L10 corr_keyedLayer_sign       corr(k-layer, sgn, sgn) = sgn k1 sgn k2 corr(U, sgn, sgn),
#                                  all k1, k2, for U and for V
import itertools, random
from math import factorial

N = 4
random.seed(8)
P = list(itertools.permutations(range(N)))
M = len(P)
ONE = tuple(range(N))
comp = lambda x, k: tuple(x[k[j]] for j in range(N))
rel = lambda a, x: tuple(a[x[i]] for i in range(N))

def randbij():
    q = P[:]; random.shuffle(q); return dict(zip(P, q))

U = randbij(); V = randbij()

def enc(n, x, L):
    for k in L[:n]:
        x = U[comp(x, k)]
    return comp(V[comp(x, L[n])], L[n + 1])

def sgn(p):
    s, seen = 1, [False] * N
    for i in range(N):
        if not seen[i]:
            j, l = i, 0
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            if l % 2 == 0: s = -s
    return s

mask = lambda s, c: {x: N * (x[s] == c) - 1 for x in P}
A = lambda f, a: sum(f[x] * f[rel(a, x)] for x in P)
corr = lambda E, f, g: sum(f[x] * g[E(x)] for x in P)
same_seat = lambda c, z, w: all((z[i] == c) == (w[i] == c) for i in range(N))

ok = True
def check(name, good):
    global ok
    ok &= good
    print(f"{name}: {good}")

check("L5 autoCorr_cardMask, all s, c, a",
      all(A(mask(s, c), a) == M * (N * (a[c] == c) - 1)
          for s in range(N) for c in range(N) for a in P))
ffree = [a for a in P if all(a[c] != c for c in range(N))]
check(f"L9-shape: A(mask, a) = -N! for all {len(ffree)} fixed-point-free a",
      all(A(mask(s, c), a) == -M for s in range(N) for c in range(N) for a in ffree))

for n in (0, 1):
    keys = list(itertools.product(P, repeat=n + 2))
    y = P[5]
    D = {}
    for a in P:
        for L in keys:
            e, e2 = enc(n, y, L), enc(n, rel(a, y), L)
            b = [0] * N
            for i in range(N):
                b[e[i]] = e2[i]
            D[(a, tuple(b))] = D.get((a, tuple(b)), 0) + 1
    Dc = lambda a, b: D.get((a, b), 0)
    check(f"rows and columns sum to N!^(n+2), n={n}",
          all(sum(Dc(a, b) for b in P) == M ** (n + 2) for a in P) and
          all(sum(Dc(a, b) for a in P) == M ** (n + 2) for b in P))
    for c, c2 in ((0, 0), (1, 3), (2, 1)):
        align = sum(Dc(a, b) for a in P if a[c] == c for b in P if b[c2] == c2)
        direct = sum(1 for a in P for L in keys
                     if same_seat(c, y, rel(a, y))
                     and same_seat(c2, enc(n, y, L), enc(n, rel(a, y), L)))
        check(f"L7 alignCount_eq n={n} c={c} c'={c2}: {align} == {direct}", align == direct)
        vals = set()
        for s, t in ((0, 0), (1, 2), (3, 1)):
            f, g = mask(s, c), mask(t, c2)
            S = sum(corr(lambda x: enc(n, x, L), f, g) ** 2 for L in keys)
            vals.add(S)
            check(f"L6 fullSumSqCorr_cardMask n={n} s={s} c={c} t={t} c'={c2}: {S}",
                  S == M * (N * N * align - M ** (n + 3)))
        check(f"L6 seats do not matter n={n} c={c} c'={c2}", len(vals) == 1)

sg = {x: sgn(x) for x in P}
for nm, W in (("U", U), ("V", V)):
    c0 = corr(lambda x: W[x], sg, sg)
    check(f"L10 corr_keyedLayer_sign ({nm}), corr(W, sgn, sgn) = {c0}, all (k1, k2)",
          all(corr(lambda x: comp(W[comp(x, k1)], k2), sg, sg) == sgn(k1) * sgn(k2) * c0
              for k1 in P for k2 in P))

print("ALL M8b TOY IDENTITIES HOLD" if ok else "SOME CHECK FAILED")
raise SystemExit(0 if ok else 1)
