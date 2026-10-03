#!/usr/bin/env python3
"""(1) The projective mixed-addition script R7 IS the chord rule with every division saved in the bottom Z:
   run v = x2 Z - X, rise u = y2 Z - Y (slope = u/v);
   A  = u^2 Z - v^2 (v - X - Z)          = v^2 Z * (slope^2 + 1 - x1 - x2)      ("new x, on the v^2 Z scale")
   s  = v^2 X - A                         = v^2 Z * (x1 - x3)                    ("old x minus new x, same scale")
   X' = v A,  Y' = u s - v^3 Y,  Z' = v^3 Z   so X'/Z' = x3 and Y'/Z' = slope (x1 - x3) - y1 = y3.
   Checked here in PARI on random points of every tier.
(2) Independent re-check of the palindromic (type-II) basis cost for Toy (p = 47) and Serious (p = 359):
   beta_i beta_j = beta_{i+j} + beta_{|i-j|} with reflection beta_{p-i} = beta_i and beta_0 = 2 = sum of all beta_i
   ("a peg that lands on the anchor floods every hole"); verified against PARI, moves compared with Board.mul."""
import random, json
from ecbs_ref import TIERS, pari
import ecbs_exchange as X
from ecbs_pegs import Board, NEXT, PREV, MIRROR

def verse_check(name, reps=50):
    T = X.Tier(name); R = T.R; l = T.l; ok = 0
    for s_ in range(reps):
        P1 = R.mul(random.randrange(1, l), T.Pref); P2 = R.mul(random.randrange(1, l), T.Pref)
        x1, y1 = P1[0], P1[1]; x2, y2 = P2[0], P2[1]
        Z = R.w ** random.randrange(1, 3 ** 5) + 1
        Xp, Yp = x1 * Z, y1 * Z
        v = x2 * Z - Xp; u = y2 * Z - Yp
        A = u * u * Z - v * v * (v - Xp - Z)
        s = v * v * Xp - A
        X3, Y3, Z3 = v * A, u * s - v ** 3 * Yp, v ** 3 * Z
        lam = (y2 - y1) / (x2 - x1); x3 = lam ** 2 + 1 - x1 - x2; y3 = lam * (x1 - x3) - y1
        S = R.add(P1, P2)
        ok += (A == v * v * Z * (lam ** 2 + 1 - x1 - x2) and s == v * v * Z * (x1 - x3)
               and X3 / Z3 == x3 and Y3 / Z3 == y3 and pari([x3, y3]) == S)
    return ok, reps

def D_polys(n):
    x = pari('x'); D = [pari('Mod(2,3)'), x * pari('Mod(1,3)')]
    for i in range(1, n + 1): D.append(x * D[i] - D[i - 1])
    return D

def palin(n, reps=30):
    p = 2 * n + 1; D = D_polys(n)
    f = pari.lift(D[n + 1] - D[n]) * pari('Mod(1,3)')
    f = pari.divrem(f, pari('Mod(1,3)*(x-2)'))[0]
    irr = bool(pari.polisirreducible(f))
    w = pari.ffgen(f, 'b')
    beta = [pari.subst(pari.lift(D[i]), 'x', w) for i in range(n + 1)]
    val = lambda r: sum(({'W': 1, 'R': -1}[c]) * beta[i + 1] for i, c in enumerate(r) if c != '.') if any(c != '.' for c in r) else 0 * w
    refl = lambda k: k if k <= n else p - k
    def mul(a, b):
        out = ['.'] * n; anchor = '.'; moves = 0
        def drop(k, c):
            nonlocal anchor, moves
            moves += 1
            if k == 0: anchor = NEXT[anchor] if c == 'W' else PREV[anchor]
            else: out[k - 1] = NEXT[out[k - 1]] if c == 'W' else PREV[out[k - 1]]
        for j, cb in enumerate(b, 1):
            if cb == '.': continue
            for i, ca in enumerate(a, 1):
                if ca == '.': continue
                c = ca if cb == 'W' else MIRROR[ca]
                drop(refl(i + j), c); drop(abs(i - j), c)
        if anchor != '.':
            moves += 1
            for k in range(n): drop(k + 1, anchor)
        return out, moves
    rnd = random.Random(n); ok = 0; mv = 0
    for _ in range(reps):
        a = [rnd.choice('.WR') for _ in range(n)]; b = [rnd.choice('.WR') for _ in range(n)]
        r, m = mul(a, b); mv += m; ok += val(r) == val(a) * val(b)
    Bd = Board(n, TIERS["Toy" if n == 23 else "Serious"][1]); rnd = random.Random(n); m0 = 0
    for _ in range(reps):
        a = [rnd.choice('.WR') for _ in range(n)]; b = [rnd.choice('.WR') for _ in range(n)]
        s0 = Bd.moves; Bd.mul(a, b); m0 += Bd.moves - s0
    return dict(irreducible=irr, mul_ok=ok, reps=reps, moves=mv / reps, poly_moves=m0 / reps, ratio=mv / m0)

def main():
    random.seed(8); out = {}
    print("== 1. Verse = chord rule kept over a bottom (PARI, random points)")
    for name in TIERS:
        ok, reps = verse_check(name); out[name] = ok
        print(f"  {name}: {ok}/{reps} additions satisfy all five scale identities and equal PARI's sum")
    print("\n== 2. Palindromic type-II basis, independent re-check")
    for n in (23, 179):
        r = palin(n); out[f"palin{n}"] = r
        print(f"  n={n}: (D_(n+1) - D_n)/(x - 2) irreducible {r['irreducible']}; multiply correct {r['mul_ok']}/{r['reps']}; "
              f"mean moves {r['moves']:,.0f} vs polynomial basis {r['poly_moves']:,.0f} (x{r['ratio']:.2f})")
    json.dump(out, open("ecbs_verse.json", "w"), indent=1)

if __name__ == "__main__":
    main()
