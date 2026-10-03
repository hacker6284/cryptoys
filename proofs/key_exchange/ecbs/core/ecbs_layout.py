#!/usr/bin/env python3
"""Visual layout + cursor-ship recipes for ECBS (no printed rulebook edition).

Every register is a BAND of rows on a tower of 10-column grids laid end to end.  The register length
n "reads as rows.holes": floor(n/10) full rows then (n mod 10) holes; the rest of the band is a gap.
  Demo 7 = 0 rows + 7 holes (band 1 row), Toy 23 = 2 rows + 3 (band 3 rows),
  Hobby 59 = 5 rows + 9 (band 6 rows, "one hole short"), Serious 179 = 17 rows + 9 (band 18 rows, "one hole short").
Overflow areas are further bands of the same shape directly BELOW the destination band.

The recipes below move cursor ships using only these physical moves:
  step on / step back (reading order; at the end of a band's holes jump to the next band's first hole),
  "same place" in another band (same row-in-band and column), "r rows up" (same column),
and they are checked against the index arithmetic of ecbs_pegs.Board (which is checked against PARI).
Also: exhaustive search for fold trinomials x^n = s1 x^k + s0 whose n-k is a whole number of rows,
Gaussian normal bases, and the proof-by-code that no rigid motion of holes can be a polynomial-basis cube."""
import random, json, sys
from ecbs_pegs import Board, MIRROR, NEXT, PREV
from ecbs_ref import TIERS, pari

W = 10
class Tower:
    def __init__(self, n, k):
        self.n, self.k = n, k
        self.H = -(-n // W)                       # band height in rows
        self.gap = self.H * W - n
    # physical coordinates: (global row, column); band b covers rows b*H .. b*H+H-1
    def first(self, band): return (band * self.H, 0)
    def band_of(self, pos): return pos[0] // self.H
    def in_register(self, pos):
        r, c = pos; rr = r % self.H
        return rr * W + c < self.n                # a gap hole is at/after rows.holes
    def step_on(self, pos):
        r, c = pos
        c += 1
        if c == W: r, c = r + 1, 0
        if (r % self.H == 0 and c == 0 and (r, c) != pos) or not self.in_register((r, c)):
            b = self.band_of(pos); return self.first(b + 1)     # gap reached -> next band's first hole
        return (r, c)
    def step_back(self, pos):
        r, c = pos
        if r % self.H == 0 and c == 0:             # first hole of a band -> last register hole of band above
            b = self.band_of(pos) - 1
            last = self.n - 1
            return (b * self.H + last // W, last % W)
        c -= 1
        if c < 0: r, c = r - 1, W - 1
        return (r, c)
    def same_place(self, pos, band):
        return (band * self.H + pos[0] % self.H, pos[1])
    def rows_up(self, pos, r): return (pos[0] - r, pos[1])
    # bookkeeping only (used to CHECK the physical recipes, never by them)
    def index(self, pos, base_band):
        r, c = pos; b = self.band_of(pos)
        return (b - base_band) * self.n + (r % self.H) * W + c

class Grid:
    """a dict of pegs keyed by physical position"""
    def __init__(self): self.h = {}; self.moves = 0; self.ship_steps = 0
    def get(self, p): return self.h.get(p, '.')
    def drop(self, p, colour, mirror=False):
        if colour == '.': return
        if mirror: colour = MIRROR[colour]
        cur = self.get(p); new = NEXT[cur] if colour == 'W' else PREV[cur]
        if new == '.': self.h.pop(p, None)
        else: self.h[p] = new
        self.moves += 1
    def lift(self, p): c = self.h.pop(p); self.moves += 1; return c
    def put(self, T, band, reg):
        pos = T.first(band)
        for c in reg:
            if c != '.': self.h[pos] = c
            pos = T.step_on(pos)
    def read(self, T, band, length=None):
        out = []; pos = T.first(band)
        for _ in range(length or T.n): out.append(self.get(pos)); pos = T.step_on(pos)
        return out

def fold_rule(T):
    """the cruiser's start relative to the carrier: 'r rows up' if n-k is a multiple of 10 and the
       carrier's start row allows it, else 'd holes back' (Demo)."""
    d = T.n - T.k
    return ('rows', d // W) if d % W == 0 else ('holes', d)

def v_fold(G, T, dst_band, top_band):
    """carrier on the last register hole of the top overflow band; battleship at the same place one band
       up; cruiser r rows up (or d holes back).  Step all three back together until the carrier enters
       the destination band.  At each carrier peg: lift, drop at battleship and at cruiser."""
    kind, amt = fold_rule(T)
    last = T.n - 1
    car = (top_band * T.H + last // W, last % W)
    bat = T.same_place(car, top_band - 1)
    if kind == 'rows':
        cru = T.rows_up(car, amt)
        assert T.band_of(cru) == top_band and T.in_register(cru), "cruiser start must be inside the top band"
    else:
        cru = car
        for _ in range(amt): cru = T.step_back(cru)
    # check the pictures against index arithmetic
    assert T.index(bat, dst_band) == T.index(car, dst_band) - T.n
    assert T.index(cru, dst_band) == T.index(car, dst_band) - (T.n - T.k)
    while T.band_of(car) > dst_band:
        c = G.get(car)
        if c != '.':
            G.lift(car); G.drop(bat, c); G.drop(cru, c)
        car, bat, cru = T.step_back(car), T.step_back(bat), T.step_back(cru); G.ship_steps += 3

def v_mul(G, T, a_band, b_band, d_band):
    """D (+)= A*B: for each peg of B (highest first, lifted): strip ship at the same place in D's band,
       A ship on A's first hole; step both on together; drop A's pegs (mirrored if B's peg is red).
       Then fold (overflow = the band below D)."""
    # B's pegs, highest first: scan from B's last hole back (visible: the highest remaining peg)
    pos = T.first(b_band)
    posl = []
    for _ in range(T.n): posl.append(pos); pos = T.step_on(pos)
    for bp in reversed(posl):
        c = G.get(bp)
        if c == '.': continue
        G.lift(bp)
        s = T.same_place(bp, d_band); a = T.first(a_band)
        for _ in range(T.n):
            G.drop(s, G.get(a), mirror=(c == 'R'))
            s = T.step_on(s); a = T.step_on(a); G.ship_steps += 2
    v_fold(G, T, d_band, d_band + 1)

def v_cube(G, T, a_band, d_band):
    """fresh D + 2 overflow bands below it.  Input ship on A's first hole, landing ship on D's first hole.
       Input ship steps 1 hole, landing ship hops 3 ("over two"); a peg under the input ship jumps to
       the landing ship.  Then fold from the lower overflow band."""
    a = T.first(a_band); d = T.first(d_band)
    for i in range(T.n):
        c = G.get(a)
        if c != '.': G.lift(a); G.drop(d, c)
        a = T.step_on(a)
        if i < T.n - 1:
            for _ in range(3): d = T.step_on(d)
        G.ship_steps += 4
    v_fold(G, T, d_band, d_band + 2)

def v_add(G, T, a_band, d_band, mirror=False):
    a, d = T.first(a_band), T.first(d_band)
    for _ in range(T.n):
        G.drop(d, G.get(a), mirror); a, d = T.step_on(a), T.step_on(d); G.ship_steps += 2

def check_cursors(name, rnd, reps=30):
    n, k, _ = TIERS[name]; T = Tower(n, k); B = Board(n, k); ok = [0, 0, 0]
    for _ in range(reps):
        A = [rnd.choice('.WR') for _ in range(n)]; Bv = [rnd.choice('.WR') for _ in range(n)]
        D0 = [rnd.choice('.WR') for _ in range(n)]
        G = Grid(); G.put(T, 0, A); G.put(T, 1, Bv); G.put(T, 2, D0)
        v_mul(G, T, 0, 1, 2)
        want = B.mul(A, Bv); B.add_into(want, D0)
        ok[0] += G.read(T, 2) == want and G.read(T, 1) == ['.'] * n and all(G.get(p) == '.' for p in G.h if T.band_of(p) >= 3)
        G = Grid(); G.put(T, 0, A); v_cube(G, T, 0, 1)
        ok[1] += G.read(T, 1) == B.cube(A[:]) and G.read(T, 0) == ['.'] * n and not any(T.band_of(p) >= 2 for p in G.h)
        G = Grid(); G.put(T, 0, A); G.put(T, 1, D0); v_add(G, T, 0, 1, True)
        want = D0[:]; B.add_into(want, A, mirror=True); ok[2] += G.read(T, 1) == want
    return ok, fold_rule(T), T

def fold_search():
    out = {}
    for n in (7, 23, 59, 179):
        good = []
        for kk in range(1, n):
            for s1 in (1, 2):
                for s0 in (1, 2):
                    f = pari(f"Mod(1,3)*(x^{n} - {s1}*x^{kk} - {s0})")
                    if pari.polisirreducible(f): good.append((kk, n - kk, s1, s0))
        out[n] = good
    return out

def gnb_types(n, tmax=20):
    res = []
    for t in range(1, tmax + 1):
        p = t * n + 1
        if not pari.isprime(p): continue
        o = int(pari.znorder(pari.Mod(3, p)))
        from math import gcd
        if gcd(t * n // o, n) == 1: res.append(t)
    return res

def cube_weights(n, k):
    """weight of x^(3i) mod (x^n - x^k - 1) for each i: a rigid motion of holes maps one peg to one peg."""
    f = pari(f"Mod(1,3)*(x^{n} - x^{k} - 1)")
    w = []
    for i in range(n):
        r = pari.lift(pari(f"Mod(1,3)*x^{3*i}") % f)
        w.append(sum(1 for c in pari.Vec(r) if int(c) % 3))
    return w

def main():
    rnd = random.Random(20260930); out = {}
    print("== 1. Fold trinomials x^n = s1*x^k + s0 irreducible over GF(3)  (listed as k, n-k, s1, s0)")
    fs = fold_search(); out['folds'] = fs
    for n, g in fs.items():
        rows = [x for x in g if x[1] % 10 == 0 and x[2] == 1 and x[3] == 1]
        print(f"  n={n}: {len(g)} irreducible; with s1=s0=+1 and n-k a whole number of 10-hole rows: {rows}")
        print(f"         all: {g if len(g) <= 12 else g[:12] + ['...']}")
    print("\n== 2. Gaussian normal bases of GF(3^n), types t <= 20 (t = 1 or 2 is 'optimal')")
    for n in (7, 23, 59, 179):
        t = gnb_types(n); out.setdefault('gnb', {})[n] = t
        print(f"  n={n}: types {t}")
    print("\n== 3. Can a rigid motion (any permutation of holes) be the polynomial-basis cube?")
    for name, (n, k, _) in TIERS.items():
        w = cube_weights(n, k); multi = sum(1 for x in w if x > 1)
        print(f"  {name}: x^(3i) reduces to a single peg for {w.count(1)} of {n} holes; {multi} single pegs become 2+ pegs "
              f"(max {max(w)}), so no permutation of holes can be the cube")
        out.setdefault('cube_weights', {})[name] = dict(single=w.count(1), multi=multi, max=max(w))
    print("\n== 4. Cursor-ship recipes on the band layout, checked against Board (itself checked against PARI)")
    for name in TIERS:
        ok, fr, T = check_cursors(name, rnd)
        G = Grid(); A = [rnd.choice('.WR') for _ in range(T.n)]; Bv = [rnd.choice('.WR') for _ in range(T.n)]
        G.put(T, 0, A); G.put(T, 1, Bv); v_mul(G, T, 0, 1, 2); mm, ms = G.moves, G.ship_steps
        G = Grid(); G.put(T, 0, A); v_cube(G, T, 0, 1); cm, cs = G.moves, G.ship_steps
        print(f"  {name}: n={T.n} = {T.n // 10} rows + {T.n % 10} holes; band {T.H} rows, gap {T.gap}; "
              f"fold x^{T.n} = x^{T.k} + 1 -> cruiser starts {fr[1]} {fr[0]} {'up' if fr[0]=='rows' else 'back'}")
        print(f"      30 random: multiply-accumulate {ok[0]}/30, cube {ok[1]}/30, subtract {ok[2]}/30 correct; "
              f"one multiply = {mm} peg moves + {ms} ship steps; one cube = {cm} peg moves + {cs} ship steps")
        out.setdefault('cursor', {})[name] = dict(ok=ok, fold=fr, H=T.H, gap=T.gap, mul=(mm, ms), cube=(cm, cs))
    print("\n== 5. Price of the visual fold: mean moves of one multiply / one cube (300 random inputs, same inputs per n)")
    for n, ks in ((23, (3, 15)), (59, (17, 39)), (179, (59, 75))):
        r2 = random.Random(n); ins = [([r2.choice('.WR') for _ in range(n)], [r2.choice('.WR') for _ in range(n)]) for _ in range(300)]
        for kk in ks:
            Bd = Board(n, kk); m0 = Bd.moves
            for a, b in ins: Bd.mul(a, b)
            mm = (Bd.moves - m0) / 300; m0 = Bd.moves
            for a, b in ins: Bd.cube(a[:])
            cm = (Bd.moves - m0) / 300
            print(f"  n={n}, x^{n} = x^{kk} + 1 (n-k = {n-kk}): multiply {mm:,.0f}, cube {cm:,.0f} moves")
            out.setdefault('fold_price', {})[f"{n}_{kk}"] = (mm, cm)
    json.dump(out, open("ecbs_layout.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
