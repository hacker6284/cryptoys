"""v10Sym a x: rank index + a (mod 13), GF(4) suit label XOR x (clubs 0, diamonds 1,
hearts 2, spades 3). The 52 elements form Z/13 x (Z/2)^2 (not cyclic). Every
nontrivial element has a power equal to v10Sym 1 0 (order 13) or to one of the three
involutions v10Sym 0 x: exponent 13 if x != 0, else the inverse of a mod 13.
So four real-key witnesses cover all 51. Also: every v10Sym commutes with v10
SumRanks on random grids (the proved "if" direction), and a witness table for the
heavy Lean library (identity key, identity message)."""
import sys, pathlib, random
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import ddport as P
v10sym = P.v10sym
def exp(a, x): return 13 if x else pow(a, -1, 13)
def target(a, x): return (1, 0) if x == 0 else (0, x)
G = {(a, x): v10sym(a, x) for a in range(13) for x in range(4)}
comp = lambda s, t: [s[t[c]] for c in range(52)]
def power(s, n):
    r = list(range(52))
    for _ in range(n): r = comp(s, r)
    return r
if __name__ == '__main__':
    assert all(sorted(s) == list(range(52)) for s in G.values())
    assert all(comp(s, t) in G.values() for s in G.values() for t in G.values())
    for ax, s in G.items():
        if ax == (0, 0): continue
        assert power(s, exp(*ax)) == G[target(*ax)], ax
    print("ok: all 51 nontrivial v10Sym reduce to v10Sym 1 0 or v10Sym 0 x (x = 1, 2, 3)")
    rng = random.Random(0)
    for _ in range(300):
        d = list(range(52)); rng.shuffle(d)
        g = [d[13 * r:13 * r + 13] for r in range(4)]
        for s in G.values():
            assert P.sum_ranks_v10([[s[c] for c in row] for row in g]) == \
                [[s[c] for c in row] for row in P.sum_ranks_v10(g)]
    print("ok: every v10Sym commutes with v10 SumRanks on 300 random decks")
    idK = list(range(52))
    base = P.encrypt(list(range(52)), idK, 12)
    print("enc id:", base)
    for ax in [(1, 0), (0, 1), (0, 2), (0, 3)]:
        s = G[ax]; c = P.encrypt(s, idK, 12)
        print(f"enc v10Sym {ax[0]} {ax[1]}:", c, "breaks:", c != [s[y] for y in base])
