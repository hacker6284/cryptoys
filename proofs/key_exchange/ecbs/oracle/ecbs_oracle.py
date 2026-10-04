"""The oracle for ECBS: PARI/GP finite-field and elliptic-curve arithmetic (via cypari2).
The evidence drivers run the code sudoc generates from primitives/key_exchange/ecbs/ecbs.sudo and check
it against this module. Nothing here models the board: no pegs, homes, workbench or card steps; it
computes P, [k]P, pi(C) - C, the key scalar and the SPEC 6 fold straight from the curve.
n, the tap k, the key cells and l are pinned below as literals copied from SPEC 1 and 4, checked
by PARI (pinned_checks: x^n - x^k - 1 irreducible over GF(3), l prime, l = #E/5), and the generated
tier() of ecbs.sudo must equal them (asserted at import). The layout constants (lane width, kept
rows) are read from the generated tier().
A number is a list of n trits (hole 0 first; 0 empty, 1 white, 2 red) or a '.WR' string."""
import os, sys
import cypari2
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))  # proofs/
import sudo_js as SJ
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9, silent=True)
NAMES = ("Demo", "Toy", "Hobby", "Serious")


def _sudo_tiers():
    s = SJ.Sudo("primitives/key_exchange/ecbs/ecbs.sudo")
    try:
        return {name: s.call("tier", name) for name in NAMES}
    finally:
        s.close()


# Pinned from SPEC 1 (n, tap x^n = x^k + 1, l = #E/5) and SPEC 4 (key cells). SPEC 1 prints
# Serious's l abbreviated (5078489869...5423907, 282 bits); the full value is core/ecbs_curve's.
PINNED = {
    "Demo":    dict(n=7,   k=5,  cells=2,   l=421),
    "Toy":     dict(n=23,  k=15, cells=16,  l=18828582139),
    "Hobby":   dict(n=59,  k=39, cells=51,  l=2826077218347794449447657747),
    "Serious": dict(n=179, k=59, cells=162,
                    l=5078489869724426155952648514707704116694985077007329814177591439556413097455105423907),
}
assert str(PINNED["Serious"]["l"]).startswith("5078489869") and str(PINNED["Serious"]["l"]).endswith("5423907")

SUDO_TIER = _sudo_tiers()                 # the generated Tier records, by name
for _name, _p in PINNED.items():          # the generated tier() must equal the pinned SPEC values
    _t = SUDO_TIER[_name]
    assert (_t["n"], _t["k"], _t["cells"]) == (_p["n"], _p["k"], _p["cells"]), \
        f"generated tier({_name}) n/k/cells {(_t['n'], _t['k'], _t['cells'])} != SPEC {_p}"
TIERS = {name: (p["n"], p["k"]) for name, p in PINNED.items()}
_vecrev = pari('(a,n)->Vecrev(a.pol, n)')

def V(n, t=-1, q=3):
    if n == 0: return 2
    a, b = 2, t
    for _ in range(n - 1): a, b = b, t * b - q * a
    return b

class Ref:
    def __init__(self, n, k, b=1):
        self.n, self.k = n, k
        self.w = pari(f"ffgen(Mod(1,3)*(x^{n} - x^{k} - 1), 'w)")
        self.E = pari.ellinit([0, 2, 0, 0, b], self.w)
        self.NE = 3 ** n + 1 - V(n); self.l = self.NE // 5
        self.zero = 0 * self.w
    def el(self, reg):
        s = self.zero
        for i, c in enumerate(reg):
            if c == 'W': s += self.w ** i
            elif c == 'R': s -= self.w ** i
        return s
    def reg(self, a):
        v = _vecrev(a, self.n)
        return ['.WR'[int(c) % 3] for c in v]
    def pt(self, P):  return pari([self.el(P[0]), self.el(P[1])])
    def unpt(self, R): return (self.reg(R[0]), self.reg(R[1]))
    def mul(self, k, R): return pari.ellmul(self.E, R, k)
    def add(self, R, S): return pari.elladd(self.E, R, S)
    def neg(self, R): return pari.ellneg(self.E, R)
    def frob(self, R): return pari([R[0] ** 3, R[1] ** 3])
    def on(self, R): return bool(pari.ellisoncurve(self.E, R))
    def rand_el(self, rnd): return ['.WR'[rnd.randrange(3)] for _ in range(self.n)]


FOLD_KEEP_ROWS = {name: t["keeprows"] for name, t in SUDO_TIER.items()}
LANE = {name: t["w"] for name, t in SUDO_TIER.items()}
CELLS = {name: p["cells"] for name, p in PINNED.items()}


def pinned_checks():
    """PARI on the pinned literals: the tap is irreducible over GF(3), l is prime (PARI isprime,
    proven), and l = #E(GF(3^n))/5 from the trace recurrence. Returns {name: (irreducible, prime, l_is_E/5)}."""
    out = {}
    for name, p in PINNED.items():
        n, k, l = p["n"], p["k"], p["l"]
        irr = bool(pari.polisirreducible(pari(f"Mod(1,3)*(x^{n} - x^{k} - 1)")))
        prime = bool(pari.isprime(l))
        NE = 3 ** n + 1 - V(n)
        out[name] = (irr, prime, NE % 5 == 0 and NE // 5 == l)
    return out


class Tier:
    """A tier from the curve alone: P by the base-point rule (SPEC 5.1), l, lambda."""
    def __init__(self, name):
        self.name = name; n, k = TIERS[name]; self.n, self.k = n, k
        self.R = Ref(n, k); self.l = self.R.l; self.cells = CELLS[name]
        assert self.l == PINNED[name]["l"], f"{name}: #E/5 != the pinned l"
        # base point BY RULE: x = one white peg in hole j (j = 1, 2, ...), y = rhs^((3^n+1)/4);
        # the first j with y*y = rhs; then P = 5 (x, y).
        w = self.R.w; e = (3 ** n + 1) // 4; j = 1
        while True:
            x = w ** j; rhs = x ** 3 - x ** 2 + 1; y = rhs ** e
            if y * y == rhs: break
            j += 1
        self.base_hole = j; self.Rbase = pari([x, y])
        P = self.R.mul(5, self.Rbase)
        assert len(P) == 2 and len(self.R.mul(self.l, P)) == 1
        self.Pref = P; self.P = self.R.unpt(P)
        lam = [int(z) for z in pari.polrootsmod(pari("x^2+x+3"), self.l)]
        self.lam = [z for z in lam if self.R.mul(z, P) == self.R.frob(P)][0]

    # trits <-> PARI
    def el(self, t): return self.R.el(t if isinstance(t, str) else ''.join('.WR'[d] for d in t))
    def trits(self, e): return ['.WR'.index(c) for c in self.R.reg(e)]
    def point(self, p):
        """{x: trits, y: trits} or (x, y) -> PARI point; both empty means O is NOT meant (the card has no O)."""
        x, y = (p['x'], p['y']) if isinstance(p, dict) else p
        return pari([self.el(x), self.el(y)])
    def unpoint(self, Q):
        assert len(Q) == 2, "the point at infinity has no bands"
        return {'x': self.trits(Q[0]), 'y': self.trits(Q[1])}

    def scalar(self, cells):
        """the pegs-only key k = sum_j c_j lambda^(m-1-j) mod l, c_j in {0, 1, -1} (white +1, red -1)."""
        m = len(cells); k = 0
        for j, c in enumerate(cells):
            d = {0: 0, 1: 1, 2: -1, '.': 0, 'W': 1, 'R': -1}[c]
            k += d * pow(self.lam, m - 1 - j, self.l)
        return k % self.l
    def kP(self, k): return self.R.mul(k, self.Pref)
    def pi_minus_1(self, C): return self.R.add(self.R.frob(C), self.R.neg(C))
    def ref_fold(self, x):
        """SPEC 6: the fold to m = kept rows x lane width (fold_mod)."""
        return fold_mod(x, FOLD_KEEP_ROWS[self.name] * LANE[self.name])


def fold_mod(x, m):
    """z_j = sum of x_i over i = j (mod m), over GF(3); x as trits or a '.WR' string (returned alike)."""
    t = ['.WR'.index(c) for c in x] if isinstance(x, str) else list(x)
    z = [0] * m
    for i, c in enumerate(t): z[i % m] = (z[i % m] + c) % 3
    return ''.join('.WR'[d] for d in z) if isinstance(x, str) else z
