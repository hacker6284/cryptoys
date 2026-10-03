"""Independent reference for ECBS: PARI/GP finite-field and elliptic-curve arithmetic (via cypari2).
Nothing here shares code with the peg recipes (ecbs_pegs.py) or with kx-report/peg."""
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)
TIERS = {"Demo": (7, 5, 1), "Toy": (23, 15, 1), "Hobby": (59, 39, 2), "Serious": (179, 59, 6)}
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
    def is_zero(self, R): return pari.ellisoncurve(self.E, R) and len(R) == 1
    def on(self, R): return bool(pari.ellisoncurve(self.E, R))
    def rand_el(self, rnd): return ['.WR'[rnd.randrange(3)] for _ in range(self.n)]
