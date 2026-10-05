"""mr_ec.py -- small independent EC toolkit over GF(3^n) built on python-flint (NOT PARI, NOT kx-specs code).
Curve E_{a2,a6}: y^2 = x^3 + a2 x^2 + a6 (char 3).  Points: None = O, else (x, y)."""
import flint
from flint import fmpz_mod_poly_ctx, fq_default_ctx

def field(n, k=None):
    """GF(3^n); with k given, the polynomial basis x^n = x^k + 1 (modulus x^n - x^k - 1)."""
    if k is None:
        return fq_default_ctx(3, n, 't')
    R = fmpz_mod_poly_ctx(3)
    coeffs = [0] * (n + 1); coeffs[n] = 1; coeffs[k] = (coeffs[k] - 1) % 3; coeffs[0] = (coeffs[0] - 1) % 3
    return fq_default_ctx(modulus=R(coeffs))

def el_from_digits(F, digs):
    """digits d_i in {0,1,2} (hole i -> t^i)"""
    t = F.gen(); s = F(0); p = F(1)
    for d in digs:
        if d % 3: s += (d % 3) * p
        p *= t
    return s

def digits(F, a, n):
    """coefficient vector of a (hole 0 first), each in {0,1,2}"""
    s = str(a.to_list()) if hasattr(a, 'to_list') else None
    L = [int(c) for c in a.to_list()] if hasattr(a, 'to_list') else None
    L = (L or []) + [0] * n
    return L[:n]

class Curve:
    def __init__(self, F, a2, a6):
        self.F, self.a2, self.a6 = F, F(a2), F(a6)
    def rhs(self, x): return x * x * x + self.a2 * x * x + self.a6
    def on(self, P): return P is None or P[1] * P[1] == self.rhs(P[0])
    def neg(self, P): return None if P is None else (P[0], -P[1])
    def add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if y1 == -y2: return None
            lam = self.a2 * x1 / y1                 # (3x^2 + 2 a2 x)/(2y) = a2 x / y in char 3
        else:
            lam = (y2 - y1) / (x2 - x1)
        x3 = lam * lam - self.a2 - x1 - x2
        return (x3, lam * (x1 - x3) - y1)
    def mul(self, k, P):
        if k < 0: return self.mul(-k, self.neg(P))
        R = None; Q = P
        while k:
            if k & 1: R = self.add(R, Q)
            Q = self.add(Q, Q); k >>= 1
        return R
    def frob(self, P, i=1):
        if P is None: return None
        x, y = P
        for _ in range(i): x, y = x ** 3, y ** 3
        return (x, y)
