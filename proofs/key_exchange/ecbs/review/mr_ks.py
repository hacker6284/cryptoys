#!/usr/bin/env python3
r"""mr_ks.py -- Q11(a): the character-sum constant for f = x on E: y^2 = x^3 + 2x^2 + 1 over GF(3^n).
Claim to test (REVIEW.md, proved via Weil/Deligne + Grothendieck-Ogg-Shafarevich): for every group
character chi of E(F_q) and every nontrivial additive character psi of F_q,
    | sum_{P in E(F_q) \ O} chi(P) psi(x(P)) | <= 3 sqrt(q),
hence for any subgroup H: | sum_{P in H \ O} psi(x(P)) | <= 3 sqrt(q)   (KS-type constant 3, not 4).
(1) n = 7: ALL (chi, psi) pairs exactly (E cyclic of order 2105; FFT over Z/2105).
(2) n = 9, 11, 13: trivial chi (whole group) for all psi, by a ternary Walsh-Hadamard transform.
All F_3-linear functionals x -> a.coords(x) are exactly the maps x -> Tr(beta x), so max over a = max over psi.
Run: python mr_ks.py"""
import math, itertools, time
import numpy as np
from mr_ec import field, Curve, el_from_digits

def coords(a, n):
    L = [int(c) for c in a.to_list()] + [0] * n
    return L[:n]

def all_x_counts(n):
    """f[x] = #{y : (x,y) in E}, x indexed by base-3 integer of its coordinates (coord 0 = least significant)."""
    F = field(n); C = Curve(F, 2, 1); e = (3 ** n - 1) // 2
    f = np.zeros(3 ** n, dtype=np.float64)
    t = F.gen(); powers = [t ** i for i in range(n)]
    for idx in range(3 ** n):
        v = idx; x = F(0); i = 0
        while v:
            v, d = divmod(v, 3)
            if d: x += d * powers[i]
            i += 1
        r = C.rhs(x)
        f[idx] = 1 if r == 0 else (2 if r ** e == 1 else 0)
    return f

def ternary_wht(f, n):
    w = np.exp(2j * np.pi / 3)
    M = np.array([[1, 1, 1], [1, w, w * w], [1, w * w, w]])
    a = f.astype(complex).reshape([3] * n)
    for ax in range(n):
        a = np.tensordot(M, a, axes=([1], [ax]))
        a = np.moveaxis(a, 0, ax)
    return a.reshape(-1)

def full_n7():
    n = 7; F = field(n); C = Curve(F, 2, 1); q = 3 ** n
    e = (q - 1) // 2; pts = []
    for digs in itertools.product(range(3), repeat=n):
        x = el_from_digits(F, digs); r = C.rhs(x)
        if r == 0: pts.append((x, F(0)))
        elif r ** e == 1:
            # find sqrt by exponent trick (q = 3 mod 4)
            y = r ** ((q + 1) // 4); assert y * y == r
            pts += [(x, y), (x, -y)]
    NE = len(pts) + 1; assert NE == 2105
    G = next(P for P in pts if C.mul(5, P) is not None and C.mul(421, P) is not None)
    xs = []; Q = None
    for j in range(NE):
        xs.append(None if Q is None else coords(Q[0], n)); Q = C.add(Q, G)
    assert Q is None
    X = np.array([[0] * n] + xs[1:], dtype=np.int64)             # row j: coords of x(jG); row 0 unused
    w = np.exp(2j * np.pi / 3); best = (0, None, None); best_triv = 0; best_sub = 0
    for a in itertools.product(range(3), repeat=n):
        if not any(a): continue
        ph = (X @ np.array(a)) % 3
        fvec = w ** ph; fvec[0] = 0
        S = np.fft.fft(fvec)                                       # S[c] = sum_j f(j) e^{-2 pi i c j / NE}
        m = np.max(np.abs(S))
        if m > best[0]: best = (m, a, int(np.argmax(np.abs(S))))
        best_triv = max(best_triv, abs(S[0]))
        sub = abs(np.sum(fvec[::5]))                               # H = <5G> of order 421, O excluded
        best_sub = max(best_sub, sub)
    return q, best, best_triv, best_sub

def main():
    t0 = time.time()
    q, best, bt, bs = full_n7()
    s = math.sqrt(q)
    print(f"n = 7: max over ALL (chi, psi) of |sum_(P != O) chi(P) psi(x(P))| = {best[0]:.3f} = {best[0]/s:.4f} sqrt(q)  (bound 3 sqrt(q) = {3*s:.1f})")
    print(f"       trivial chi (whole group): {bt/s:.4f} sqrt(q);   subgroup of order 421 (O excluded): {bs/s:.4f} sqrt(q)")
    print(f"       [{time.time()-t0:.1f}s]", flush=True)
    for n in (9, 11, 13):
        t1 = time.time()
        f = all_x_counts(n); S = ternary_wht(f, n)
        assert abs(S[0].real - (f.sum())) < 1e-6
        m = np.max(np.abs(S[1:])); s = math.sqrt(3 ** n)
        print(f"n = {n}: #E = {int(f.sum()) + 1}; max over psi != 1 of |sum_(P != O) psi(x(P))| = {m/s:.4f} sqrt(q)  (Weil bound 3 sqrt(q)) [{time.time()-t1:.1f}s]", flush=True)

if __name__ == "__main__": main()
