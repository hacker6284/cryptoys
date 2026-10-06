#!/usr/bin/env python3
r"""mr_frob.py -- Q3: how much can Frobenius (tau acts as lambda, lambda^n = 1) help a key search on
pegs-only keys k = sum_{e<m} d_e lambda^e, d uniform in {-1,0,1}^m?

A generic attacker can walk on classes {+-lambda^i k}.  The saving over a negation-only search is
governed by c(k) = #{i in Z/n : lambda^i k in S} (S = the key set).  If representations are unique,
lambda^i k in S iff the cyclic rotation of the digit vector by i puts zeros on the n-m positions
outside the window.  (1) exact expectation of c under that rotation model; (2) numerical test of
the model (true membership lambda^i k in S, by hashing S) on scaled-down windows; (3) resulting
bounds on the Frobenius speed-up.
Run: python mr_frob.py"""
import math, itertools, random
import numpy as np
from mr_lemmaA import ell, lam_of

def Ec_rotation(n, m):
    """E[#{i: rot_i(d) lies in window}] and E[1/c] (by exact enumeration over zero patterns is too big;
       E[c] is exact, E[1/c] via Monte Carlo below)."""
    tot = 0.0
    for i in range(n):
        req = {(e) for e in range(m) if (e + i) % n >= m}
        tot += 3.0 ** (-len(req))
    return tot

def c_rotation_mc(n, m, N, rnd):
    vals = []
    for _ in range(N):
        d = [rnd.choice((-1, 0, 1)) for _ in range(m)] + [0] * (n - m)
        c = 0
        for i in range(n):
            if all(d[(j - i) % n] == 0 for j in range(m, n)): c += 1
        vals.append(c)
    return vals

def mulmod(a, b, l):        # a: np.uint64 array (< 2^35), b: python int < l < 2^35
    b1, b0 = divmod(b, 1 << 18)
    t = (a * np.uint64(b1)) % np.uint64(l)
    t = (t * np.uint64(1 << 18)) % np.uint64(l)
    return (t + (a * np.uint64(b0)) % np.uint64(l)) % np.uint64(l)

def test_model(n, m):
    """exact over all 3^m keys: true c(k) vs rotation-model c(k)."""
    l = ell(n); lam = lam_of(n)
    pw = [pow(lam, e, l) for e in range(m)]
    if l >= 2 ** 35:
        return test_model_py(n, m, l, lam, pw)
    # all keys, digit vectors in lexicographic order
    keys = np.zeros(1, dtype=np.uint64); digs = np.zeros((1, 0), dtype=np.int8)
    for e in range(m):
        adds = np.array([0, pw[e] % l, (-pw[e]) % l], dtype=np.uint64)
        keys = ((keys[:, None] + adds[None, :]) % np.uint64(l)).reshape(-1)
        digs = np.concatenate([np.repeat(digs, 3, axis=0), np.tile(np.array([0, 1, -1], dtype=np.int8), len(digs))[:, None]], axis=1)
    assert len(np.unique(keys)) == len(keys), "window not injective"
    sk = np.sort(keys)
    ctrue = np.zeros(len(keys), dtype=np.int64)
    for i in range(n):
        ki = mulmod(keys, pow(lam, i, l), l)
        pos = np.searchsorted(sk, ki); pos[pos >= len(sk)] = 0
        ctrue += (sk[pos] == ki)
    full = np.concatenate([digs, np.zeros((len(keys), n - m), dtype=np.int8)], axis=1)
    crot = np.zeros(len(keys), dtype=np.int64)
    for i in range(n):
        rolled = np.roll(full, i, axis=1)                 # digit e -> position e+i
        crot += np.all(rolled[:, m:] == 0, axis=1)
    return ctrue, crot

def test_model_py(n, m, l, lam, pw):
    keys = [0]; digs = [()]
    for e in range(m):
        keys = [(k + d * pw[e]) % l for k in keys for d in (0, 1, -1)]
        digs = [dv + (d,) for dv in digs for d in (0, 1, -1)]
    S = set(keys); assert len(S) == len(keys)
    lp = [pow(lam, i, l) for i in range(n)]
    ctrue = np.array([sum(1 for i in range(n) if (k * lp[i]) % l in S) for k in keys])
    crot = []
    for dv in digs:
        full = list(dv) + [0] * (n - m)
        crot.append(sum(1 for i in range(n) if all(full[(j - i) % n] == 0 for j in range(m, n))))
    return ctrue, np.array(crot)

def main():
    rnd = random.Random(3)
    print("== 1. Rotation model at Serious (n = 179): c(k) = #{i : lambda^i k in S}")
    for m in (162, 170, 173, 175, 176):
        Ec = Ec_rotation(179, m)
        vals = c_rotation_mc(179, m, 20000, rnd)
        Einv = sum(1 / v for v in vals) / len(vals)
        print(f"   m = {m}: E[c] = {Ec:.3f} (exact); MC E[c] = {sum(vals)/len(vals):.3f}; E[1/c] = {Einv:.4f}; "
              f"#classes/|S| (+-, rotations) = E[1/c]/2 = {Einv/2:.4f}; saving over negation-only BSGS/rho-on-S <= sqrt(1/E[1/c]) = 2^{0.5*math.log2(1/Einv):.2f}, "
              f"<= sqrt(E[c]) = 2^{0.5*math.log2(Ec):.2f}")
    print("\n== 2. Model test: true membership vs rotation model, all 3^m keys")
    for n, m in ((23, 12), (23, 14), (23, 15), (59, 10)):
        ct, cr = test_model(n, m)
        print(f"   n = {n}, m = {m}: keys {len(ct)}; c_true == c_rot for {np.sum(ct == cr)} keys; max excess {int(np.max(ct - cr))}; "
              f"E[c_true] = {ct.mean():.4f}, E[c_rot] = {cr.mean():.4f}, exact formula {Ec_rotation(n, m):.4f}")
    print("\n== 3. Summary numbers for the report (Serious)")
    l = ell(179)
    for m in (162, 173, 175, 176):
        H = m * math.log2(3)
        bsgs = math.log2(3 ** (m // 2) + 3 ** (m - m // 2))
        Ec = Ec_rotation(179, m)
        print(f"   m = {m}: H_inf = {H:.2f}; BSGS (no symmetry) 2^{bsgs:.2f}; with negation 2^{bsgs-0.5:.2f}; "
              f"hypothetical ideal Frobenius class search 2^{bsgs-0.5-0.5*math.log2(Ec):.2f}; rho on the curve 2^136.78")

if __name__ == "__main__": main()
