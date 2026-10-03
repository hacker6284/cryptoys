"""GF(3^7) as lookup tables (numpy), for EXHAUSTIVE Demo checks.  Evidence harness: every table is built
from PARI (../core/ecbs_ref.py, the tap x^7 = x^5 + 1) and cross-checked against PARI by selftest().
An element is the integer sum d_i 3^i of its trits (hole i: empty 0, white 1, red 2)."""
import sys, os
import numpy as np
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'core'))
from ecbs_ref import Ref, pari
N, K = 7, 5
Q = 3 ** N
R = Ref(N, K)
P3 = 3 ** np.arange(N)
DIG = np.array([[(a // 3 ** i) % 3 for i in range(N)] for a in range(Q)], dtype=np.int64)

def to_int(e):            # PARI element -> int
    return int(sum('.WR'.index(c) * 3 ** i for i, c in enumerate(R.reg(e))))
def to_el(a):             # int -> PARI element
    return R.el(['.WR'[d] for d in DIG[a]])

# a primitive element: find g with multiplicative order Q - 1
g = None
for cand in range(3, Q):
    e = to_el(cand)
    if pari.fforder(e) == Q - 1: g = e; break
EXP = np.zeros(2 * (Q - 1), dtype=np.int64); LOG = np.full(Q, -1, dtype=np.int64)
x = R.w ** 0
for k in range(Q - 1):
    a = to_int(x); EXP[k] = a; EXP[k + Q - 1] = a; LOG[a] = k; x = x * g
assert len(set(EXP[:Q - 1].tolist())) == Q - 1

def add(a, b): return ((DIG[a] + DIG[b]) % 3) @ P3
def neg(a): return ((3 - DIG[a]) % 3) @ P3
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    a = np.asarray(a); b = np.asarray(b)
    out = EXP[(LOG[np.where(a == 0, 1, a)] + LOG[np.where(b == 0, 1, b)]) % (Q - 1)]
    return np.where((a == 0) | (b == 0), 0, out)
def inv(a):
    a = np.asarray(a); assert np.all(a != 0)
    return EXP[(-LOG[a]) % (Q - 1)]
def cube(a): return mul(mul(a, a), a)
ONE = 1

def selftest(rnd_n=3000, seed=7):
    rng = np.random.default_rng(seed)
    a = rng.integers(0, Q, rnd_n); b = rng.integers(0, Q, rnd_n)
    ok = 0
    for x_, y_, s_, p_, c_ in zip(a, b, add(a, b), mul(a, b), cube(a)):
        X, Y = to_el(int(x_)), to_el(int(y_))
        ok += to_int(X + Y) == s_ and to_int(X * Y) == p_ and to_int(X ** 3) == c_
    nz = a[a != 0]; okinv = sum(to_int(1 / to_el(int(z))) == iv for z, iv in zip(nz, inv(nz)))
    return dict(add_mul_cube_ok=f"{ok}/{rnd_n}", inv_ok=f"{okinv}/{len(nz)}")
