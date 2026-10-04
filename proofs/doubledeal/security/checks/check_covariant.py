#!/usr/bin/env python3
"""Numerical check of the covariant round statement (`roundBody_covariant_iff_id`; proved in
the heavy library, `DoubleDealSecurityHeavy/V10Sym.lean`):
no nontrivial relabelling sigma admits a relabelling tau with
F(sigma.m) = tau.F(m) on every deck, where F = GridCycle o stem is the unkeyed
round body. (tau = sigma is the commuting case.) For each sigma, tau is forced
by one deck (tau = F(sigma.m1) o F(m1)^-1); covariance fails if another deck
disagrees. Deterministic seed."""
import random, sys
import ddport as P

def app(s, d): return [s[x] for x in d]
def transp(a, b): s = list(range(52)); s[a], s[b] = b, a; return s
sig9, sig10 = P.v9sym, P.v10sym
assert sorted(sig9(0, 1)) == list(range(52)), "v9Sym 0 1 is not a permutation"
assert sorted(sig10(1, 1)) == list(range(52)), "v10Sym 1 1 is not a permutation"

rng = random.Random(20260927)
def rdeck(): d = list(range(52)); rng.shuffle(d); return d
def F(m, v): return P.mix_columns(P.stem(m, v), v)

def covariant(s, v, decks=4):
    m1 = rdeck()
    a, b = F(m1, v), F(app(s, m1), v)
    tau = [None]*52
    for x, y in zip(a, b): tau[x] = y
    for _ in range(decks - 1):
        m = rdeck()
        if F(app(s, m), v) != app(tau, F(m, v)): return False
    return True

ID = list(range(52))
for v in (8, 9, 10, 11):
    tr = [transp(a, b) for a in range(52) for b in range(a+1, 52)]
    sig, gname = (sig10, "nontrivial v10Sym") if v >= 10 else (sig9, "nontrivial v9Sym")
    g = [sig(a, b) for a in range(13) for b in range(4) if (a, b) != (0, 0)]
    rs = []
    for _ in range(200):
        s = ID[:]; rng.shuffle(s); rs.append(s)
    res = {name: sum(covariant(s, v) for s in fam) for name, fam in
           (("transpositions", tr), (gname, g), ("random", rs))}
    assert covariant(ID, v)
    print(f"v{v}: covariant (some tau) for "
          + ", ".join(f"{name} {k}/{len(fam)}" for (name, k), fam in zip(res.items(), (tr, g, rs))))
    if any(res.values()): sys.exit(1)
print("no nontrivial sigma is round-covariant on the sampled decks (identity is)")
