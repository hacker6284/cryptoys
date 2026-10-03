#!/usr/bin/env python3
"""Receiver validation for ECBS: trace (subgroup) check vs cofactor strip, exceptional cases,
small-subgroup and invalid-curve inputs.  Peg recipes checked against PARI."""
import random
from ecbs_ref import Ref, TIERS, V, pari
import ecbs_exchange as X
import ecbs_keys as K

def chain(n):
    """the trace-check addition chain: list of ('double', m) / ('plus1', m) / ('final', m)."""
    steps = []; m = 1
    for b in bin(n)[3:]:
        steps.append(('double', m)); m *= 2
        if b == '1':
            steps.append(('final' if m + 1 == n else 'plus1', m)); m += 1
    return steps

def honest_never_exceptional(n, l, lam):
    """S_m = s_m B with s_m = 1 + lam + ... + lam^(m-1).  A mixed addition of s1 B and s2 B is
       exceptional iff s1 = +-s2 (mod l) (includes s = 0, the point at infinity)."""
    s = lambda m: sum(pow(lam, i, l) for i in range(m)) % l
    bad = []
    for kind, m in chain(n):
        if kind == 'double': a, b = s(m), pow(lam, m, l) * s(m) % l
        elif kind == 'plus1': a, b = pow(lam, 1, l) * s(m) % l, 1
        else: continue
        if a == 0 or b == 0 or a == b or (a + b) % l == 0: bad.append((kind, m))
    # cofactor strip: running scalars lam, lam - 1, lam^2 - lam, lam^2 - lam + 1, ...
    strip = []
    acc = 1                                  # Q = B after the first addition
    for d in (-1, 1, -1):
        acc = acc * lam % l                  # Frobenius
        if acc == 0 or acc == d % l or (acc + d) % l == 0: strip.append(d)
        acc = (acc + d) % l
    return bad, strip, s(n) % l

def main():
    rnd = random.Random(99)
    for name in TIERS:
        T = X.Tier(name); n, l = T.n, T.l
        print("=" * 78); print(f"{name}: n = {n}"); print("=" * 78)
        print("trace-check chain:", " ".join(f"{k[0]}{m}" if k != 'final' else f"final{m}" for k, m in chain(n)))
        bad, strip, trace = honest_never_exceptional(n, l, T.lam)
        print(f"honest points: exceptional steps in trace chain: {bad or 'none'}; in cofactor strip: {strip or 'none'}; "
              f"sum lambda^i (i<n) mod l = {trace}  (0 => every B in <P> passes)")
        print(f"order-5 points: Frobenius fixes them, trace = n * T5 = {n % 5} * T5 != O  (n mod 5 = {n % 5})")
        # the rational 5-torsion
        R = T.R
        if name == "Demo":
            pts = [p for p in pari.ellgroup(R.E)] and None
            allpts = []
            # enumerate every affine point of E over GF(3^7) through the reference
            els = [sum(((c % 3) if False else c) * R.w ** i for i, c in enumerate(v)) for v in
                   __import__('itertools').product((0, 1, 2), repeat=n)]
            for x in els:
                rhs = x ** 3 + 2 * x ** 2 + 1
                if rhs == 0: allpts.append(pari([x, rhs])); continue
                if pari.issquare(rhs):
                    y = pari.sqrt(rhs); allpts += [pari([x, y]), pari([x, -y])]
            assert len(allpts) + 1 == R.NE
            acc_tr = rej_tr = acc_sub = 0; mism = 0; cof_ok = 0
            for Pt in allpts:
                in_sub = len(R.mul(l, Pt)) == 1
                ok, _ = X.trace_check(T, R.unpt(Pt))
                mism += ok != in_sub; acc_tr += ok
                c5, _ = X.cofactor_strip(T, R.unpt(Pt))
                ref5 = R.mul(5, Pt)
                cof_ok += (c5 is None and (len(ref5) == 1 or True)) or (c5 is not None and R.pt(c5) == ref5)
            print(f"Demo exhaustive: {len(allpts)} affine points on E; trace check accepts {acc_tr} "
                  f"(subgroup has {l - 1} non-zero points); disagreements with 'l*B = O': {mism}; "
                  f"cofactor strip consistent with 5B (or rejected) on {cof_ok}/{len(allpts)}")
            nrej = sum(1 for Pt in allpts if X.cofactor_strip(T, R.unpt(Pt))[0] is None)
            print(f"   cofactor strip hit an exceptional case (=> reject) on {nrej} points")
            # walk exceptional-case rate at Demo (re-roll rule)
            fails = 0; N = 400
            for _ in range(N):
                w, terms = K.walk_three_state(K.three_state(rnd, 1))
                try: X.run_walk(T, w, [T.P])
                except ArithmeticError: fails += 1
            print(f"   Demo public walks hitting an exceptional case: {fails}/{N} (re-roll rule needed)")
        else:
            N = 30 if name != "Serious" else 8
            good = sum(X.trace_check(T, R.unpt(R.mul(rnd.randrange(1, l), T.Pref)))[0] for _ in range(N))
            T5 = pari([pari(1) + 0 * R.w, pari(1) + 0 * R.w]); assert R.on(T5)
            badacc = sum(X.trace_check(T, R.unpt(R.add(R.mul(rnd.randrange(1, l), T.Pref), R.mul(rnd.randrange(1, 5), T5))))[0] for _ in range(N))
            print(f"random honest points accepted: {good}/{N}; random B + (order-5 point) accepted: {badacc}/{N}")
        # invalid curves reachable with the same addition script (the script uses a = 2 but never b)
        N2 = 3 ** n + 1 - V(n, t=2)
        f2 = pari.factor(N2, 10 ** 8)
        f2s = [(int(p), int(e), bool(pari.isprime(p))) for p, e in zip(f2[0], f2[1])]
        print(f"b' = 2 (y^2 = x^3 + 2x^2 + 2, trace 2 over GF(3)): order {N2} = " +
              " * ".join(f"{p}{'^' + str(e) if e > 1 else ''}{'' if pr else '(composite)'}" for p, e, pr in f2s))
        Nn = 3 ** n + 1
        fn = pari.factor(Nn, 10 ** 8)
        print(f"b' = 0 (y^2 = x^2 (x + 2), non-split node): smooth points form a cyclic group of order 3^n + 1 = " +
              " * ".join(f"{int(p)}{'^' + str(int(e)) if int(e) > 1 else ''}{'' if pari.isprime(p) else '(composite)'}" for p, e in zip(fn[0], fn[1])))
        print("b' outside GF(3): Frobenius moves the point to the curve with b'^3, so the walk is not a group operation;"
              " every such input fails the on-curve check.")

if __name__ == "__main__":
    main()
