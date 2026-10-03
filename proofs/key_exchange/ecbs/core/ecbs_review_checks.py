#!/usr/bin/env python3
"""Small independent checks of review items adopted into the spec (REVIEW.md 2026-09-30):
 (a) the relation at m = n - 2:  2 lam^(n-3) = sum_{e < n-3} lam^e  (mod l), all tiers;
 (b) Demo brute force: largest m for which pegs-only (digits -1, 0, +1 on positions 0..m-1) is injective mod l;
 (c) Demo exhaustive: on-curve + the LAZY-Y trace chain (ecbs_fform.WBF) accepts exactly <P> minus O."""
import sys, itertools
sys.dont_write_bytecode = True
import ecbs_exchange as X
from ecbs_ref import pari
from ecbs_fform import WBF
for name in ("Demo", "Toy", "Hobby", "Serious"):
    T = X.Tier(name); n, l, lam = T.n, T.l, T.lam
    lhs = 2 * pow(lam, n - 3, l) % l; rhs = sum(pow(lam, e, l) for e in range(n - 3)) % l
    print(f"(a) {name}: 2 lam^(n-3) == sum_(e<n-3) lam^e mod l: {lhs == rhs}")
T = X.Tier("Demo"); n, l, lam = T.n, T.l, T.lam
for m in range(1, 7):
    seen = set(); inj = True
    for d in itertools.product((-1, 0, 1), repeat=m):
        k = sum(c * pow(lam, e, l) for e, c in enumerate(d)) % l
        if k in seen: inj = False; break
        seen.add(k)
    print(f"(b) Demo pegs-only m = {m}: injective {inj}")
R = T.R; tot = acc = acc_sub = bad = 0
for i in range(3 ** 7):
    digs = []; t = i
    for _ in range(7): digs.append(t % 3); t //= 3
    x = sum(int(d) * R.w ** j for j, d in enumerate(digs)) if i else 0 * R.w
    rhs = x ** 3 + 2 * x ** 2 + 1
    if rhs == 0 * R.w: ys = [0 * R.w]
    elif pari.issquare(rhs): y = pari.sqrt(rhs); ys = [y, -y]
    else: continue
    for y in ys:
        Pt = pari([x, y]); insub = len(R.mul(l, Pt)) == 1
        B = WBF(7, 5); bx, by = R.unpt(Pt); bx, by = B.new_copy(bx), B.new_copy(by)
        ok = B.on_curve_check(bx, by) and B.trace_check(bx, by)
        tot += 1; acc += ok; acc_sub += ok and insub; bad += ok != insub
print(f"(c) Demo exhaustive, lazy-y trace chain: {tot} affine points, accepted {acc}, of which in <P> {acc_sub}; misclassified {bad}")
