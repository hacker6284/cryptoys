"""D1' (stripped free-start test) and the right-side D1, seeded; scratch only.

Convention (repo): compose(g, h) = g*h applies h first, then g; cp[s] = h.cp[g.cp[s]].
g = flip of edge LABELS e1, e2 (ep = id, eo = 1 at e1, e2; an involution, g^-1 = g).
  * The earlier D1 harness set h2[20+e] ^= 1, i.e. h2 = g*h (LEFT side): the pieces sitting in
    slots e1, e2 of h are flipped.  Checked below.
  * Here h'' = h*g (RIGHT side): pieces e1, e2 are flipped wherever they sit, so
    X'' = W*h*g = X*g whenever the card-phase word W is unchanged.
Output of any DM-shaped design: y = h * Q * X, X = W*h; Q = h^-1 y X^-1 (C36: Q = id;
SWBb: Q = U^-1 R^-1, where U depends on X and the last card grip, R on B0 = U h^-1, i.e. also on h).
Delta = (h g)^-1 y'' g^-1 (h^-1 y)^-1, computable from h, g and the two outputs.
PROVED (algebra): if W'' = W then X'' = X g and Delta = Q'' Q^-1.  Verified numerically below.
Statistics on Delta and on the right-side D1 quotient Qs = M^-1 M'' (M = h^-1 y h^-1,
M'' = (hg)^-1 y'' (hg)^-1), plus the right-side exact predictor y'' ?= (hg) M (hg).
Usage: python3 mdfix_d1prime.py KIND T N [KIND T N ...] [--workers 4] [--seedoff OFF]
"""
import math
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool

import mdfix_lib as L
import mdfix_dist as M

CH = 10
inv, comp = L.inv_st, L.compose_st


def gflip(e1, e2):
    g = list(L.ID_ST)
    g[20 + e1] ^= 1
    g[20 + e2] ^= 1
    return g


def run_internal(kind, t, h, d):
    """Returns (y, X, Q_internal, cardtrace) with Q from the puzzle states (not from y)."""
    X = list(h)
    trace = []
    gi = L.E.run(X, d, f3=False, trace=trace)
    if kind == 'C':
        L.f3(X, t, gi)          # rounds on A: Q = id, X here is E(h) = W h with W incl. rounds
        return comp(h, X), X, list(L.ID_ST), trace
    B = inv(h)
    L.sweep_onto(B, X, gi)
    L.f3b(B, t, 0)
    y = comp(inv(B), X)
    Q = comp(inv(h), inv(B))     # B_f = R U h^-1  =>  Q = U^-1 R^-1 = h^-1 B_f^-1
    return y, X, Q, trace


def selfchecks(kinds):
    rng = random.Random(20261001)
    out = []
    # side of the earlier D1 flip
    left = right = 0
    for _ in range(1000):
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        h2 = list(h)
        h2[20 + e1] ^= 1
        h2[20 + e2] ^= 1
        g = gflip(e1, e2)
        left += h2 == comp(g, h)
        right += h2 == comp(h, g)
    out.append(f'side check: earlier D1 flip h2[20+e]^=1 equals g*h = compose(g,h) in {left}/1000 cases and '
               f'h*g = compose(h,g) in {right}/1000 (equal only when h maps e1,e2 to themselves)')
    for kind, t in kinds:
        nW = okX = okD = 0
        for _ in range(3000):
            K = list(range(52))
            rng.shuffle(K)
            h = L.uniform_st(rng)
            e1, e2 = rng.sample(range(30), 2)
            g = gflip(e1, e2)
            hg = comp(h, g)
            y, X, Q, tr = run_internal(kind, t, h, K)
            y2, X2, Q2, tr2 = run_internal(kind, t, hg, K)
            assert y == L.make_dm(kind, t)(h, K) and y2 == L.make_dm(kind, t)(hg, K)
            if kind == 'C':     # W includes the F3 rounds; compare full traces
                tr, tr2 = [], []
                L.E.em(h, K, trace=tr) if t == 36 else None
                L.E.em(hg, K, trace=tr2) if t == 36 else None
            if tr != tr2:
                continue
            nW += 1
            okX += X2 == comp(X, g)
            Delta = comp(comp(comp(inv(hg), y2), g), inv(comp(inv(h), y)))
            okD += Delta == comp(Q2, inv(Q))
        out.append(f'identity check {kind}{t}: W unchanged in {nW}/3000 pairs; among them X\'\' == X*g in {okX}/{nW} '
                   f'and Delta == Q\'\' Q^-1 (Q from the puzzle states) in {okD}/{nW}')
        assert okX == nW and okD == nW
    return out


def work(a):
    kind, t, n, seed = a
    dm = L.make_dm(kind, t)
    rng = random.Random(seed)
    r = dict(n=n, fe=0, fc=0, sfe=0, sfc=0, mv=0, mv2=0, he=Counter(), hc=Counter(), ce=Counter(), cc=Counter(),
             pos=[0] * 50, idf=[0] * 50, ident=0,
             pred=0, qfe=0, qfc=0, qsfe=0, qsfc=0, qmv=0, qmv2=0)
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        g = gflip(e1, e2)
        hg = comp(h, g)
        y, y2 = dm(h, K), dm(hg, K)
        D = comp(comp(comp(inv(hg), y2), g), inv(comp(inv(h), y)))
        a1, a2, m = L.fixe(D), L.fixc(D), L.moved(D)
        r['fe'] += a1 >= 2
        r['fc'] += a2 >= 2
        r['sfe'] += a1
        r['sfc'] += a2
        r['mv'] += m
        r['mv2'] += m * m
        r['he'][a1] += 1
        r['hc'][a2] += 1
        r['ce'][L.cyc_e(D)] += 1
        r['cc'][L.cyc_c(D)] += 1
        r['ident'] += m == 0
        for s in range(20):
            r['pos'][s] += D[s] // 3 == s
            r['idf'][s] += D[s] == 3 * s
        for s in range(30):
            r['pos'][20 + s] += D[20 + s] // 2 == s
            r['idf'][20 + s] += D[20 + s] == 2 * s
        hi, hgi = inv(h), inv(hg)
        Mm = comp(hi, comp(y, hi))
        M2 = comp(hgi, comp(y2, hgi))
        r['pred'] += comp(hg, comp(Mm, hg)) == y2
        Qs = comp(inv(Mm), M2)
        b1, b2, mq = L.fixe(Qs), L.fixc(Qs), L.moved(Qs)
        r['qfe'] += b1 >= 2
        r['qfc'] += b2 >= 2
        r['qsfe'] += b1
        r['qsfc'] += b2
        r['qmv'] += mq
        r['qmv2'] += mq * mq
    return r


def show(name, R, dt):
    n = R['n']
    P2 = M.P2E

    def ci(k):
        lo, hi = L.wilson(k, n)
        return f'{k / n:.4f} [{lo:.4f},{hi:.4f}] adv {k / n - P2:+.4f}'

    def mean_sd(s1, s2):
        m = s1 / n
        sd = math.sqrt(max(s2 / n - m * m, 0) * n / (n - 1))
        return m, 1.96 * sd / math.sqrt(n)
    m, hw = mean_sd(R['mv'], R['mv2'])
    xe = L.chi2_cycletype(R['ce'], M.CPE)
    xc = L.chi2_cycletype(R['cc'], M.CPC)
    fe_x = M.hist_chi(R['he'], M.LAWE, 5)
    fc_x = M.hist_chi(R['hc'], M.LAWC, 5)
    lo, hi = L.wilson(R['ident'], n)
    print(f"D1' {name:7s} n={n}: Delta = identity {R['ident']} ({R['ident'] / n:.5f} [{lo:.5f},{hi:.5f}]) | P(fixE>=2) {ci(R['fe'])}"
          f" | P(fixC>=2) {ci(R['fc'])} | mean fixE {R['sfe'] / n:.4f}, fixC {R['sfc'] / n:.4f} (ideal 1 +-{1.96 / math.sqrt(n):.4f})"
          f" | mean moved {m:.4f} +- {hw:.4f} (ideal {M.MMEAN:.4f})"
          f" | chi2 cyc-type E {xe[0]:.1f}/{xe[1]} p={xe[2]:.2g}, C {xc[0]:.1f}/{xc[1]} p={xc[2]:.2g}"
          f" | chi2 fixE-hist p={fe_x[2]:.2g}, fixC-hist p={fc_x[2]:.2g}  [{dt:.0f}s]")
    # per-slot (not conjugacy invariant)
    from scipy.stats import norm
    for key, lab, pc, pe in (('pos', 'position fixed', 1 / 20, 1 / 30), ('idf', 'fixed with orientation 0', 1 / 60, 1 / 60)):
        zs = []
        for s in range(50):
            p = pc if s < 20 else pe
            zs.append((R[key][s] / n - p) / math.sqrt(p * (1 - p) / n))
        zmax = max(zs, key=abs)
        smax = zs.index(zmax)
        pb = min(1.0, 50 * 2 * norm.sf(abs(zmax)))
        rates = [R[key][s] / n for s in range(50)]
        print(f"     per-slot '{lab}' rates: corners mean {sum(rates[:20]) / 20:.5f} (ideal {pc:.5f}) range "
              f"[{min(rates[:20]):.5f},{max(rates[:20]):.5f}], edges mean {sum(rates[20:]) / 30:.5f} (ideal {pe:.5f}) range "
              f"[{min(rates[20:]):.5f},{max(rates[20:]):.5f}]; max |z| {abs(zmax):.2f} at slot {smax} "
              f"(Bonferroni p over 50 slots {pb:.2g}); sum z^2 = {sum(z * z for z in zs):.1f} on 50 slots")
    mq, hwq = mean_sd(R['qmv'], R['qmv2'])
    lo, hi = L.wilson(R['pred'], n)
    print(f"D1R {name:7s} n={n}: right-side exact prediction {R['pred']}/{n} = {R['pred'] / n:.5f} [{lo:.5f},{hi:.5f}]"
          f" | Qs: P(fixE>=2) {ci(R['qfe'])}, P(fixC>=2) {ci(R['qfc'])}, mean fixE {R['qsfe'] / n:.4f}, "
          f"fixC {R['qsfc'] / n:.4f}, mean moved {mq:.4f} +- {hwq:.4f}")
    sys.stdout.flush()


def main():
    args = [a for a in sys.argv[1:]]
    w = 4
    if '--workers' in args:
        i = args.index('--workers')
        w = int(args[i + 1])
        del args[i:i + 2]
    off = 0
    if '--seedoff' in args:
        i = args.index('--seedoff')
        off = int(args[i + 1])
        del args[i:i + 2]
    jobs = [(args[i], int(args[i + 1]), int(args[i + 2])) for i in range(0, len(args), 3)]
    print('\n'.join(L.selftest()))
    print('\n'.join(selfchecks(sorted({(k, t) for k, t, _ in jobs}))))
    T0 = time.time()
    with Pool(w) as p:
        for j, (kind, t, n) in enumerate(jobs):
            t0 = time.time()
            seed0 = 20_000_000 + 100_000 * (kind == 'SWBb') + 1000 * t + off
            R = M.merge(p.map(work, [(kind, t, n // CH, seed0 + c) for c in range(CH)]))
            print(f'{kind}{t}: seeds {seed0}+chunk (10 chunks)')
            show(f'{kind}{t}', R, time.time() - t0)
    print(f'wall time {time.time() - T0:.0f} s, workers {w}')


if __name__ == '__main__':
    main()
