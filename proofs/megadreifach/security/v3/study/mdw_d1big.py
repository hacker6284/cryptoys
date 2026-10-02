"""Dedicated D1 (left free start) and D1' (right free start) on NRk, same samples; scratch only.

Parts:
  conj KIND T N          harness side-convention check (deterministic identities, N samples):
                         (a) D1' harness Delta == W(hg) W(h)^-1;  (b) g~ = h g h^-1 is a 2-edge flip;
                         (c) Delta(h, g) == W(h) Q(h, g~) W(h)^-1 with Q(h, g~) = W(h)^-1 W(g~ h)  (D1 <-> D1' map)
                         (d) per sample, the conjugacy-invariant statistics of Delta(h,g) and Q(h,g~) are equal
  diag NRk T N SEED0    D1 left: which corners carry the excess of fully fixed corners (last-card pieces, register)
  ctrl - 0 N SEED0      null control: Q = a^-1 b, a and b independent uniform_st (same statistics)
  big KIND T N SEED0     per sample: deal K, uniform h, 2-edge flip g (slots e1,e2);
                         D1 left:  Q = W(h)^-1 W(g h);   D1' right: Delta = W(h g) W(h)^-1 (harness formula)
                         chunk c (100k samples) uses random.Random(SEED0 + c); cumulative summary each quarter.
KIND T: NRk 52 (two passes) or NRk 104 (three passes: em_nr(104, h, K + K)).
"""
import math
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool

from scipy.stats import chi2 as C2, norm

import mdfix_lib as L
import mdfix_dist as M
import mdw_lib as W

comp, inv = L.compose_st, L.inv_st
CHN = 100000


def mk(kind, t):
    if kind == 'NRk' and t > 52:
        assert t <= 104
        return lambda h, d: comp(h, W.em_nr(t, h, list(d) + list(d), kopp=True))
    return W.make_dm(kind, t)


def gflip(e1, e2):
    g = list(L.ID_ST)
    g[20 + e1] ^= 1
    g[20 + e2] ^= 1
    return g


def is_2flip(g):
    if any(g[s] != 3 * s for s in range(20)):
        return False
    d = [s for s in range(30) if g[20 + s] != 2 * s]
    return len(d) == 2 and all(g[20 + s] == 2 * s + 1 for s in d)


def conj_check(kind, t, n, seed):
    dm = mk(kind, t)
    rng = random.Random(seed)
    ok = [0, 0, 0, 0]
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        g = gflip(e1, e2)
        hi = inv(h)
        Wh = comp(hi, comp(dm(h, K), hi))
        hg = comp(h, g)
        y3 = dm(hg, K)
        X = comp(hi, dm(h, K))
        D = comp(comp(comp(inv(hg), y3), g), inv(X))             # exact harness formula (mdw_tests.d1_work)
        Whg = comp(inv(hg), comp(y3, inv(hg)))
        ok[0] += D == comp(Whg, inv(Wh))
        gt = comp(h, comp(g, hi))
        ok[1] += is_2flip(gt)
        gth = comp(gt, h)
        Wgth = comp(inv(gth), comp(dm(gth, K), inv(gth)))
        Q = comp(inv(Wh), Wgth)
        ok[2] += D == comp(Wh, comp(Q, inv(Wh)))
        ok[3] += all(f(D) == f(Q) for f in (L.fixc, L.fixe, L.moved, L.cyc_c, L.cyc_e))
    return ok


def new_side():
    return dict(pred=0, fe=0, fc=0, mv=0, mv2=0, he=Counter(), hc=Counter(), ce=Counter(), cc=Counter(),
                pos=[0] * 50, idf=[0] * 50)


def acc(r, z, ident):
    a1, a2, m = L.fixe(z), L.fixc(z), L.moved(z)
    r['pred'] += ident
    r['fe'] += a1 >= 2
    r['fc'] += a2 >= 2
    r['mv'] += m
    r['mv2'] += m * m
    r['he'][a1] += 1
    r['hc'][a2] += 1
    r['ce'][L.cyc_e(z)] += 1
    r['cc'][L.cyc_c(z)] += 1
    for s in range(20):
        r['pos'][s] += z[s] // 3 == s
        r['idf'][s] += z[s] == 3 * s
    for s in range(30):
        r['pos'][20 + s] += z[20 + s] // 2 == s
        r['idf'][20 + s] += z[20 + s] == 2 * s
    return a2 >= 2, m


def big_work(a):
    kind, t, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    A, B = new_side(), new_side()
    pr = dict(n=n, dfc=0, dfc2=0, dmv=0, dmv2=0)        # paired differences D1 - D1'
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        g = gflip(e1, e2)
        hi = inv(h)
        y = dm(h, K)
        Wh = comp(hi, comp(y, hi))
        Whi = inv(Wh)
        h2 = comp(g, h)
        h2i = inv(h2)
        W2 = comp(h2i, comp(dm(h2, K), h2i))
        fa, ma = acc(A, comp(Whi, W2), W2 == Wh)
        hg = comp(h, g)
        hgi = inv(hg)
        W3 = comp(hgi, comp(dm(hg, K), hgi))
        D = comp(W3, Whi)
        fb, mb = acc(B, D, W3 == Wh)
        pr['dfc'] += fa - fb
        pr['dfc2'] += (fa - fb) ** 2
        pr['dmv'] += ma - mb
        pr['dmv2'] += (ma - mb) ** 2
    return dict(n=n, A=A, B=B, pr=pr)


def ctrl_work(a):
    """Null control: Q = a^-1 b for independent a, b = L.uniform_st (tests the reference laws and the sampler)."""
    n, seed = a
    rng = random.Random(seed)
    A = new_side()
    for _ in range(n):
        x, y = L.uniform_st(rng), L.uniform_st(rng)
        acc(A, comp(inv(x), y), x == y)
    return dict(n=n, A=A)


def diag_work(a):
    """D1 left on NRk T: where do the extra fully fixed corners of Q sit?  Per sample, piece-state coincidence
    between X = E(h) and X'' = E(gh) (card-phase output states) for the pieces named by the last cards."""
    t, n, seed = a
    rng = random.Random(seed)
    r = dict(n=n, chk=0, ffc=0, ffe=0, cL=0, eL=0, cL1=0, oth=0, req=0, cLreq=0, oth_req=0, ffc_req=0, ffc_rne=0)
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        h2 = comp(gflip(e1, e2), h)
        D = K + K if t > 52 else K
        r1, r2 = [], []
        X = W.em_nr(t, h, D, regout=r1, kopp=True)
        X2 = W.em_nr(t, h2, D, regout=r2, kopp=True)
        hi, h2i = inv(h), inv(h2)
        Q = comp(inv(comp(hi, comp(comp(h, X), hi))), comp(h2i, comp(comp(h2, X2), h2i)))
        fq = sum(Q[s] == 3 * s for s in range(20))
        same = [W.find_c(X, c) == W.find_c(X2, c) for c in range(20)]
        r['chk'] += fq == sum(same)
        r['ffc'] += fq
        r['ffe'] += sum(W.find_e(X, e) == W.find_e(X2, e) for e in range(30))
        last = D[t - 1]
        cl, el, cl1 = W.CARD[last][4], W.CARD[last][1], W.CARD[D[t - 2]][4]
        r['cL'] += same[cl]
        r['eL'] += W.find_e(X, el) == W.find_e(X2, el)
        r['cL1'] += same[cl1] if cl1 != cl else 0
        o = (sum(same) - same[cl]) / 19
        r['oth'] += o
        eq = r1[0] == r2[0]
        r['req'] += eq
        if eq:
            r['cLreq'] += same[cl]
            r['oth_req'] += o
            r['ffc_req'] += sum(same)
        else:
            r['ffc_rne'] += sum(same)
    return r


def merge_all(rs):
    return dict(n=sum(r['n'] for r in rs), A=M.merge([r['A'] for r in rs]), B=M.merge([r['B'] for r in rs]),
                pr=M.merge([r['pr'] for r in rs]))


def mhw(s1, s2, n):
    m = s1 / n
    sd = math.sqrt(max(s2 / n - m * m, 0) * n / (n - 1))
    return m, 1.96 * sd / math.sqrt(n)


def show(lab, r, n):
    def ci(k, P):
        lo, hi = L.wilson(k, n)
        return f'{k / n:.5f} [{lo:.5f},{hi:.5f}] adv {k / n - P:+.5f}'
    lo, hi = L.wilson(r['pred'], n)
    he, hc = r['he'], r['hc']
    mfe = sum(k * c for k, c in he.items()) / n
    mfc = sum(k * c for k, c in hc.items()) / n
    vfe = sum(k * k * c for k, c in he.items()) / n - mfe ** 2
    vfc = sum(k * k * c for k, c in hc.items()) / n - mfc ** 2
    m, hw = mhw(r['mv'], r['mv2'], n)
    xe, xc = L.chi2_cycletype(r['ce'], M.CPE), L.chi2_cycletype(r['cc'], M.CPC)
    fe_x, fc_x = M.hist_chi(he, M.LAWE, 5), M.hist_chi(hc, M.LAWC, 5)
    print(f"  {lab} n={n}: exact prediction {r['pred']} [{lo:.2e},{hi:.2e}] | P(fixE>=2) {ci(r['fe'], M.P2E)} | P(fixC>=2) {ci(r['fc'], M.P2C)}")
    print(f"     mean fixE {mfe:.5f} +- {1.96 * math.sqrt(vfe / n):.5f}, mean fixC {mfc:.5f} +- {1.96 * math.sqrt(vfc / n):.5f} (ideal 1)"
          f" | mean moved {m:.5f} +- {hw:.5f} (ideal {M.MMEAN:.5f}, diff {m - M.MMEAN:+.5f})")
    print(f"     chi2 cyc-type E {xe[0]:.1f}/{xe[1]} p={xe[2]:.2g}, C {xc[0]:.1f}/{xc[1]} p={xc[2]:.2g} | "
          f"fixE-hist {fe_x[0]:.1f}/{fe_x[1]} p={fe_x[2]:.2g}, fixC-hist {fc_x[0]:.1f}/{fc_x[1]} p={fc_x[2]:.2g}")
    print('     fixC hist (obs/ideal): ' + ', '.join(f'{j}:{hc.get(j, 0) / n:.5f}/{float(M.LAWC[j]):.5f}' for j in range(5)))
    for key, nm, pc, pe in (('pos', 'position fixed', 1 / 20, 1 / 30), ('idf', 'fixed, orientation 0', 1 / 60, 1 / 60)):
        zs = [((r[key][s] / n) - (pc if s < 20 else pe)) / math.sqrt((pc if s < 20 else pe) * (1 - (pc if s < 20 else pe)) / n)
              for s in range(50)]
        zm = max(zs, key=abs)
        rc = [r[key][s] / n for s in range(20)]
        re_ = [r[key][s] / n for s in range(20, 50)]
        print(f"     per-slot '{nm}': corners {min(rc):.5f}..{max(rc):.5f} (ideal {pc:.5f}, 1-slot 95% hw {1.96 * math.sqrt(pc * (1 - pc) / n):.5f}),"
              f" edges {min(re_):.5f}..{max(re_):.5f} (ideal {pe:.5f}) | max |z| {abs(zm):.2f} at slot {zs.index(zm)}, Bonferroni p "
              f"{min(1.0, 100 * norm.sf(abs(zm))):.2g}; sum z^2 {sum(z * z for z in zs):.1f}/50 (chi2_50 p={C2.sf(sum(z * z for z in zs), 50):.2g}; slots not independent)")


def report(R, dt, tag):
    n = R['n']
    print(f'[{tag}] cumulative n={n}  [{dt:.0f}s]')
    show('D1  left  Q = W(h)^-1 W(gh)  ', R['A'], n)
    show("D1' right Delta = W(hg)W(h)^-1", R['B'], n)
    p = R['pr']
    a, ha = mhw(p['dfc'], p['dfc2'], n)
    b, hb = mhw(p['dmv'], p['dmv2'], n)
    print(f"  paired D1 - D1' (same deal, h, g): P(fixC>=2) diff {a:+.5f} +- {ha:.5f}; mean moved diff {b:+.5f} +- {hb:.5f}")
    sys.stdout.flush()


def main():
    args = sys.argv[1:]
    print('\n'.join(W.selftest(kinds=(('NRk', 52),))))
    T0 = time.time()
    part, kind, t, N = args[0], args[1], int(args[2]), int(args[3])
    if t > 52:
        # slow-path consistency for the 3-pass wrapper: two passes of K+K prefix == NRk52 on K
        rng = random.Random(1)
        for _ in range(5):
            K = list(range(52))
            rng.shuffle(K)
            h = L.uniform_st(rng)
            assert W.em_nr(52, h, K + K, kopp=True) == W.em_nr(52, h, K, kopp=True)
        print(f'NRk{t} wrapper: em_nr({t}, h, K+K) prefix check vs NRk52 OK (5 blocks); cost turns {260 + 5 * t}, finds {104 + 2 * t}')
    with Pool(4) as p:
        if part == 'diag':
            seed0 = int(args[4])
            nch = N // CHN
            print(f'diag NRk{t}: D1 left, N={N}, {nch} chunks of {CHN}, chunk c seed {seed0}+c; '
                  'coincide = same (slot, orientation) in X = E(h) and X\'\' = E(gh); ideal 1/60 corners, 1/60 edges')
            R = M.merge(p.map(diag_work, [(t, CHN, seed0 + c) for c in range(nch)]))
            n = R['n']

            def pc(k, m, P):
                lo, hi = L.wilson(k, m)
                return f'{k / m:.5f} [{lo:.5f},{hi:.5f}] (ideal {P:.5f}, excess {k / m - P:+.5f})'
            print(f"  check: #coinciding corners == #fully fixed corners of Q in {R['chk']}/{n} samples")
            print(f"  mean fully fixed corners of Q {R['ffc'] / n:.5f} (ideal {20 / 60:.5f}, excess {R['ffc'] / n - 1 / 3:+.5f}); "
                  f"edges {R['ffe'] / n:.5f} (ideal {30 / 60:.5f}, excess {R['ffe'] / n - 0.5:+.5f})")
            print(f"  last card's corner coincides: {pc(R['cL'], n, 1 / 60)}")
            print(f"  last card's edge coincides:   {pc(R['eL'], n, 1 / 60)}")
            print(f"  second-to-last card's corner (if different) coincides: {R['cL1'] / n:.5f} (ideal about {1 / 60:.5f} x P(different))")
            print(f"  other 19 corners, mean per corner: {R['oth'] / n:.6f} (ideal {1 / 60:.6f}, excess {R['oth'] / n - 1 / 60:+.6f}; "
                  f"excess x 19 = {19 * (R['oth'] / n - 1 / 60):+.5f})")
            print(f"  final registers equal (last face R = R''): {pc(R['req'], n, 1 / 12)}")
            m = R['req']
            print(f"  given R = R'': last corner coincides {pc(R['cLreq'], m, 1 / 5)}; other corners per corner {R['oth_req'] / m:.6f}; "
                  f"mean coinciding corners {R['ffc_req'] / m:.5f} | given R != R'': mean coinciding corners {R['ffc_rne'] / (n - m):.5f}")
        elif part == 'ctrl':
            seed0 = int(args[4])
            nch = N // CHN
            print(f'ctrl: N={N}, {nch} chunks of {CHN}, chunk c seed {seed0}+c; Q = a^-1 b, a, b independent uniform_st')
            rs = p.map(ctrl_work, [(CHN, seed0 + c) for c in range(nch)])
            show('null control Q = a^-1 b', M.merge([r['A'] for r in rs]), sum(r['n'] for r in rs))
        elif part == 'conj':
            rs = p.map(_conj, [(kind, t, N // 4, 39_000_000 + c) for c in range(4)])
            ok = [sum(r[i] for r in rs) for i in range(4)]
            print(f"conj {kind}{t} n={N} (seeds 39000000+c): (a) harness Delta == W(hg)W(h)^-1: {ok[0]}/{N}; "
                  f"(b) h g h^-1 is a 2-edge flip: {ok[1]}/{N}; (c) Delta(h,g) == W(h) Q(h, hgh^-1) W(h)^-1: {ok[2]}/{N}; "
                  f"(d) fixC, fixE, moved, corner and edge cycle types of Delta(h,g) == those of Q(h, hgh^-1): {ok[3]}/{N}")
        else:
            seed0 = int(args[4])
            nch = N // CHN
            print(f'big {kind}{t}: N={N}, {nch} chunks of {CHN}, chunk c seed {seed0}+c')
            parts, q = [], max(1, nch // 4)
            for i, r in enumerate(p.imap(big_work, [(kind, t, CHN, seed0 + c) for c in range(nch)])):
                parts.append(r)
                if (i + 1) % q == 0 or i + 1 == nch:
                    report(merge_all(parts), time.time() - T0, f'{i + 1}/{nch} chunks')
    print(f'wall time {time.time() - T0:.0f} s, workers 4')


def _conj(a):
    return conj_check(*a)


if __name__ == '__main__':
    main()
