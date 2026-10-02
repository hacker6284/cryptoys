"""Tests for the colour-named card-phase candidates (mdw_lib); scratch only.

Parts:
  base               read coverage of v2 (card phase alone, and C36 = cards + 36 F3), and of CF
  scan               D2 decay vs number of blank rounds for every candidate (100k pairs each)
  d1 KIND T N        D1 (left flip h -> g*h), D1' (right flip h -> h*g; Delta = X'' g^-1 X^-1),
                     W-unchanged rates under a 2-edge flip and a 2-corner twist, per-slot rates
  d2 KIND T N        D2 (secret uniform h, deal vs deal with cards 51,52 swapped)
  d3 KIND T N        telescoping pairs at 51,52 (same face / opposite faces / King+Ace / random),
                     IV and uniform starts: card-phase positions equal, output collisions
  merge KIND T NCELL adjacent swaps at positions POS, IV and uniform starts
Seeds are printed.  Statistics and exact laws as in mdfix_dist / mdfix_d1prime.
"""
import math
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool

import mdfix_lib as L
import mdfix_dist as M
import mdw_lib as W

CH = 10
comp, inv = L.compose_st, L.inv_st


def mk(kind, t):
    if kind == 'C':
        return L.make_dm('C', t)
    return W.make_dm(kind, t)


def cards_only(kind, h, d):
    if kind == 'C':
        st = list(h)
        L.cards(st, d)
        return st
    return W.em(kind, 0, h, d, rounds=False)


def gflip(e1, e2):
    g = list(L.ID_ST)
    g[20 + e1] ^= 1
    g[20 + e2] ^= 1
    return g


def gtwist(c1, c2):
    g = list(L.ID_ST)
    g[c1] = 3 * c1 + 1
    g[c2] = 3 * c2 + 2
    return g


# ---------------------------------------------------------------- coverage
def cov_work(a):
    kind, t, start, n, seed = a
    rng = random.Random(seed)
    distinct = Counter()
    anyu = uc = ue = 0
    miss_c, miss_e = [0] * 20, [0] * 30
    for _ in range(n):
        h = L.IV_ST if start == 'IV' else L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        if kind in ('Ccards', 'C'):
            rec = []
            L.E.run(list(h), d, f3=(kind == 'C'), rec=rec) if kind == 'Ccards' else None
            if kind == 'C':
                st = list(h)
                gi = L.E.run(st, d, f3=False, rec=rec)
                for r in range(1, t + 1):
                    op, rd, _, _ = L.F3[r & 1][gi]
                    L.apply(st, op)
                    s, tab = rd[0]
                    rec.append((s, st[s]))
                    gi = tab[st[s]]
            pcs = {('c', x // 3) if s < 20 else ('e', x // 2) for s, x in rec}
        else:
            rec = []
            W.em(kind, t, h, d, rec=rec)
            pcs = set(rec)
        rc = {p for k, p in pcs if k == 'c'}
        re_ = {p for k, p in pcs if k == 'e'}
        distinct[len(rc) + len(re_)] += 1
        uc += 20 - len(rc)
        ue += 30 - len(re_)
        anyu += len(rc) + len(re_) < 50
        # missed pieces -> their slot in the input h
        posc = {h[s] // 3: s for s in range(20)}
        pose = {h[20 + s] // 2: s for s in range(30)}
        for p in range(20):
            if p not in rc:
                miss_c[posc[p]] += 1
        for p in range(30):
            if p not in re_:
                miss_e[pose[p]] += 1
    return dict(n=n, distinct=distinct, anyu=anyu, uc=uc, ue=ue, miss_c=miss_c, miss_e=miss_e)


def show_cov(name, R, dt):
    n = R['n']
    lo, hi = L.wilson(R['anyu'], n)
    dist = R['distinct']
    mean = sum(k * c for k, c in dist.items()) / n
    q = sorted(dist.items())
    print(f"COV {name:18s} n={n}: distinct pieces read mean {mean:.3f} of 50 (min {q[0][0]}, max {q[-1][0]}); "
          f"P(>=1 unread) {R['anyu'] / n:.5f} [{lo:.5f},{hi:.5f}]; mean unread corners {R['uc'] / n:.3f}, edges {R['ue'] / n:.3f}  [{dt:.0f}s]")
    print('     distribution of #distinct pieces read: ' + ', '.join(f'{k}:{c / n:.4f}' for k, c in q if c / n >= 0.0005))
    mc, me = R['miss_c'], R['miss_e']
    tc = sorted(range(20), key=lambda s: -mc[s])
    te = sorted(range(30), key=lambda s: -me[s])
    print('     most-missed input slots (corner c<slot>, edge e<slot> = SPEC 5.6 numbering; miss rate): '
          + ', '.join(f'c{s} {mc[s] / n:.3f}' for s in tc[:4]) + ' | ' + ', '.join(f'e{s} {me[s] / n:.3f}' for s in te[:6])
          + f' | least-missed: c{tc[-1]} {mc[tc[-1]] / n:.3f}, e{te[-1]} {me[te[-1]] / n:.3f}')
    sys.stdout.flush()


# ---------------------------------------------------------------- D2
def d2_work(a):
    kind, t, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    r = dict(n=n, fe=0, fc=0, mv=0, mv2=0, he=Counter(), hc=Counter(), ce=Counter(), cc=Counter())
    for _ in range(n):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        d2 = list(d)
        d2[50], d2[51] = d2[51], d2[50]
        z = comp(inv(dm(h, d)), dm(h, d2))
        a1, a2, m = L.fixe(z), L.fixc(z), L.moved(z)
        r['fe'] += a1 >= 2
        r['fc'] += a2 >= 2
        r['mv'] += m
        r['mv2'] += m * m
        r['he'][a1] += 1
        r['hc'][a2] += 1
        r['ce'][L.cyc_e(z)] += 1
        r['cc'][L.cyc_c(z)] += 1
    return r


# ---------------------------------------------------------------- D1 / D1'
def d1_work(a):
    kind, t, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    r = dict(n=n, pred=0, fe=0, fc=0, sfe=0, sfc=0, mv=0, mv2=0,
             ident=0, dfe=0, dfc=0, dsfe=0, dsfc=0, dmv=0, dmv2=0, dhe=Counter(), dhc=Counter(), dce=Counter(), dcc=Counter(),
             pos=[0] * 50, idf=[0] * 50, wsameE=0, wsameC=0, xsame=0, qsmall=0, dsmall=0)
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        g = gflip(e1, e2)
        y = dm(h, K)
        X = comp(inv(h), y)                  # = W h (Q = id for every rule here)
        # D1: left flip h2 = g*h (pieces in slots e1, e2 of h flipped)
        h2 = comp(g, h)
        y2 = dm(h2, K)
        hi, h2i = inv(h), inv(h2)
        Mm = comp(hi, comp(y, hi))           # = W
        M2 = comp(h2i, comp(y2, h2i))        # = W''
        r['pred'] += comp(h2, comp(Mm, h2)) == y2
        r['wsameE'] += Mm == M2
        Q = comp(inv(Mm), M2)
        a1, a2, m = L.fixe(Q), L.fixc(Q), L.moved(Q)
        r['xsame'] += comp(M2, h2) == X          # final card-phase+replay states re-merged
        r['qsmall'] += m <= 10
        r['fe'] += a1 >= 2
        r['fc'] += a2 >= 2
        r['sfe'] += a1
        r['sfc'] += a2
        r['mv'] += m
        r['mv2'] += m * m
        # D1': right flip h3 = h*g; Delta = (hg)^-1 y3 g^-1 (h^-1 y)^-1
        hg = comp(h, g)
        y3 = dm(hg, K)
        D = comp(comp(comp(inv(hg), y3), g), inv(X))
        b1, b2, mq = L.fixe(D), L.fixc(D), L.moved(D)
        r['ident'] += mq == 0
        r['dsmall'] += mq <= 10
        r['dfe'] += b1 >= 2
        r['dfc'] += b2 >= 2
        r['dsfe'] += b1
        r['dsfc'] += b2
        r['dmv'] += mq
        r['dmv2'] += mq * mq
        r['dhe'][b1] += 1
        r['dhc'][b2] += 1
        r['dce'][L.cyc_e(D)] += 1
        r['dcc'][L.cyc_c(D)] += 1
        for s in range(20):
            r['pos'][s] += D[s] // 3 == s
            r['idf'][s] += D[s] == 3 * s
        for s in range(30):
            r['pos'][20 + s] += D[20 + s] // 2 == s
            r['idf'][20 + s] += D[20 + s] == 2 * s
        # corner-only perturbation (left): two corners of h twisted +1 / -1
        c1, c2 = rng.sample(range(20), 2)
        h4 = comp(gtwist(c1, c2), h)
        y4 = dm(h4, K)
        h4i = inv(h4)
        r['wsameC'] += comp(h4i, comp(y4, h4i)) == Mm
    return r


def d1l_work(a):
    """D1 left flip only (replication runs): Q = W^-1 W'' statistics incl. histograms and cycle types."""
    kind, t, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    r = dict(n=n, pred=0, fe=0, fc=0, mv=0, mv2=0, he=Counter(), hc=Counter(), ce=Counter(), cc=Counter())
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        h2 = comp(gflip(e1, e2), h)
        y, y2 = dm(h, K), dm(h2, K)
        hi, h2i = inv(h), inv(h2)
        Mm = comp(hi, comp(y, hi))
        M2 = comp(h2i, comp(y2, h2i))
        r['pred'] += Mm == M2
        Q = comp(inv(Mm), M2)
        a1, a2, m = L.fixe(Q), L.fixc(Q), L.moved(Q)
        r['fe'] += a1 >= 2
        r['fc'] += a2 >= 2
        r['mv'] += m
        r['mv2'] += m * m
        r['he'][a1] += 1
        r['hc'][a2] += 1
        r['ce'][L.cyc_e(Q)] += 1
        r['cc'][L.cyc_c(Q)] += 1
    return r


def mean_hw(s1, s2, n):
    m = s1 / n
    sd = math.sqrt(max(s2 / n - m * m, 0) * n / (n - 1))
    return m, 1.96 * sd / math.sqrt(n)


def show_d1(name, R, dt):
    from scipy.stats import norm
    n = R['n']
    P2E, P2C = M.P2E, M.P2C

    def ci(k, P):
        lo, hi = L.wilson(k, n)
        return f'{k / n:.4f} [{lo:.4f},{hi:.4f}] adv {k / n - P:+.4f}'
    lo, hi = L.wilson(R['pred'], n)
    m, hw = mean_hw(R['mv'], R['mv2'], n)
    a, b = L.wilson(R['wsameE'], n)
    c, d = L.wilson(R['wsameC'], n)
    print(f"D1  {name:8s} n={n}: exact prediction {R['pred']} ({R['pred'] / n:.6f} [{lo:.6f},{hi:.6f}]) | W unchanged: 2-edge flip "
          f"{R['wsameE']} [{a:.6f},{b:.6f}], 2-corner twist {R['wsameC']} [{c:.6f},{d:.6f}] | Q: P(fixE>=2) {ci(R['fe'], P2E)}, "
          f"P(fixC>=2) {ci(R['fc'], P2C)}, mean fixE {R['sfe'] / n:.4f}, fixC {R['sfc'] / n:.4f} (ideal 1 +-{1.96 / math.sqrt(n):.4f}), "
          f"mean moved {m:.4f} +- {hw:.4f} (ideal {M.MMEAN:.4f})  [{dt:.0f}s]")
    if 'xsame' in R:
        print(f"     D1 tail: final states equal (X'' = X) {R['xsame']}; Q moves <= 10 slots {R['qsmall']}; "
              f"D1' Delta moves <= 10 slots {R['dsmall']} (ideal P(moved <= 10) < 1e-30)")
    lo, hi = L.wilson(R['ident'], n)
    m, hw = mean_hw(R['dmv'], R['dmv2'], n)
    xe = L.chi2_cycletype(R['dce'], M.CPE)
    xc = L.chi2_cycletype(R['dcc'], M.CPC)
    fe_x = M.hist_chi(R['dhe'], M.LAWE, 5)
    fc_x = M.hist_chi(R['dhc'], M.LAWC, 5)
    print(f"D1' {name:8s} n={n}: Delta = identity {R['ident']} ({R['ident'] / n:.6f} [{lo:.6f},{hi:.6f}]) | P(fixE>=2) {ci(R['dfe'], P2E)}"
          f" | P(fixC>=2) {ci(R['dfc'], P2C)} | mean fixE {R['dsfe'] / n:.4f}, fixC {R['dsfc'] / n:.4f} | mean moved {m:.4f} +- {hw:.4f}"
          f" | chi2 cyc-type E {xe[0]:.1f}/{xe[1]} p={xe[2]:.2g}, C {xc[0]:.1f}/{xc[1]} p={xc[2]:.2g}"
          f" | chi2 fixE-hist p={fe_x[2]:.2g}, fixC-hist p={fc_x[2]:.2g}")
    for key, lab, pc, pe in (('pos', 'position fixed', 1 / 20, 1 / 30), ('idf', 'fixed with orientation 0', 1 / 60, 1 / 60)):
        zs = []
        for s in range(50):
            p = pc if s < 20 else pe
            zs.append((R[key][s] / n - p) / math.sqrt(p * (1 - p) / n))
        zmax = max(zs, key=abs)
        pb = min(1.0, 50 * 2 * norm.sf(abs(zmax)))
        print(f"     D1' per-slot '{lab}': max |z| {abs(zmax):.2f} at slot {zs.index(zmax)} (Bonferroni p over 50 slots {pb:.2g}); "
              f"sum z^2 = {sum(z * z for z in zs):.1f} on 50 slots")
    sys.stdout.flush()


# ---------------------------------------------------------------- D3 telescoping
def tele_pair(rng, cls):
    """Two distinct cards of a class: 'same' = same face (same rank < 12), 'opp' = opposite faces,
    'KA' = a King and an Ace (both on face 0), 'rand' = any two cards."""
    if cls == 'same':
        r = rng.randrange(12)
        s1, s2 = rng.sample(range(4), 2)
        return 4 * r + s1, 4 * r + s2
    if cls == 'opp':
        r = rng.randrange(12)
        return 4 * r + rng.randrange(4), 4 * L.ref.OPP[r] + rng.randrange(4)
    if cls == 'KA':
        return 48 + rng.randrange(4), rng.randrange(4)
    return tuple(rng.sample(range(52), 2))


def d3_work(a):
    kind, t, start, cls, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    poseq = coll = 0
    ex = []
    for _ in range(n):
        h = L.IV_ST if start == 'IV' else L.uniform_st(rng)
        a1, b1 = tele_pair(rng, cls)
        rest = [c for c in range(52) if c not in (a1, b1)]
        rng.shuffle(rest)
        d = rest + [a1, b1]
        d2 = rest + [b1, a1]
        pe = cards_only(kind, h, d) == cards_only(kind, h, d2)
        poseq += pe
        c = dm(h, d) == dm(h, d2)
        coll += c
        if (c or pe) and len(ex) < 2:
            ex.append((a1, b1, pe, c))
    return dict(n=n, poseq=poseq, coll=coll, ex=ex)


# ---------------------------------------------------------------- merge search
POS = [1, 2, 13, 26, 27, 39, 50, 51]


def merge_work(a):
    kind, t, start, i, n, seed = a
    dm = mk(kind, t)
    rng = random.Random(seed)
    hist = [0] * 51
    hits = []
    peq = 0
    for _ in range(n):
        h = L.IV_ST if start == 'IV' else L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        d2 = list(d)
        d2[i - 1], d2[i] = d2[i], d2[i - 1]
        y, y2 = dm(h, d), dm(h, d2)
        k = sum(u != v for u, v in zip(y, y2))
        hist[k] += 1
        if kind != 'C':
            peq += W.em(kind, 0, h, d, stop=i + 1, rounds=False) == W.em(kind, 0, h, d2, stop=i + 1, rounds=False)
        if k == 0:
            hits.append((d[i - 1], d[i]))
    return dict(hist=hist, hits=hits, peq=peq)


def run(p, fn, cfg, n, seed0):
    t0 = time.time()
    R = M.merge(p.map(fn, [cfg + (n // CH, seed0 + c) for c in range(CH)]))
    return R, time.time() - t0


KCODE = {'C': 0, 'CF': 1, 'NP': 2, 'NPL': 3, 'NPr': 4, 'NRr': 5, 'NRk': 6}


def main():
    args = sys.argv[1:]
    w = 4
    if '--workers' in args:
        i = args.index('--workers')
        w = int(args[i + 1])
        del args[i:i + 2]
    part = args[0]
    print('\n'.join(W.selftest()))
    T0 = time.time()
    with Pool(w) as p:
        if part == 'base':
            print('read coverage per block: distinct pieces of the puzzle read during E (seeds 30_000_000 + 1000*k + chunk)')
            plan = [('Ccards', 0, 'v2 card phase (52 reads)'), ('C', 36, 'C36 = v2 (88 reads)'),
                    ('CF', 0, 'CF cards (52 reads)'), ('CF', 24, 'CF24 (76 reads)'), ('CF', 48, 'CF48 (100 reads)'),
                    ('NP', 0, 'NP cards (104 reads)'), ('NPL', 0, 'NPL cards (104 reads)')]
            for k, (kind, t, lab) in enumerate(plan):
                for si, start in enumerate(('rand', 'IV')):
                    R, dt = run(p, cov_work, (kind, t, start), 100000, 30_000_000 + 1000 * (2 * k + si))
                    show_cov(f'{lab} {start}', R, dt)
        elif part == 'scan':
            print('D2 scan (100k pairs each; seeds 31_000_000 + 100_000*kind + 1000*t + chunk)')
            plan = [('NP', 0), ('NP', 12), ('NP', 24), ('NP', 36), ('NPL', 0), ('NPL', 24), ('NPL', 48),
                    ('CF', 0), ('CF', 24), ('CF', 48), ('NPr', 13), ('NPr', 26)]
            for kind, t in plan:
                R, dt = run(p, d2_work, (kind, t), 100000, 31_000_000 + 100_000 * KCODE[kind] + 1000 * t)
                M.show_d2(f'{kind}{t}', R, dt)
        elif part == 'scan2':
            print('D2 scan 2 (200k pairs each; seeds 31_000_000 + 100_000*kind + 1000*t + 500 + chunk)')
            for kind, t in [('NPr', 39), ('NPr', 52)]:
                R, dt = run(p, d2_work, (kind, t), 200000, 31_000_000 + 100_000 * KCODE[kind] + 1000 * t + 500)
                M.show_d2(f'{kind}{t}', R, dt)
        elif part == 'scan3':
            print('D2 scan 3, register rule NRr (seeds 31_000_000 + 100_000*kind + 1000*t + 700 + chunk)')
            for t, n in [(0, 100000), (13, 200000), (26, 200000), (39, 200000), (52, 200000)]:
                R, dt = run(p, d2_work, ('NRr', t), n, 31_000_000 + 100_000 * KCODE['NRr'] + 1000 * t + 700)
                M.show_d2(f'NRr{t}', R, dt)
        elif part == 'd1L':
            kind, t, N = args[1], int(args[2]), int(args[3])
            off = int(args[args.index('--seedoff') + 1]) if '--seedoff' in args else 0
            base = 37_000_000 + 100_000 * KCODE[kind] + 1000 * t + off
            print(f'd1L (left flip only; Q = W^-1 W\'\') {kind}{t}: seeds {base}+...; W unchanged = exact prediction')
            R, dt = run(p, d1l_work, (kind, t), N, base)
            lo, hi = L.wilson(R['pred'], R['n'])
            print(f"D1L {kind}{t}: W unchanged {R['pred']} [{lo:.2e},{hi:.2e}]")
            M.show_d2(f'D1L-Q {kind}{t}', R, dt)
        elif part in ('d1', 'd2', 'd3', 'merge'):
            kind, t, N = args[1], int(args[2]), int(args[3])
            off = int(args[args.index('--seedoff') + 1]) if '--seedoff' in args else 0
            base = {'d1': 32, 'd2': 33, 'd3': 34, 'merge': 35}[part] * 1_000_000 + 100_000 * KCODE[kind] + 1000 * t + off
            print(f'{part} {kind}{t}: seeds {base}+... ; cost {W.cost(kind, t) if kind != "C" else L.cost("C", t)}')
            if part == 'd1':
                R, dt = run(p, d1_work, (kind, t), N, base)
                show_d1(f'{kind}{t}', R, dt)
            elif part == 'd2':
                R, dt = run(p, d2_work, (kind, t), N, base)
                M.show_d2(f'{kind}{t}', R, dt)
            elif part == 'd3':
                for si, start in enumerate(('IV', 'rand')):
                    for ci, cls in enumerate(('same', 'opp', 'KA', 'rand')):
                        R, dt = run(p, d3_work, (kind, t, start, cls), N, base + 100 * (4 * si + ci))
                        ub = 1 - 0.05 ** (1 / R['n'])
                        print(f"D3 {kind}{t} start {start:4s} pair {cls:4s} n={R['n']}: card-phase positions equal {R['poseq']}, "
                              f"output collisions {R['coll']} (0-hit 95% bound {ub:.1e}) ex {R['ex'][:2]}  [{dt:.0f}s]")
                        sys.stdout.flush()
            else:
                law = L.moved_law()
                bins = [(0, 40), (41, 44), (45, 46), (47, 47), (48, 48), (49, 49), (50, 50)]
                tot = 0
                hits, peq = [], 0
                H = {'IV': [0] * 51, 'rand': [0] * 51}
                for si, start in enumerate(('IV', 'rand')):
                    for i in POS:
                        R, dt = run(p, merge_work, (kind, t, start, i), N, base + 10000 * si + 100 * i)
                        H[start] = [x + y for x, y in zip(H[start], R['hist'])]
                        hits += R['hits']
                        peq += R['peq']
                        tot += R['hist'] and sum(R['hist'])
                print(f'merge {kind}{t}: {tot} adjacent-swap pairs ({len(POS)} positions {POS} x IV/uniform x {N}); '
                      f'state equal right after the swapped pair {peq}; output collisions {len(hits)}; 0-hit 95% bound per pair '
                      f'{1 - 0.05 ** (1 / tot):.2e}; hits {hits[:5]}')
                for start in H:
                    n = sum(H[start])
                    mean = sum(k * c for k, c in enumerate(H[start])) / n
                    print(f'  {start:4s} differing output slots: mean {mean:.4f} (ideal {M.MMEAN:.4f}); '
                          + '; '.join(f'[{a}-{b}] {sum(H[start][a:b + 1]) / n:.5f} (ideal {float(sum(law[a:b + 1])):.5f})' for a, b in bins))
    print(f'wall time {time.time() - T0:.0f} s, workers {w}')


if __name__ == '__main__':
    main()
