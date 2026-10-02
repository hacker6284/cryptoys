"""(b) diffusion curve and (c) candidate fixes: the two known distinguishers, seeded.

D2 (secret start, A2 setting): h uniform secret, D uniform, D' = D with cards 51,52 swapped;
   z = y^-1 y'.  Statistics: P(fixE>=2), P(fixC>=2) (fixed edge / corner slots, orientation
   ignored), mean moved slots (orientation counted; = #differing slots), chi-square of the edge
   and corner cycle types and of the fixE / fixC histograms against the exact uniform laws.
D1 (free start / A1 setting): secret uniform deck K, chosen uniform h, h' = h with 2 random edge
   slots flipped; y = f(h,K), y' = f(h',K).  pred = [y' == h' (h^-1 y h^-1) h']; Q = M^-1 M' with
   M = h^-1 y h^-1: P(fixE>=2), P(fixC>=2), mean moved, against the uniform law.
U  unread pieces of h per block (rules Ct only; the sweep reads every piece by construction).
Usage: python3 mdfix_dist.py PART [--workers 4]   PART in {b, c, slowcheck}
"""
import math
import random
import sys
import time
from collections import Counter
from multiprocessing import Pool

import mdfix_lib as L

CH = 10
LAWE, LAWC = L.fix_law(30), L.fix_law(20)
P2E, P2C = float(1 - LAWE[0] - LAWE[1]), float(1 - LAWC[0] - LAWC[1])
ML = L.moved_law()
MMEAN = float(sum(k * p for k, p in enumerate(ML)))
CPE, CPC = L.class_probs(30), L.class_probs(20)


def d2_work(a):
    kind, t, n, seed = a
    dm = L.make_dm(kind, t)
    rng = random.Random(seed)
    fe, fc, mv, mv2 = 0, 0, 0, 0
    he, hc, ce, cc = Counter(), Counter(), Counter(), Counter()
    for _ in range(n):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        d2 = list(d)
        d2[50], d2[51] = d2[51], d2[50]
        z = L.compose_st(L.inv_st(dm(h, d)), dm(h, d2))
        a1, a2, m = L.fixe(z), L.fixc(z), L.moved(z)
        fe += a1 >= 2
        fc += a2 >= 2
        mv += m
        mv2 += m * m
        he[a1] += 1
        hc[a2] += 1
        ce[L.cyc_e(z)] += 1
        cc[L.cyc_c(z)] += 1
    return dict(n=n, fe=fe, fc=fc, mv=mv, mv2=mv2, he=he, hc=hc, ce=ce, cc=cc)


def d1_work(a):
    kind, t, n, seed = a
    dm = L.make_dm(kind, t)
    rng = random.Random(seed)
    pred = fe = fc = mv = mv2 = sfe = sfc = 0
    for _ in range(n):
        K = list(range(52))
        rng.shuffle(K)
        h = L.uniform_st(rng)
        e1, e2 = rng.sample(range(30), 2)
        h2 = list(h)
        h2[20 + e1] ^= 1
        h2[20 + e2] ^= 1
        y, y2 = dm(h, K), dm(h2, K)
        hi, h2i = L.inv_st(h), L.inv_st(h2)
        M = L.compose_st(hi, L.compose_st(y, hi))
        M2 = L.compose_st(h2i, L.compose_st(y2, h2i))
        pred += L.compose_st(h2, L.compose_st(M, h2)) == y2
        Q = L.compose_st(L.inv_st(M), M2)
        m = L.moved(Q)
        a1, a2 = L.fixe(Q), L.fixc(Q)
        fe += a1 >= 2
        fc += a2 >= 2
        sfe += a1
        sfc += a2
        mv += m
        mv2 += m * m
    return dict(n=n, pred=pred, fe=fe, fc=fc, mv=mv, mv2=mv2, sfe=sfe, sfc=sfc)


def unread_work(a):
    t, n, seed = a
    rng = random.Random(seed)
    uc = ue = anyu = 0
    slot_ue = [0] * 30
    for _ in range(n):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        rec = []
        L.E.run(list(h), d, f3=False, rec=rec)  # card phase reads (gi ends where cards() does)
        st = list(h)
        gi = L.cards(st, d)
        for r in range(1, t + 1):
            op, rd, _, _ = L.F3[r & 1][gi]
            L.apply(st, op)
            s, tab = rd[0]
            rec.append((s, st[s]))
            gi = tab[st[s]]
        hs = L.eng.read_hslots(h, rec)
        RC = {s for k, s in hs if k == 'c'}
        RE = {s for k, s in hs if k == 'e'}
        uc += 20 - len(RC)
        ue += 30 - len(RE)
        anyu += len(RC) < 20 or len(RE) < 30
        for s in range(30):
            slot_ue[s] += s not in RE
    return dict(n=n, uc=uc, ue=ue, anyu=anyu, slot_ue=slot_ue)


def merge(rs):
    out = {}
    for k, v in rs[0].items():
        if isinstance(v, Counter):
            c = Counter()
            for r in rs:
                c.update(r[k])
            out[k] = c
        elif k in ('ex', 'hits'):          # lists of examples are concatenated (2026-10-01 fix: 'hits' was summed)
            out[k] = sum((r[k] for r in rs), [])
        elif isinstance(v, list):
            out[k] = [sum(r[k][j] for r in rs) for j in range(len(v))]
        else:
            out[k] = sum(r[k] for r in rs)
    return out


def hist_chi(cnt, law, top):
    """chi-square of a histogram vs law over bins 0..top-1, top+ pooled."""
    from scipy.stats import chi2 as C2
    n = sum(cnt.values())
    x2 = 0.0
    for j in range(top):
        e = float(law[j]) * n
        x2 += (cnt.get(j, 0) - e) ** 2 / e
    e = float(1 - sum(law[:top])) * n
    o = n - sum(cnt.get(j, 0) for j in range(top))
    x2 += (o - e) ** 2 / e
    return x2, top, float(C2.sf(x2, top))


def show_d2(name, R, dt):
    n = R['n']
    lo, hi = L.wilson(R['fe'], n)
    loc, hic = L.wilson(R['fc'], n)
    m = R['mv'] / n
    sd = math.sqrt(max(R['mv2'] / n - m * m, 0) * n / (n - 1))
    xe = L.chi2_cycletype(R['ce'], CPE)
    xc = L.chi2_cycletype(R['cc'], CPC)
    fe_x = hist_chi(R['he'], LAWE, 5)
    fc_x = hist_chi(R['hc'], LAWC, 5)
    print(f"D2 {name:8s} n={n:7d}  P(fixE>=2) {R['fe'] / n:.4f} [{lo:.4f},{hi:.4f}] adv {R['fe'] / n - P2E:+.4f}"
          f" | P(fixC>=2) {R['fc'] / n:.4f} [{loc:.4f},{hic:.4f}] adv {R['fc'] / n - P2C:+.4f}"
          f" | mean fixE {sum(k * c for k, c in R['he'].items()) / n:.4f}, fixC {sum(k * c for k, c in R['hc'].items()) / n:.4f} (ideal 1 +-{1.96 / math.sqrt(n):.4f})"
          f" | mean moved {m:.4f} +- {1.96 * sd / math.sqrt(n):.4f} (ideal {MMEAN:.4f}, diff {m - MMEAN:+.4f})"
          f" | chi2 cyc-type E {xe[0]:.1f}/{xe[1]} p={xe[2]:.2g}, C {xc[0]:.1f}/{xc[1]} p={xc[2]:.2g}"
          f" | chi2 fixE-hist p={fe_x[2]:.2g}, fixC-hist p={fc_x[2]:.2g}  [{dt:.0f}s]")
    sys.stdout.flush()


def show_d1(name, R, dt):
    n = R['n']
    lo, hi = L.wilson(R['pred'], n)
    a, b = L.wilson(R['fe'], n)
    c, d = L.wilson(R['fc'], n)
    m = R['mv'] / n
    sd = math.sqrt(max(R['mv2'] / n - m * m, 0) * n / (n - 1))
    print(f"D1 {name:8s} n={n:7d}  prediction success {R['pred']}/{n} = {R['pred'] / n:.5f} [{lo:.5f},{hi:.5f}]"
          f" | Q: P(fixE>=2) {R['fe'] / n:.4f} [{a:.4f},{b:.4f}] adv {R['fe'] / n - P2E:+.4f}"
          f", P(fixC>=2) {R['fc'] / n:.4f} [{c:.4f},{d:.4f}] adv {R['fc'] / n - P2C:+.4f}"
          f", mean fixE {R['sfe'] / n:.4f}, mean fixC {R['sfc'] / n:.4f} (ideal 1, sd 1 => +-{1.96 / math.sqrt(n):.4f})"
          f", mean moved {m:.4f} +- {1.96 * sd / math.sqrt(n):.4f} (ideal {MMEAN:.4f})  [{dt:.0f}s]")
    sys.stdout.flush()


def run(p, fn, cfg, n, seed0):
    t0 = time.time()
    R = merge(p.map(fn, [cfg + (n // CH, seed0 + c) for c in range(CH)]))
    return R, time.time() - t0


def slowcheck():
    """SWA / SWB / SWBh fast == a slow composition of m9_search primitives (positions,
    face_turn, vnoon, read_slot, read_colours_piece, em_block for cards and F3 rounds)."""
    rng = random.Random(4242)
    ok = 0
    cfgs = [('SWA', 36), ('SWB', 12), ('SWB', 36), ('SWBh', 36)]
    for trial in range(16):
        kind, t = cfgs[trial % 4]
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        y = slow_dm(kind, t, h, d)
        fast = L.make_dm(kind, t)(h, d)
        ok += L.eng.as_tuple_pos(L.eng.from_st(fast)) == y
    print(f'slowcheck: fast SWA/SWB/SWBh == slow composition from m9_search primitives: {ok}/16')
    assert ok == 16


def slow_dm(kind, t, h, d):
    ref, eng = L.ref, L.eng
    if kind == 'C':
        hp = eng.as_tuple_pos(eng.from_st(h))
        return ref.compose(hp, ref.em_block(hp, d, t=t))
    if True:
        hp = eng.as_tuple_pos(eng.from_st(h))
        grips = []
        X = ref.em_block(hp, d, t=(t if kind == 'SWA' else 0), grips=grips)
        o = tuple(range(12)) if kind == 'SWBh' else tuple(grips[-1])
        B = eng.as_tuple_pos(eng.inverse([list(x) for x in hp]))
        seen = set()
        for p in range(12):
            f = o[p]
            noon = ref.vnoon(p, o)
            nb = list(eng.NBRS[f])
            k = nb.index(noon)
            nb = nb[k:] + nb[:k]
            for i in range(5):
                for pos in (2, 1):            # edge (even pos), then corner (odd pos)
                    kd, s = ref.read_slot(f, nb[i], pos)
                    if (kd, s) in seen:
                        continue
                    seen.add((kd, s))
                    piece, ori = (X[0][s], X[1][s]) if kd == 'c' else (X[2][s], X[3][s])
                    c1, c2 = ref.read_colours_piece(kd, s, piece, ori, f, nb[i])
                    B = ref.face_turn(B, c1, 1)
                    B = ref.face_turn(B, c2, 1)
        assert len(seen) == 50
        if kind != 'SWA':
            B = ref.em_block(B, [], t=t)
        return ref.compose(eng.as_tuple_pos(eng.inverse([list(x) for x in B])), X)


TELE = [(2, 49), (1, 50), (2, 26)]   # A-spade K-heart, A-heart K-spade, A-spade 7-spade (SPEC 8)


def d3_work(a):
    """Telescoping pair at deal positions 51,52 (both orders), IV or uniform start: how often the
    card-phase POSITIONS are equal, and output collisions for each candidate."""
    start, cands, n, seed = a
    rng = random.Random(seed)
    poseq = 0
    coll = [0] * len(cands)
    ex = []
    for _ in range(n):
        h = L.IV_ST if start == 'IV' else L.uniform_st(rng)
        a1, b1 = rng.choice(TELE)
        rest = [c for c in range(52) if c not in (a1, b1)]
        rng.shuffle(rest)
        d = rest + [a1, b1]
        d2 = rest + [b1, a1]
        X, X2 = list(h), list(h)
        L.cards(X, d)
        L.cards(X2, d2)
        pe = X == X2
        poseq += pe
        for j, (kind, t) in enumerate(cands):
            dm = L.make_dm(kind, t)
            c = dm(h, d) == dm(h, d2)
            coll[j] += c
            if c and len(ex) < 3:
                ex.append((kind, t, start, list(h) if start == 'rand' else 'IV', d, d2))
    return dict(n=n, poseq=poseq, coll=coll, ex=ex)


def main():
    part = sys.argv[1]
    w = int(sys.argv[sys.argv.index('--workers') + 1]) if '--workers' in sys.argv else 4
    print('\n'.join(L.selftest()))
    slowcheck()
    print(f'Ideal (exact, uniform z): P(fixE>=2) {P2E:.6f}, P(fixC>=2) {P2C:.6f}, mean moved {MMEAN:.4f}; '
          f'cycle-type chi-square: exact class probabilities 2/z_lambda on A_30 / A_20, classes with expected < 20 pooled')
    T0 = time.time()
    with Pool(w) as p:
        if part == 'b':
            print('(b) diffusion curve, v2 card rule with t F3 rounds (Ct); D2 statistic; seeds 5_000_000 + 1000 t + chunk')
            plan = [(0, 50000), (4, 50000), (8, 100000), (12, 200000), (18, 200000), (24, 400000),
                    (36, 400000), (48, 400000), (60, 400000), (76, 1000000), (100, 1000000)]
            for t, n in plan:
                R, dt = run(p, d2_work, ('C', t), n, 5_000_000 + 1000 * t)
                show_d2(f'C t={t}', R, dt)
        elif part == 'c':
            print('(c1) unread pieces of h per block, rules Ct (20,000 blocks each; seeds 6_000_000 + 1000 t + chunk)')
            for t in (36, 48, 60, 76, 100):
                R, dt = run(p, unread_work, (t,), 20000, 6_000_000 + 1000 * t)
                n = R['n']
                lo, hi = L.wilson(R['anyu'], n)
                su = R['slot_ue']
                print(f"U  C t={t:3d}: P(>=1 unread piece) {R['anyu'] / n:.4f} [{lo:.4f},{hi:.4f}]; "
                      f"mean unread corners {R['uc'] / n:.3f}, edges {R['ue'] / n:.3f}; per-edge-slot unread "
                      f"frequency min {min(su) / n:.3f} max {max(su) / n:.3f}  [{dt:.0f}s]")
            print('U  SWA/SWB/SWBh: every piece of h is read by the sweep (PROVED: the tour reads all 50 slots of '
                  'X = W h, a relabelling of h; checked: tour covers 50 slots)')
            print('(c0) D3 telescoping pair at positions 51,52 (seeds 9_000_000 + 1000*s + chunk)')
            d3c = [('C', 36), ('SWBh', 36), ('SWB', 36)]
            for si, start in enumerate(['IV', 'rand']):
                R, dt = run(p, d3_work, (start, d3c), 200000, 9_000_000 + 1000 * si)
                n = R['n']
                print(f"D3 {start:4s} n={n}: card-phase positions equal {R['poseq']} ({R['poseq'] / n:.5f}); output collisions "
                      + ', '.join(f"{k}{t} {c}" for (k, t), c in zip(d3c, R['coll'])) + f"  [{dt:.0f}s]")
                for e in R['ex'][:2]:
                    kind, t, st0, hh, d, d2 = e
                    hh = L.IV_ST if hh == 'IV' else hh
                    v = slow_dm(kind, t, hh, d) == slow_dm(kind, t, hh, d2)
                    print(f'   example collision ({kind}{t}, start {st0}; slow reference equal: {v}): h =',
                          'IV-COOK12' if st0 == 'IV' else hh, 'D =', d, "D' =", d2)
            print('(c2) D1 free-start 2-query test (seeds 7_000_000 + 1000*k + chunk)')
            cands = [('C', 36), ('C', 48), ('C', 60), ('C', 76), ('C', 100), ('SWA', 36), ('SWB', 12),
                     ('SWB', 36), ('SWB', 60), ('SWB', 76), ('SWB', 100)]
            for k, (kind, t) in enumerate(cands):
                nn = 400000 if kind == 'SWB' and t >= 36 else 200000
                R, dt = run(p, d1_work, (kind, t), nn, 7_000_000 + 1000 * k)
                show_d1(f'{kind}{t}', R, dt)
            print('(c3) D2 secret-start test on the sweep candidates (Ct are in part b; seeds 8_000_000 + 1000*k + chunk)')
            for k, (kind, t) in enumerate([('SWA', 36), ('SWB', 12), ('SWB', 36), ('SWB', 76)]):
                R, dt = run(p, d2_work, (kind, t), 400000 if t < 76 else 1000000, 8_000_000 + 1000 * k)
                show_d2(f'{kind}{t}', R, dt)
            print('cost per block (SPEC 5.7 model):')
            cands = cands + [('SWBh', 36)]
            for kind, t in cands:
                print(f'  {kind}{t}: {L.cost(kind, t)}')
        if part == 'f':
            kind, t = sys.argv[2], int(sys.argv[3])
            print(f'(f) validation of the down-selected candidate {kind}{t}')
            R, dt = run(p, d1_work, (kind, t), 1000000, 16_000_000 + 1000 * t)
            show_d1(f'{kind}{t}', R, dt)
            R, dt = run(p, d2_work, (kind, t), 1000000, 17_000_000 + 1000 * t)
            show_d2(f'{kind}{t}', R, dt)
            for si, start in enumerate(['IV', 'rand']):
                R, dt = run(p, d3_work, (start, [(kind, t)]), 200000, 18_000_000 + 1000 * si)
                print(f"D3 {start:4s} n={R['n']}: card-phase positions equal {R['poseq']}; output collisions {kind}{t} {R['coll'][0]}  [{dt:.0f}s]")
            print(f'  cost {kind}{t}: {L.cost(kind, t)}')
        if part == 'e':
            print('(e) F3b rounds (Up +1, read at once, Front +1, re-grip): decay and the sweep with F3b on B')
            for k, (t, n) in enumerate([(12, 200000), (24, 400000), (36, 400000), (48, 400000)]):
                R, dt = run(p, d2_work, ('Cb', t), n, 12_000_000 + 1000 * t)
                show_d2(f'Cb t={t}', R, dt)
            for k, t in enumerate([24, 36, 48]):
                R, dt = run(p, d1_work, ('SWBb', t), 400000, 13_000_000 + 1000 * t)
                show_d1(f'SWBb{t}', R, dt)
            for t in (48,):
                R, dt = run(p, d2_work, ('SWBb', t), 1000000, 14_000_000 + 1000 * t)
                show_d2(f'SWBb{t}', R, dt)
            R, dt = run(p, d3_work, ('rand', [('SWBb', 48)]), 200000, 15_000_000)
            print(f"D3 rand n={R['n']}: card-phase positions equal {R['poseq']}; output collisions SWBb48 {R['coll'][0]}  [{dt:.0f}s]")
            for kind, t in [('Cb', 36), ('SWBb', 36), ('SWBb', 48)]:
                print(f'  cost {kind}{t}: {L.cost(kind, t)}')
    print(f'wall time {time.time() - T0:.0f} s, workers {w}')


if __name__ == '__main__':
    main()
