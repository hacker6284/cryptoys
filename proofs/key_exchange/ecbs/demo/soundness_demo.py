"""Soundness of the certificate check at Demo (n = 7), as ../card/soundness_v3.py does for Toy / Hobby /
Serious, but EXHAUSTIVE where Demo allows it.
 FIELD (gf37 tables, cross-checked against PARI): every pair (x, y) in GF(3^7)^2 as the sender's C, with
   the self-consistent A (the card's certificate formulas applied to C).  The card's receiver steps:
   curve test (up times itself vs curve side), run = across minus its cube (reject if empty), slope =
   rise / run, new across, new up, compare.  For every on-curve C the honest A is checked against PARI's
   pi(C) - C; every accepted A is checked to lie in <P> minus O; the multiplicity of each subgroup point is
   counted.  Wrong A's for every on-curve C.  The ladder-and-tally inversion for every nonzero element.
 PEG (homes_demo boards, CARD.md followed literally; the receiver holds its own A in the across and up
   while it rebuilds theirs; C and A are called in from a sender board): every on-curve C with its
   honest A; and sampled classes (C outside <P> with A = C, the 4 order-5 points, A not matching, C off
   the curve).
 CALLING at Demo: let go before every call and resume from the board; stale receiving homes.
Usage: python soundness_demo.py   (writes soundness_demo.json)"""
import sys, os, json, random, time
import numpy as np
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gf37 as F
import homes_demo as D
H, V = D.H, D.V
sys.path.insert(0, os.path.join(HERE, '..', 'card'))
os.chdir(H.ECBS)
import ecbs_exchange as X
os.chdir(HERE)
from soundness import invert_literal, ladder

T = X.Tier('Demo'); R = T.R; l = T.l; Q = F.Q

def card_cert(x, y):
    """the card's certificate on arrays x, y (x not in GF(3)): returns (nx, ny)."""
    x3 = F.cube(x); y3 = F.cube(y); run = F.sub(x, x3)
    g = F.inv(run); rise = F.neg(F.add(y3, y)); s = F.mul(g, rise)
    nx = F.sub(F.add(F.add(F.mul(s, s), F.ONE), x3), run)
    ny = F.sub(F.mul(s, F.sub(x3, nx)), y3)
    return nx, ny

def field():
    out = {'selftest_vs_PARI': F.selftest()}
    xs, ys = np.meshgrid(np.arange(Q), np.arange(Q), indexing='ij'); xs = xs.ravel(); ys = ys.ravel()
    b = F.add(F.sub(F.mul(ys, ys), F.cube(xs)), F.mul(xs, xs))         # b' = y^2 - x^3 + x^2
    oncurve = b == F.ONE
    xin3 = F.cube(xs) == xs                                              # x in GF(3)  <=>  run empty
    out['pairs'] = int(len(xs)); out['on_curve_affine'] = int(oncurve.sum())
    out['empty_run_on_curve'] = int((oncurve & xin3).sum())
    ok = ~xin3
    nx, ny = card_cert(xs[ok], ys[ok])
    # honest A for on-curve C, checked against PARI pi(C) - C
    idx = np.nonzero(oncurve & ~xin3)[0]; pos = {int(i): j for j, i in enumerate(np.nonzero(ok)[0])}
    pari_ok = 0; in_sub = 0; mult = {}
    for i in idx:
        C = R.pt((['.WR'[d] for d in F.DIG[xs[i]]], ['.WR'[d] for d in F.DIG[ys[i]]]))
        Ap = R.add(R.frob(C), R.neg(C)); j = pos[int(i)]
        A = (int(nx[j]), int(ny[j]))
        pari_ok += len(Ap) == 2 and (F.to_int(Ap[0]), F.to_int(Ap[1])) == A
        in_sub += len(R.mul(l, Ap)) == 1 and len(Ap) == 2
        mult[A] = mult.get(A, 0) + 1
    out['honest'] = dict(accept=int(len(idx)), empty=out['empty_run_on_curve'], A_equals_PARI_piC_minus_C=pari_ok,
                         accepted_A_in_subgroup_minus_O=in_sub, distinct_accepted_A=len(mult),
                         multiplicity_of_each=sorted(set(mult.values())))
    # every on-curve C with the 4 order-5 points: run empty
    gf3 = [(int(a), int(c)) for a, c in zip(xs[oncurve & xin3], ys[oncurve & xin3])]
    out['order5_points'] = [(''.join('.WR'[d] for d in F.DIG[a]), ''.join('.WR'[d] for d in F.DIG[c])) for a, c in gf3]
    # wrong A for every non-empty on-curve C: -A, A = C, one peg changed, another subgroup point
    rng = np.random.default_rng(11); mism = 0; trials = 0
    Ax = nx[[pos[int(i)] for i in idx]]; Ay = ny[[pos[int(i)] for i in idx]]
    subs = list(mult.keys())
    for k, i in enumerate(idx):
        cands = [(int(Ax[k]), int(F.neg(Ay[k]))), (int(xs[i]), int(ys[i]))]
        d = F.DIG[Ax[k]].copy(); h = rng.integers(7); d[h] = (d[h] + rng.integers(1, 3)) % 3
        cands.append((int(d @ F.P3), int(Ay[k])))
        while True:
            o = subs[rng.integers(len(subs))]
            if o != (int(Ax[k]), int(Ay[k])): break
        cands.append(o)
        for c in cands:
            trials += 1; mism += c != (int(Ax[k]), int(Ay[k]))
    out['A_not_matching'] = dict(trials=trials, mismatch=mism)
    # off the curve, A = the card formulas on C
    off = ~oncurve
    out['off_curve'] = dict(pairs=int(off.sum()), rejected_by_curve_test=int(off.sum()),
                            would_pass_without_curve_test=int((off & ~xin3).sum()),
                            run_empty_without_curve_test=int((off & xin3).sum()))
    # the ladder-and-tally inversion, every nonzero element
    ir = ladder(T.n - 1); bad = 0
    for a in range(1, Q):
        e = F.to_el(a); bad += F.to_int(invert_literal(e, ir)) != int(F.inv(np.array([a]))[0])
    out['ladder'] = ''.join(ir); out['inversion_wrong_of_2186'] = bad
    return out, (xs, ys, oncurve, xin3, nx, ny, ok)

def peg(field_data, rnd):
    xs, ys, oncurve, xin3, nx, ny, ok = field_data
    reg = lambda a: ['.WR'[d] for d in F.DIG[a]]
    pos = {int(i): j for j, i in enumerate(np.nonzero(ok)[0])}
    def cert_of(i):
        if xin3[i]: return (['.'] * 7, ['.'] * 7)
        j = pos[int(i)]; return reg(nx[j]), reg(ny[j])
    def receiver(Cr, Ar):
        hb = D.HBDemo()
        mine = R.unpt(R.mul((T.lam - 1) * rnd.randrange(1, l) % l, T.Pref)); hb.put('across', mine[0]); hb.put('up', mine[1])
        snd = D.HBDemo(); snd.put('across', list(Cr[0])); snd.put('up', list(Cr[1]))
        V.call_session(hb, snd, rnd)
        m0 = hb.moves
        if not H.on_curve(hb): v = 'curve'
        else:
            try:
                V.certificate(hb, 'base across', 'base up')
                hb.cr.phase_drop(); hb.cr.phase_drop()
                snd.clear('across'); snd.clear('up'); snd.put('across', list(Ar[0])); snd.put('up', list(Ar[1]))
                V.call_session(hb, snd, rnd)
                okm = V.receive_certificate(hb); hb.clear('bottom'); hb.clear('gap')
                v = 'accept' if okm else 'mismatch'
                if okm:
                    C = R.pt(Cr); assert R.pt((hb.value('base across'), hb.value('base up'))) == R.add(R.frob(C), R.neg(C))
            except V.EmptyCertificate:
                v = 'empty'
        return v, hb.peak, hb.moves - m0, hb.cr.highest if hasattr(hb.cr, 'highest') else hb.cr.max_hole
    out = {}
    def run(label, items):
        res = {'trials': 0, 'accept': 0, 'curve': 0, 'empty': 0, 'mismatch': 0, 'peak': 0, 'max_check_moves': 0, 'highest_control_hole': 0}
        for Cr, Ar in items:
            v, pk, mv, hh = receiver(Cr, Ar); res['trials'] += 1; res[v] += 1
            res['peak'] = max(res['peak'], pk); res['max_check_moves'] = max(res['max_check_moves'], mv)
            res['highest_control_hole'] = max(res['highest_control_hole'], hh)
        out[label] = res
    on = np.nonzero(oncurve)[0]
    run('every on-curve C, honest A', [((reg(xs[i]), reg(ys[i])), cert_of(i)) for i in on])
    sub = lambda i: len(R.mul(l, R.pt((reg(xs[i]), reg(ys[i]))))) == 1
    outs = [i for i in on if not xin3[i] and not sub(i)]
    pick = rnd.sample(outs, 200)
    run('C outside <P>, A = C', [((reg(xs[i]), reg(ys[i])), (reg(xs[i]), reg(ys[i]))) for i in pick])
    run('C outside <P>, correct certificate', [((reg(xs[i]), reg(ys[i])), cert_of(i)) for i in pick])
    o5 = [i for i in on if xin3[i]]
    hon = lambda: R.unpt(R.mul(rnd.randrange(1, l), T.Pref))
    run('C = nonzero order-5 point', [((reg(xs[i]), reg(ys[i])), A) for i in o5 for A in ((['.'] * 7, ['.'] * 7), hon())])
    mm = []
    for k in range(300):
        i = rnd.choice([i for i in on if not xin3[i]]); Ac = cert_of(i)
        if k % 3 == 0: A = (Ac[0], [{'W': 'R', 'R': 'W', '.': '.'}[c] for c in Ac[1]])
        elif k % 3 == 1:
            A = [list(Ac[0]), list(Ac[1])]; h = rnd.randrange(7); A[0][h] = rnd.choice([c for c in '.WR' if c != A[0][h]])
        else:
            while True:
                A = hon()
                if tuple(map(tuple, A)) != tuple(map(tuple, Ac)): break
        mm.append(((reg(xs[i]), reg(ys[i])), A))
    run('A not matching pi(C) - C', mm)
    offs = np.nonzero(~oncurve & ~xin3)[0]
    pick = [int(offs[j]) for j in np.random.default_rng(5).choice(len(offs), 300, replace=False)]
    run('C off the curve, A = the card formulas on C', [((reg(xs[i]), reg(ys[i])), cert_of(i)) for i in pick])
    return out

def calling(rnd):
    n = 7
    def pair():
        snd = D.HBDemo(); rec = D.HBDemo()
        for h in ('across', 'up'): snd.put(h, R.rand_el(rnd))
        for h in ('across', 'up'): rec.put(h, R.rand_el(rnd))
        return snd, rec
    snd, rec = pair(); rec.put('base up', R.rand_el(rnd))
    V.start_calling(rec); k = 0
    while rec.cr.row[rec.cr.calling] == 'W':
        dst, i = rec.cursor; src = dict(V.plan_for(rec))[dst]
        if rec.home[dst] is not None:
            assert rec.home[dst][:i] == snd.home[src][:i] and all(c == '.' for c in rec.home[dst][i:])
        V.call_step(rec, snd); k += 1
    ok_a = k == 2 * n and rec.home['base across'] == snd.home['across'] and rec.home['base up'] == snd.home['up']
    trials = 200; wrong_noclear = wrong_rule = 0
    for _ in range(trials):
        snd, rec = pair(); stale = (R.rand_el(rnd), R.rand_el(rnd))
        lay = lambda old, band: [b if b != '.' else o for o, b in zip(old, band)]
        wrong_noclear += lay(stale[0], snd.home['across']) != snd.home['across'] or lay(stale[1], snd.home['up']) != snd.home['up']
        rec.put('base across', list(stale[0])); rec.put('base up', list(stale[1]))
        V.call_session(rec, snd, rnd)
        wrong_rule += rec.home['base across'] != snd.home['across'] or rec.home['base up'] != snd.home['up']
    cs = {h: [D.coord_demo(h, i) for i in range(n)] for h in H.HOMES}
    allc = [c for v in cs.values() for c in v]
    return dict(resume_every_hole=ok_a, calls_in_session=k, stale_trials=trials,
                stale_copy_wrong_without_clearing=wrong_noclear, stale_copy_wrong_with_rule=wrong_rule,
                homes_disjoint=len(set(allc)) == len(allc),
                never_control_rows_I_J=all(c[1][0] not in 'IJ' for c in allc),
                never_lane_1=all(int(c[1][1:]) > 2 for c in allc),
                published_bands={h: f"grid {cs[h][0][0]}, {cs[h][0][1]} .. {cs[h][-1][1]}" for h in ('across', 'up')})

if __name__ == '__main__':
    t0 = time.time(); rnd = random.Random(20261003)
    f, data = field(); print('FIELD', json.dumps(f, indent=1), flush=True)
    p = peg(data, rnd); print('PEG', json.dumps(p, indent=1), flush=True)
    c = calling(rnd); print('CALLING', json.dumps(c, indent=1), flush=True)
    json.dump(dict(field=f, peg=p, calling=c, secs=round(time.time() - t0, 1)), open(os.path.join(HERE, 'soundness_demo.json'), 'w'), indent=1)
    print('secs', round(time.time() - t0, 1))
