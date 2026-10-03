"""Soundness of the v3 certificate check, two levels.
 FIELD: PARI field elements, the card's steps written literally (curve side, run = across minus its cube,
        reject if empty, ladder-and-tally inversion, rise, slope, Frobenius, new across, new up, compare).
 PEG:   homes_v3 boards, card followed literally (receiver holds its own A in the across and up while it
        rebuilds theirs in the base bands).
Attack classes: honest; C outside the subgroup (with the correct certificate, and with a wrong one);
the 4 nonzero order-5 points (with several A's); A not matching pi(C) - C; C off the curve.
The receiver's verdict is one of accept / 'curve' / 'empty' / 'mismatch'."""
import sys, os, random, time, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H, homes_v3 as V
os.chdir(H.ECBS)
import ecbs_exchange as X
from ecbs_ref import pari
os.chdir(HERE)
from soundness import invert_literal, ladder

def field_receiver(T, C, A, ir):
    R = T.R; x, y = C; one = R.w ** 0
    if y * y != x ** 3 - x * x + one: return 'curve', None          # curve side vs up times itself
    run = x - x ** 3
    if run == 0: return 'empty', None
    g = invert_literal(run, ir)
    rise = -(y ** 3 + y)
    s = g * rise
    x1, y1 = x ** 3, y ** 3
    nx = s * s + one + x1 - run
    ny = s * (x1 - nx) - y1
    if nx != A[0] or ny != A[1]: return 'mismatch', (nx, ny)
    return 'accept', (nx, ny)

def field_cert_formula(T, C, ir):
    """the attacker's 'consistent' certificate for any (x, y), on the curve or not: the card's formulas."""
    R = T.R; x, y = C; one = R.w ** 0; run = x - x ** 3
    s = invert_literal(run, ir) * (-(y ** 3 + y)); x1, y1 = x ** 3, y ** 3; nx = s * s + one + x1 - run
    return nx, s * (x1 - nx) - y1

def gens(T, rnd):
    R = T.R; E = R.E; l = T.l; w = R.w; one = w ** 0; zero = 0 * w
    gf3 = [pari([zero, one]), pari([zero, -one]), pari([one, one]), pari([one, -one])]
    for t in gf3: assert R.on(t) and len(R.mul(5, t)) == 1 and R.frob(t) == t
    sub = lambda P: len(R.mul(l, P)) == 1
    def honest(): return R.mul(rnd.randrange(1, l), T.Pref)
    def plusT(): return R.add(honest(), gf3[rnd.randrange(4)])
    def rand_out():
        while True:
            P = pari.random(E)
            if len(P) == 2 and not sub(P): return P
    def off_curve():
        while True:
            P = pari([pari.random(w), pari.random(w)])
            if not R.on(P): return P
    def tweak(P):                                                   # change one peg of one coordinate
        reg = [list(P[0 if i == 0 else 1]) for i in (0, 1)]
        return reg
    return gf3, sub, honest, plusT, rand_out, off_curve

def pi_minus_1(R, C): return R.add(R.frob(C), R.neg(C))

def one_peg_off(T, A, rnd):
    R = T.R; reg = [list(r) for r in R.unpt(A)]; c = rnd.randrange(2); i = rnd.randrange(T.n)
    reg[c][i] = rnd.choice([z for z in '.WR' if z != reg[c][i]])
    return R.el(reg[0]), R.el(reg[1])

def field_level(name, N, rnd):
    T = X.Tier(name); R = T.R; l = T.l; ir = ladder(T.n - 1)
    gf3, sub, honest, plusT, rand_out, off_curve = gens(T, rnd)
    out = {}
    def tally(label, trials):
        res = {'trials': 0, 'accept': 0, 'curve': 0, 'empty': 0, 'mismatch': 0}
        extra = {}
        for C, A, note in trials:
            v, used = field_receiver(T, (C[0], C[1]), (A[0], A[1]), ir)
            res['trials'] += 1; res[v] += 1
            if v == 'accept':
                Ap = pari([used[0], used[1]])
                extra['accepted_A_in_subgroup'] = extra.get('accepted_A_in_subgroup', 0) + (R.on(Ap) and sub(Ap))
                extra['accepted_A_equals_pari_piC_minus_C'] = extra.get('accepted_A_equals_pari_piC_minus_C', 0) + (Ap == pi_minus_1(R, C))
            if note: extra[note] = extra.get(note, 0) + 1
            if len(C) == 2 and R.on(C):                             # empty run <=> C fixed by Frobenius
                assert (C[0] - C[0] ** 3 == 0) == (R.frob(C) == C) == (len(R.mul(5, C)) == 1)
        res.update(extra); out[label] = res
    t0 = time.time()
    tally('honest', [(C, pi_minus_1(R, C), None) for C in (honest() for _ in range(N))])
    def outside():
        C = plusT() if rnd.random() < .5 else rand_out(); assert not sub(C); return C
    tally('C outside subgroup, correct certificate', [(C, pi_minus_1(R, C), None) for C in (outside() for _ in range(N))])
    def outside_bad():
        C = outside(); k = rnd.randrange(3)
        A = [C, rand_out(), R.neg(pi_minus_1(R, C))][k]
        return C, A, ['A = C', 'A = random non-subgroup point', 'A = minus the certificate'][k]
    tally('C outside subgroup, wrong certificate', [outside_bad() for _ in range(N)])
    empty_bands = (0 * R.w, 0 * R.w)
    o5 = []
    for t in gf3:
        for A, note in ((empty_bands, 'A = empty bands'), (t, 'A = C'), (honest(), 'A = random subgroup point'),
                        (honest(), 'A = another subgroup point')):
            o5.append((t, A, note))
    tally('C = nonzero order-5 point', o5)
    def mism():
        C = honest(); Ac = pi_minus_1(R, C); k = rnd.randrange(5)
        if k == 0: A = honest()
        elif k == 1: A = R.neg(Ac)
        elif k == 2: A = one_peg_off(T, Ac, rnd)
        elif k == 3: A = C
        else: A = rand_out()
        if k != 2 and A == Ac: return mism()
        return C, A, ['A = random subgroup point', 'A = minus the certificate', 'A = certificate with one peg changed', 'A = C', 'A = non-subgroup point'][k]
    tally('A not matching pi(C) - C', [mism() for _ in range(N)])
    def offc():
        if rnd.random() < .5:
            C = off_curve(); note = 'random (x, y)'
        else:
            h = honest(); C = pari([h[0], h[1] + R.w ** rnd.randrange(T.n)]); note = 'honest C, y nudged'
            if R.on(C): return offc()
        A = field_cert_formula(T, (C[0], C[1]), ir) if C[0] != C[0] ** 3 else (0 * R.w, 0 * R.w)
        return C, A, note
    oc = [offc() for _ in range(N)]
    tally('C off the curve (A = the card formulas on C)', oc)
    # without the curve test, how many off-curve C would pass?  (shows the curve test does the rejecting)
    passed = 0
    for C, A, _ in oc:
        x, y = C[0], C[1]
        if x == x ** 3: continue
        passed += field_cert_formula(T, (x, y), ir) == (A[0], A[1])
    out['C off the curve (A = the card formulas on C)']['would_pass_without_curve_test'] = passed
    # inversion sanity
    bad = 0
    for _ in range(N):
        z = pari.random(R.w)
        if z != 0: bad += invert_literal(z, ir) * z != 1
    out['inversion_wrong'] = bad
    out['secs'] = round(time.time() - t0, 1)
    return out

def peg_level(name, N, rnd):
    T = X.Tier(name); R = T.R; l = T.l; ir = ladder(T.n - 1)
    gf3, sub, honest, plusT, rand_out, off_curve = gens(T, rnd)
    out = {}
    def receiver(C, A):
        """receiver board: its own A (honest) in the across and up; their C called into the base bands."""
        hb = V.HB3(name, T.n, T.k)
        mine = pi_minus_1(R, honest()); Mr = R.unpt(mine); hb.put('across', Mr[0]); hb.put('up', Mr[1])
        Cr = R.unpt(C); Ar = R.unpt(pari([A[0], A[1]])) if not (A[0] == 0 and A[1] == 0) else (['.'] * T.n, ['.'] * T.n)
        snd = V.HB3(name, T.n, T.k); snd.put('across', list(Cr[0])); snd.put('up', list(Cr[1]))   # the sender publishes C
        V.call_session(hb, snd)
        m0 = hb.moves
        if not H.on_curve(hb): v = 'curve'
        else:
            try:
                V.certificate(hb, 'base across', 'base up')
                hb.cr.phase_drop(); hb.cr.phase_drop()                       # own and theirs certified: red
                snd.clear('across'); snd.clear('up'); snd.put('across', list(Ar[0])); snd.put('up', list(Ar[1]))
                V.call_session(hb, snd)
                ok = V.receive_certificate(hb); hb.clear('bottom'); hb.clear('gap')
                v = 'accept' if ok else 'mismatch'
                if ok: assert R.pt((hb.value('base across'), hb.value('base up'))) == pi_minus_1(R, C)
            except V.EmptyCertificate:
                v = 'empty'
        return v, hb.peak, hb.moves - m0, hb.cr.tally_max
    def run(label, items):
        res = {'trials': 0, 'accept': 0, 'curve': 0, 'empty': 0, 'mismatch': 0, 'peak': 0, 'max_check_moves': 0}
        for C, A in items:
            v, pk, mv, tm = receiver(C, A); res['trials'] += 1; res[v] += 1
            res['peak'] = max(res['peak'], pk); res['max_check_moves'] = max(res['max_check_moves'], mv)
        out[label] = res
    run('honest', [(C, pi_minus_1(R, C)) for C in (honest() for _ in range(N))])
    outs = [plusT() if i % 2 else rand_out() for i in range(N)]
    run('C outside subgroup, correct certificate', [(C, pi_minus_1(R, C)) for C in outs])
    run('C outside subgroup, A = C', [(C, C) for C in outs])
    run('C = nonzero order-5 point', [(t, (0 * R.w, 0 * R.w)) for t in gf3] + [(t, honest()) for t in gf3])
    mm = []
    for i in range(N):
        C = honest(); Ac = pi_minus_1(R, C)
        mm.append((C, [honest(), R.neg(Ac), one_peg_off(T, Ac, rnd)][i % 3]))
    run('A not matching pi(C) - C', mm)
    oc = []
    for i in range(N):
        C = off_curve() if i % 2 else (lambda h: pari([h[0], h[1] + R.w]))(honest())
        oc.append((C, field_cert_formula(T, (C[0], C[1]), ir)))
    run('C off the curve', oc)
    return out

if __name__ == '__main__':
    level, tiers, N = sys.argv[1], sys.argv[2].split(','), int(sys.argv[3])
    res = {}
    for name in tiers:
        rnd = random.Random(31 + len(name) + N); t0 = time.time()
        res[name] = field_level(name, N, rnd) if level == 'field' else peg_level(name, N, rnd)
        res[name]['secs_total'] = round(time.time() - t0, 1)
        print(name, json.dumps(res[name], indent=1, default=str), flush=True)
    json.dump(res, open(os.path.join(HERE, f'soundness_v3_{level}_{"_".join(tiers)}.json'), 'w'), indent=1, default=str)
