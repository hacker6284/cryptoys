"""Soundness of the receiver checks, two levels:
 (1) FIELD LEVEL (PARI elements, thousands of trials): the card's trace check and the (tau-1) certificate,
     each written step by step as the card words them (ladder, tally counts, chord rule 'slope squared,
     plus one, plus the first x, minus the run', reject on an empty run), and the ladder-and-tally
     inversion.  Points are classified by PARI: in the subgroup iff l*R = O.
 (2) PEG LEVEL (homes.py fixed-home board, literal rules): fewer trials per class."""
import sys, os, random, time, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H
os.chdir(H.ECBS)
import ecbs_exchange as X
from cypari2 import Pari
os.chdir(HERE)
pari = X.pari if hasattr(X, 'pari') else Pari()

class Dummy: ctrl = 0
def ladder(m): return H.build_ladder(Dummy(), m)

def cubes(a, m):
    for _ in range(m): a = a ** 3
    return a

def invert_literal(x, rungs):
    e = x; m = 1
    for idx, r in enumerate(rungs):
        last = idx == len(rungs) - 1
        e = e * cubes(e, m)
        if not last: m *= 2
        if r == 'R':
            e = x * e ** 3
            if not last: m += 1
    inv = e ** 3; nrm = inv * x
    assert nrm == 1 or nrm == -1, "norm check"
    return inv if nrm == 1 else -inv

def chord(x1, y1, run, rise, irungs, one):
    if run == 0: raise H.Exceptional
    s = invert_literal(run, irungs) * rise
    x3 = s * s + one + x1 - run
    return x3, s * (x1 - x3) - y1

def trace_literal(R, B, trungs, irungs):
    x0, y0 = B; one = R.w ** 0; Sx, Sy = x0, y0; m = 1
    try:
        for idx, r in enumerate(trungs):
            last = idx == len(trungs) - 1
            tx = cubes(Sx, m)
            run = tx - Sx
            # (lazy y: the rise is made after the inversion; same value)
            Sx, Sy = chord(Sx, Sy, run, cubes(Sy, m) - Sy, irungs, one)
            if r == 'R' and last:
                return Sx ** 3 == x0 and Sy ** 3 == -y0
            if not last: m *= 2
            if r == 'R':
                tx, ty = Sx ** 3, Sy ** 3
                Sx, Sy = chord(tx, ty, x0 - tx, y0 - ty, irungs, one)
                if not last: m += 1
        raise RuntimeError
    except H.Exceptional:
        return False

def cert_make(R, C, irungs):
    """A = tau C + (-C): first point tau C, second point C with its up mirrored."""
    one = R.w ** 0; cx, cy = C; tx, ty = cx ** 3, cy ** 3
    return chord(tx, ty, cx - tx, -cy - ty, irungs, one)

def cert_check(R, C, A, irungs):
    if not R.on(pari([C[0], C[1]])): return False
    try: A2 = cert_make(R, C, irungs)
    except H.Exceptional: return False
    return A2[0] == A[0] and A2[1] == A[1]

def classes(T, rnd):
    R = T.R; E = R.E; l = T.l
    gf3 = [pari([0 * R.w, R.w ** 0]), pari([0 * R.w, -R.w ** 0]), pari([R.w ** 0, R.w ** 0]), pari([R.w ** 0, -R.w ** 0])]
    for t in gf3: assert R.on(t) and len(R.mul(5, t)) == 1
    def honest(): return R.mul(rnd.randrange(1, l), T.Pref)
    def plusT(): return R.add(honest(), gf3[rnd.randrange(4)])
    def rand_pt():
        while True:
            P = pari.random(E)
            if len(P) == 2: return P
    return gf3, honest, plusT, rand_pt

def field_level(name, N, rnd):
    T = X.Tier(name); R = T.R; l = T.l; n = T.n
    tr, ir = ladder(n), ladder(n - 1)
    gf3, honest, plusT, rand_pt = classes(T, rnd)
    out = {}
    # inversion
    bad = 0
    for _ in range(N):
        x = pari.random(R.w)
        if x == 0: continue
        bad += invert_literal(x, ir) * x != 1
    out['inversion_wrong'] = bad
    def run(label, gen, reps):
        acc = rej = 0; insub = 0
        for _ in range(reps):
            B = gen(); sub = len(R.mul(l, B)) == 1; insub += sub
            ok = trace_literal(R, (B[0], B[1]), tr, ir)
            acc += ok; rej += not ok
            assert ok == sub, (label, 'trace check disagrees with subgroup membership')
        out['trace ' + label] = dict(trials=reps, in_subgroup=insub, accepted=acc, rejected=rej)
    t0 = time.time()
    run('honest kP', honest, N); run('kP + GF(3) point', plusT, N)
    run('random curve point', rand_pt, N)
    run('pure order-5 point', lambda it=iter(gf3 * (N // 4 + 1)): next(it), 4)
    out['trace secs'] = round(time.time() - t0, 1)
    # certificate (option D)
    t0 = time.time()
    hon = cheat = 0; img_in_sub = 0; exc = 0; forged = 0
    for _ in range(N):
        C = honest(); A = cert_make(R, (C[0], C[1]), ir)
        hon += cert_check(R, (C[0], C[1]), A, ir)
        # adversary: arbitrary on-curve C (any class); the image must land in the subgroup
        Cq = rand_pt() if rnd.random() < .5 else plusT()
        try:
            Aq = cert_make(R, (Cq[0], Cq[1]), ir); img_in_sub += len(R.mul(l, pari([Aq[0], Aq[1]]))) == 1
        except H.Exceptional: exc += 1
        # adversary: a non-subgroup A with any certificate is rejected
        Abad = plusT() if rnd.random() < .5 else rand_pt()
        if len(R.mul(l, Abad)) == 1: continue
        Cany = rand_pt() if rnd.random() < .5 else honest()
        forged += cert_check(R, (Cany[0], Cany[1]), (Abad[0], Abad[1]), ir)
    cq_pure = sum(cert_check(R, (t[0], t[1]), (t[0], t[1]), ir) for t in gf3)
    out['certificate'] = dict(honest_accepted=hon, of=N, adversary_images_in_subgroup=img_in_sub, adversary_images_exceptional=exc,
                              nonsubgroup_A_accepted=forged, gf3_C_accepted=cq_pure, secs=round(time.time() - t0, 1))
    out['lemma'] = 'image of (tau-1) on E(GF(3^n)) lies in <P>: every adversary image in subgroup' if img_in_sub + exc == N else 'FAILED'
    return out

def peg_level(name, N, rnd):
    T = X.Tier(name); R = T.R; l = T.l
    gf3, honest, plusT, rand_pt = classes(T, rnd)
    out = {}
    def board_with(B):
        hb = H.HB(name, T.n, T.k); P = R.unpt(B); hb.put('base across', P[0]); hb.put('base up', P[1]); return hb
    for label, gen, reps in (('honest kP', honest, N), ('kP + GF(3) point', plusT, N), ('random curve point', rand_pt, N),
                             ('pure order-5 point', lambda it=iter(gf3): next(it), 4)):
        res = {'trials': reps, 'agree_with_subgroup': 0, 'accepted': 0}
        for replay in (False, True):
            key = 'replay' if replay else 'two tallies'
            res[key] = {'agree': 0, 'peak': 0, 'tally_holes_peak': 0, 'moves': 0, 'ctrl': 0}
        pts = [gen() for _ in range(reps)]
        for B in pts:
            sub = len(R.mul(l, B)) == 1
            for replay in (False, True):
                hb = board_with(B); m0, c0 = hb.moves, hb.ctrl
                ok = H.trace_check(hb, replay=replay)
                r = res['replay' if replay else 'two tallies']
                r['agree'] += ok == sub; r['peak'] = max(r['peak'], hb.peak)
                r['tally_holes_peak'] = max(r['tally_holes_peak'], hb.tally_holes_peak)
                if sub: r['moves'] = max(r['moves'], hb.moves - m0); r['ctrl'] = max(r['ctrl'], hb.ctrl - c0)
            res['accepted'] += ok
        out['trace ' + label] = res
    # certificate at peg level
    c = {'honest_ok': 0, 'forged_rejected': 0, 'forged': 0, 'peak': 0, 'moves_make': 0, 'moves_check': 0}
    for _ in range(N):
        C = honest(); Cr = R.unpt(C)
        hb = H.HB(name, T.n, T.k); hb.put('across', Cr[0]); hb.put('up', Cr[1]); m0 = hb.moves
        H.make_certificate(hb); c['moves_make'] = max(c['moves_make'], hb.moves - m0); c['peak'] = max(c['peak'], hb.peak)
        A = (hb.value('across'), hb.value('up'))
        assert R.pt(A) == R.add(R.frob(C), R.neg(C))
        hb2 = H.HB(name, T.n, T.k); hb2.put('base across', Cr[0]); hb2.put('base up', Cr[1]); m0 = hb2.moves
        c['honest_ok'] += H.check_certificate(hb2, A); c['moves_check'] = max(c['moves_check'], hb2.moves - m0); c['peak'] = max(c['peak'], hb2.peak)
        Abad = R.unpt(plusT()); c['forged'] += 1
        hb3 = H.HB(name, T.n, T.k); hb3.put('base across', Cr[0]); hb3.put('base up', Cr[1])
        c['forged_rejected'] += not H.check_certificate(hb3, Abad)
    out['certificate'] = c
    return out

if __name__ == '__main__':
    level, tiers, N = sys.argv[1], sys.argv[2].split(','), int(sys.argv[3])
    res = {}
    for name in tiers:
        rnd = random.Random(7 + len(name) + N)
        t0 = time.time()
        res[name] = field_level(name, N, rnd) if level == 'field' else peg_level(name, N, rnd)
        res[name]['secs_total'] = round(time.time() - t0, 1)
        print(name, json.dumps(res[name], indent=1), flush=True)
    json.dump(res, open(os.path.join(HERE, f'soundness_{level}_{"_".join(tiers)}.json'), 'w'), indent=1)
