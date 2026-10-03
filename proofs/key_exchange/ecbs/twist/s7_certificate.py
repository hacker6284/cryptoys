"""SPEC s7 (twist and invalid curves) for the CERTIFICATE check.  Evidence harness, not a reference.
The receiver (CARD.md check card, written out at field level with PARI elements):
  curve test  y^2 = x^3 - x^2 + 1;  rebuild A = pi(C) - C by the chord rule ('run' = x - x^3, reject if
  empty; slope = -(y^3 + y) / run; new x = slope^2 + 1 + x^3 - run; new y = slope (x^3 - new x) - y^3);
  compare with the sent A; walk the key over the REBUILT A (F-form at Toy / Hobby / Serious, chord at Demo).
None of these formulas uses the curve's constant term, so they run on any (x, y).
Parts
 A  Demo, exhaustive over all (x, y) in GF(3^7)^2 with x not in GF(3): which (x, y) lie on one of the nine
    GF(3)-defined curves y^2 = x^3 - x^2 + a4 x + a6 (a4, a6 in GF(3)); for those, translation by a4 maps
    them to E (b' = 1), E' (b' = 2) or the node (b' = 0), and the card's certificate equals the group law
    (pi - 1)C there (PARI for E, E'; the torus map for the node).  For all other (x, y) (including every
    quadratic-twist point), the rebuilt A lies on a curve with a4 not in GF(3)... (checked for all).
 B  Every tier: E' and the node.  Points over GF(3), the image of pi - 1, its factorisation; the leak
    mechanism: for C of prime order r on E' (resp. the node), the receiver's walk over the rebuilt A gives
    [kappa(mu) mod r] A with mu the eigenvalue of pi on <A> (mu = -3 on the node), kappa(z) = sum c_j
    z^(M-1-j) the key's digits.  Checked against PARI (E') and the torus map (node).
 C  End to end, WITHOUT the curve test (the curve test rejects every C used here; checked): one node point
    and an attacker who learns the receiver's shared point recovers the receiver's whole key at Demo, Toy
    and Hobby (finite-field logs in GF(3^(2n)) by PARI fflog).
Usage: python s7_certificate.py [A,B,C]   (writes s7_certificate.json; stdout = s7_certificate.txt)"""
import sys, os, json, random, time, math
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'core')); sys.path.insert(0, os.path.join(HERE, '..', 'demo'))
import numpy as np
from ecbs_ref import Ref, TIERS, pari, V as trace
os.chdir(os.path.join(HERE, '..', 'core'))
import ecbs_exchange as X, ecbs_keys as K
os.chdir(HERE)
CELLS = {'Demo': 2, 'Toy': 16, 'Hobby': 51, 'Serious': 162}
OUT = {}
def lg(x): return math.log2(x)

class Empty(Exception): pass

# ------------------------------------------------------------------ the receiver at field level
def curve_test(R, x, y): return y * y == x ** 3 - x * x + R.w ** 0
def certificate(R, x, y):
    one = R.w ** 0; x3, y3 = x ** 3, y ** 3; run = x - x3
    if run == 0: raise Empty
    s = (-(y3 + y)) / run; nx = s * s + one + x3 - run
    return nx, s * (x3 - nx) - y3
def chord(R, x1, y1, x2, y2):                      # first point + second point, the card's chord rule
    one = R.w ** 0; run = x2 - x1
    if run == 0: raise Empty
    s = (y2 - y1) / run; nx = s * s + one + x1 - run
    return nx, s * (x1 - nx) - y1
def walk(R, name, cells, bx, by):
    """F-form walk (spec R7) at Toy / Hobby / Serious, the chord walk at Demo; returns affine (x, y)."""
    if name == 'Demo':
        acc = None
        for c in cells:
            if acc is not None: acc = (acc[0] ** 3, acc[1] ** 3)
            if c == '.': continue
            y2 = by if c == 'W' else -by
            acc = (bx, y2) if acc is None else chord(R, acc[0], acc[1], bx, y2)
        return acc
    Xp = Yp = Zp = None; one = R.w ** 0
    for c in cells:
        if Xp is not None: Xp, Yp, Zp = Xp ** 3, Yp ** 3, Zp ** 3
        if c == '.': continue
        y2 = by if c == 'W' else -by
        if Xp is None: Xp, Yp, Zp = bx, y2, one; continue
        v = bx * Zp - Xp
        if v == 0: raise Empty
        u = y2 * Zp - Yp; v2 = v * v; v2Z = v2 * Zp
        Fg = u * u * Zp + v2 * v + v2Z; Zn = v * v2Z
        Xp, Yp, Zp = v * Fg + bx * Zn, -(u * Fg + y2 * Zn), Zn
    return Xp / Zp, Yp / Zp

def kappa(cells, z, mod):
    M = len(cells); return sum((1 if c == 'W' else -1) * pow(z, M - 1 - j, mod) for j, c in enumerate(cells) if c != '.') % mod

def rand_key(rnd, M):
    while True:
        k = [rnd.choice('.WR') for _ in range(M)]
        if any(c != '.' for c in k): return k

# ------------------------------------------------------------------ the node: torus map into GF(3^(2n))
class Node:
    def __init__(self, R, n):
        self.R = R; self.w2 = pari(f"ffgen(3^{2 * n}, 'v)"); self.emb = pari.ffembed(R.w, self.w2)
        self.i = pari.sqrt(-1 + 0 * self.w2); assert self.i ** 2 == -1 + 0 * self.w2
        assert pari.ffmap(self.emb, R.w) ** 0 == self.w2 ** 0
    def up(self, a): return pari.ffmap(self.emb, a)
    def psi(self, x, y):
        X, Y = self.up(x), self.up(y); return (Y + self.i * X) / (Y - self.i * X)
    def on(self, x, y): return y * y == x ** 3 - x * x and not (x == 0 and y == 0)
    def rand_point(self, rnd):
        R = self.R
        while True:
            x = pari.random(R.w)
            if x == 0: continue
            f = x ** 3 - x * x
            if f == 0 or pari.issquare(f):
                y = pari.sqrt(f) if f != 0 else 0 * R.w
                if rnd.random() < .5: y = -y
                if self.on(x, y): return x, y
    def from_torus(self, z):
        """the inverse map: (y + i x) / (y - i x) = z  <=>  y (z - 1) = i x (z + 1); with y^2 = x^2 (x - 1)
        this gives x = 1 + t^2, y = x t with t = y / x = i (z + 1)/(z - 1)."""
        t = self.i * (z + 1) / (z - 1); x = 1 + t * t; y = x * t
        xr = pari.ffmap(pari.ffinvmap(self.emb), x); yr = pari.ffmap(pari.ffinvmap(self.emb), y)
        assert self.on(xr, yr) and self.psi(xr, yr) == z
        return xr, yr

# ================================================================== part A: Demo, exhaustive
def part_A():
    import gf37 as F
    Q = F.Q; R = F.R
    xs, ys = np.meshgrid(np.arange(Q), np.arange(Q), indexing='ij'); xs = xs.ravel(); ys = ys.ravel()
    keep = F.cube(xs) != xs; xs = xs[keep]; ys = ys[keep]
    b = F.add(F.sub(F.mul(ys, ys), F.cube(xs)), F.mul(xs, xs))            # b' = y^2 - x^3 + x^2
    nx, ny = (lambda x, y: (lambda x3, y3, run: (lambda s: (lambda nxx: (nxx, F.sub(F.mul(s, F.sub(x3, nxx)), y3)))(
        F.sub(F.add(F.add(F.mul(s, s), F.ONE), x3), run)))(F.mul(F.inv(run), F.neg(F.add(y3, y)))))(F.cube(x), F.cube(y), F.sub(x, F.cube(x))))(xs, ys)
    res = {'pairs_x_not_in_GF3': int(len(xs))}
    cls = np.full(len(xs), -1)
    for a4 in range(3):
        for a6 in range(3):
            m = b == F.add(F.mul(np.full(len(xs), a4), xs), a6)
            cls[m] = 3 * a4 + a6
    assert not np.any(np.bincount(cls[cls >= 0], minlength=9) == -1)
    gf3curves = {}
    rnd = random.Random(3)
    for a4 in range(3):
        for a6 in range(3):
            idx = np.nonzero(cls == 3 * a4 + a6)[0]
            a6t = (a4 * a4 - a4 + a6) % 3                                    # E_{a4,a6} -> E_{0,a6t} by X = x + a4
            name = {1: 'E', 2: "E'", 0: 'node'}[a6t]
            # the certificate = (pi - 1)C on that curve: PARI for E / E' (translated back), torus map for the node
            chk = 0; S = idx if len(idx) <= 400 else np.array(rnd.sample(list(idx), 400))
            for i in S:
                x, y = F.to_el(int(xs[i])), F.to_el(int(ys[i])); Ax, Ay = F.to_el(int(nx[i])), F.to_el(int(ny[i]))
                tx, tAx = x + a4, Ax + a4
                if name == 'node':
                    Nd = gf37_node
                    chk += Nd.on(tAx, Ay) and Nd.psi(tAx, Ay) == Nd.psi(tx, y) ** (-4)
                else:
                    Ec = pari.ellinit([0, 2, 0, 0, a6t], R.w); Cp = pari([tx, y])
                    Ap = pari.elladd(Ec, pari([tx ** 3, y ** 3]), pari.ellneg(Ec, Cp))
                    chk += len(Ap) == 2 and Ap[0] == tAx and Ap[1] == Ay
            gf3curves[f"a4={a4},a6={a6}"] = dict(points=int(len(idx)), isomorphic_to=name,
                                                 certificate_is_pi_minus_1_there=f"{chk}/{len(S)}",
                                                 passes_curve_test=bool(a4 == 0 and a6 == 1))
    res['GF3_defined_curves'] = gf3curves
    # class (ii): every other (x, y)
    o = np.nonzero(cls < 0)[0]
    x, y, Ax, Ay, bb = xs[o], ys[o], nx[o], ny[o], b[o]
    x3 = F.cube(x); bb3 = F.cube(bb)
    a4p = F.mul(F.sub(bb3, bb), F.inv(F.sub(x3, x)))                       # the cubic through pi(C) and -C
    a6p = F.sub(bb, F.mul(a4p, x))
    lhs = F.mul(Ay, Ay); rhs = F.add(F.add(F.sub(F.cube(Ax), F.mul(Ax, Ax)), F.mul(a4p, Ax)), a6p)
    rhs_E = F.add(F.sub(F.cube(Ax), F.mul(Ax, Ax)), F.ONE)
    in3 = lambda a: F.cube(a) == a
    res['other_pairs'] = dict(
        count=int(len(o)),
        rebuilt_A_on_y2_eq_x3_minus_x2_plus_a4x_plus_a6_with_a4_a6_from_pi_C_and_minus_C=int((lhs == rhs).sum()),
        a4_nonzero=int((a4p != 0).sum()),
        curve_of_A_defined_over_GF3=int((in3(a4p) & in3(a6p)).sum()),
        Frobenius_moves_that_curve=int((~(in3(a4p) & in3(a6p))).sum()),
        rebuilt_A_happens_to_lie_on_E=int((lhs == rhs_E).sum()))
    # quadratic twist points (model y^2 = x^3 + x^2 + 2, PARI-counted) and the scaled model -y^2 = f(x)
    tw = F.mul(ys, ys) == F.add(F.add(F.cube(xs), F.mul(xs, xs)), 2)
    tw2 = F.neg(F.mul(ys, ys)) == F.add(F.sub(F.cube(xs), F.mul(xs, xs)), F.ONE)
    res['quadratic_twist_points_x_not_in_GF3'] = dict(
        model_y2_eq_x3_plus_x2_plus_2=int(tw.sum()), of_which_on_a_GF3_defined_curve=int((tw & (cls >= 0)).sum()),
        model_minus_y2_eq_f=int(tw2.sum()), of_which_on_a_GF3_defined_curve_=int((tw2 & (cls >= 0)).sum()),
        twist_order_PARI=int(pari.ellcard(pari.ellinit([0, 1, 0, 0, 2], R.w))))
    return res

# ================================================================== part B: E' and the node, every tier
TW_CLAIMED = {179: dict(Eprime=[2, 16859153558033], node=[2, 2, 3755779, 47029186391731, 9248363581047133])}
def factor_full(n_, kind, N):
    if n_ in TW_CLAIMED:                                          # Serious: the review's factors, re-verified
        ps = list(TW_CLAIMED[n_][kind]); rest = N
        for p in ps: assert rest % p == 0; rest //= p
        ps.append(rest)
    else:
        f = pari.factor(N); ps = [int(p) for p, e in zip(f[0], f[1]) for _ in range(int(e))]
    assert math.prod(ps) == N and all(bool(pari.isprime(p)) for p in ps)
    return sorted(ps)

def part_B(names, rnd):
    res = {}
    for name in names:
        n, k, _ = TIERS[name]; R = Ref(n, k); q = 3 ** n; M = CELLS[name]; one = R.w ** 0
        r_ = {}
        # points over GF(3) (x, y in GF(3)): E' and the node
        F3 = [(a, c) for a in range(3) for c in range(3)]
        r_["E'(GF(3)) affine"] = [p for p in F3 if (p[1] ** 2 - (p[0] ** 3 - p[0] ** 2 + 2)) % 3 == 0]
        r_['node ns(GF(3)) affine'] = [p for p in F3 if (p[1] ** 2 - (p[0] ** 3 - p[0] ** 2)) % 3 == 0 and p != (0, 0)]
        NEp = q + 1 - trace(n, 2); Nnode = q + 1
        Ep = pari.ellinit([0, 2, 0, 0, 2], R.w)
        if n <= 23: assert int(pari.ellcard(Ep)) == NEp
        imgE, imgN = NEp // 2, Nnode // 4
        fE = factor_full(n, 'Eprime', NEp); fN = factor_full(n, 'node', Nnode)
        def leak(ps, img, bound):
            odd = [p for p in ps if p != 2]; small = [p for p in odd if p < bound]
            return round(lg(math.prod(small)), 1) if small else 0.0
        r_["E'"] = dict(order_bits=round(lg(NEp), 2), image_of_pi_minus_1=f"index 2, order 2^{lg(imgE):.2f}",
                        factors=[p if p < 10 ** 12 else f"p{p.bit_length()}" for p in fE],
                        image_is_odd_part=bool(imgE % 2 == 1),
                        leak_bits_primes_below_2_40=leak(fE, imgE, 2 ** 40), leak_bits_primes_below_2_60=leak(fE, imgE, 2 ** 60))
        r_['node'] = dict(order_bits=round(lg(Nnode), 2), image_of_pi_minus_1=f"index 4, order 2^{lg(imgN):.2f}",
                          image_is_odd_part=bool(imgN % 2 == 1),
                          factors=[p if p < 10 ** 12 else f"p{p.bit_length()}" for p in fN],
                          leak_bits_primes_below_2_40=leak(fN, imgN, 2 ** 40), leak_bits_primes_below_2_60=leak(fN, imgN, 2 ** 60),
                          image_bits=round(lg(imgN), 2), key_bits=round(lg(3 ** M - 1), 2))
        # mechanism on E': C of prime order r (largest odd prime below 2^24, else the smallest odd prime > 2^10)
        oddE = sorted({p for p in fE if p != 2})
        cand = [p for p in oddE if 2 ** 10 < p < 2 ** 24] or [p for p in oddE if p > 2 ** 6]
        r = max(cand) if cand else None
        mech = {'r': r, 'trials': 0, 'certificate_is_PARI_pi_minus_1': 0, 'walk_is_kappa_mu_times_A': 0,
                'pi_acts_on_A_as_a_root_mu_of_z2_minus_2z_plus_3': 0, 'curve_test_rejects_C': 0, 'exceptional_reroll': 0}
        if r:
            for t in range(4):
                while True:
                    P0 = pari.random(Ep); C = pari.ellmul(Ep, P0, NEp // r)
                    if len(C) == 2: break
                Ax, Ay = certificate(R, C[0], C[1])
                Ap = pari.elladd(Ep, pari([C[0] ** 3, C[1] ** 3]), pari.ellneg(Ep, C))
                mech['certificate_is_PARI_pi_minus_1'] += Ap[0] == Ax and Ap[1] == Ay
                # pi acts on <A> (prime order r) as a root mu of z^2 - 2z + 3 mod r; find it without a log
                roots = [int(z) for z in pari.polrootsmod(pari('x^2 - 2*x + 3'), r)]
                piA = pari([Ax ** 3, Ay ** 3]); mus = [z for z in roots if pari.ellmul(Ep, Ap, z) == piA]
                mech['pi_acts_on_A_as_a_root_mu_of_z2_minus_2z_plus_3'] += len(mus) == 1
                mu = mus[0]
                key = rand_key(rnd, M)
                try: W = walk(R, name, key, Ax, Ay)
                except Empty: mech['exceptional_reroll'] += 1; continue
                Wp = pari.ellmul(Ep, Ap, kappa(key, mu, r))
                mech['walk_is_kappa_mu_times_A'] += len(Wp) == 2 and Wp[0] == W[0] and Wp[1] == W[1]
                mech['curve_test_rejects_C'] += not curve_test(R, C[0], C[1]); mech['trials'] += 1
        r_["E' mechanism"] = mech
        # mechanism on the node: torus map, mu = -3
        Nd = Node(R, n); nm = {'trials': 0, 'chord_is_torus_product': 0, 'pi_is_torus_power_minus_3': 0,
                               'certificate_is_psi_C_to_minus_4': 0, 'walk_is_psi_A_to_kappa_minus_3': 0,
                               'curve_test_rejects_C': 0, 'exceptional_reroll': 0}
        for t in range(6):
            P1 = Nd.rand_point(rnd); P2 = Nd.rand_point(rnd)
            try:
                S = chord(R, P1[0], P1[1], P2[0], P2[1])
                nm['chord_is_torus_product'] += Nd.psi(*S) == Nd.psi(*P1) * Nd.psi(*P2)
            except Empty: pass
            nm['pi_is_torus_power_minus_3'] += Nd.psi(P1[0] ** 3, P1[1] ** 3) == Nd.psi(*P1) ** (-3)
            C = Nd.rand_point(rnd)
            try: Ax, Ay = certificate(R, *C)
            except Empty: continue
            nm['certificate_is_psi_C_to_minus_4'] += Nd.psi(Ax, Ay) == Nd.psi(*C) ** (-4)
            key = rand_key(rnd, M)
            try: W = walk(R, name, key, Ax, Ay)
            except Empty: nm['exceptional_reroll'] += 1; continue
            kap = sum((1 if c == 'W' else -1) * (-3) ** (M - 1 - j) for j, c in enumerate(key) if c != '.')
            nm['walk_is_psi_A_to_kappa_minus_3'] += Nd.psi(*W) == Nd.psi(Ax, Ay) ** kap
            nm['curve_test_rejects_C'] += not curve_test(R, *C); nm['trials'] += 1
        r_['node mechanism'] = nm
        res[name] = r_
        print(name, json.dumps(r_, default=str), flush=True)
    return res

# ================================================================== part C: whole key from one node point
def part_C(names, rnd, budget_s=600):
    res = {}
    for name in names:
        n, k, _ = TIERS[name]; R = Ref(n, k); q = 3 ** n; M = CELLS[name]; Nd = Node(R, n)
        t0 = time.time(); out = {}
        # the attacker: a node point C whose rebuilt A has the full image order (q + 1)/4
        img = (q + 1) // 4
        while True:
            C = Nd.rand_point(rnd)
            try: Ax, Ay = certificate(R, *C)
            except Empty: continue
            z = Nd.psi(Ax, Ay)
            if pari.fforder(z) == img: break
        out['curve_test_rejects_C'] = not curve_test(R, *C)
        out['rebuilt_A_order'] = f"(q+1)/4 = 2^{lg(img):.2f}"; out['key_cells'] = M; out['key_space_bits'] = round(lg(3 ** M), 2)
        key = rand_key(rnd, M)
        try: W = walk(R, name, key, Ax, Ay)                          # the receiver, no curve test
        except Empty: out['exceptional'] = True; res[name] = out; continue
        zW = Nd.psi(*W)
        try:
            e = int(pari.fflog(zW, z, img))                         # the attacker's finite-field log
        except Exception as ex:
            out['fflog'] = f"failed: {type(ex).__name__}"; res[name] = out; continue
        out['fflog_secs'] = round(time.time() - t0, 1)
        # decode: e = sum c_j (-3)^(M-1-j) mod img, balanced digits; img > 3^M so the representative is unique
        assert img > 3 ** M
        v = e if e <= img // 2 else e - img
        digits = []
        for _ in range(M):
            d = ((v % 3) + 1) % 3 - 1                                # balanced digit in {-1, 0, 1}
            digits.append(d); v = (v - d) // -3
        assert v == 0
        rec = ''.join({0: '.', 1: 'W', -1: 'R'}[d] for d in reversed(digits))
        out['recovered_key_equals_receivers_key'] = rec == ''.join(key)
        res[name] = out
        print(name, json.dumps(out), flush=True)
    return res

if __name__ == '__main__':
    parts = sys.argv[1].split(',') if len(sys.argv) > 1 else ['A', 'B', 'C']
    rnd = random.Random(20261003); t0 = time.time()
    path = os.path.join(HERE, 's7_certificate.json')
    OUT = json.load(open(path)) if os.path.exists(path) else {}
    if 'A' in parts:
        import gf37
        gf37_node = Node(gf37.R, 7)
        OUT['A_demo_exhaustive'] = part_A(); print('A', json.dumps(OUT['A_demo_exhaustive'], indent=1), flush=True)
    if 'B' in parts:
        OUT['B_invalid_GF3_curves'] = part_B(['Demo', 'Toy', 'Hobby', 'Serious'], rnd)
    if 'C' in parts:
        tiers = sys.argv[2].split(',') if len(sys.argv) > 2 else ['Demo', 'Toy', 'Hobby']
        OUT.setdefault('C_whole_key_from_one_node_point', {}).update(part_C(tiers, rnd))
    json.dump(OUT, open(path, 'w'), indent=1, default=str)
    print('secs', round(time.time() - t0, 1))
