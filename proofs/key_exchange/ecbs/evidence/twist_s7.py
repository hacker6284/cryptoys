"""SPEC s7 (twist and invalid curves) for the certificate check, on the code sudoc generates
from ecbs.sudo, checked against PARI/GP.
The receiver's steps are the generated ones: curve_test(); make_certificate() (rebuild
A = pi(C) - C by the chord rule; none if the run is empty); walk_key() (the key walk over the
REBUILT A and finish: F-form at Toy / Hobby / Serious, chord at Demo). None of them uses the
curve's constant term, so they run on any (x, y). PARI (../oracle/ecbs_oracle.py) supplies
the curves E, E' and the node and checks every result.
Parts
 A  Demo, exhaustive over all (x, y) in GF(3^7)^2 with x not in GF(3) (the generated
    make_certificate on every pair, from demo_exhaustive.mjs): which (x, y) lie on one of the
    nine GF(3)-defined curves y^2 = x^3 - x^2 + a4 x + a6; for those, translation by a4 maps
    them to E, E' or the node, and the certificate equals (pi - 1)C there (PARI for E, E'; the
    torus map for the node; 400 sampled per curve). For every other (x, y) (including every
    quadratic-twist point), the rebuilt A lies on a curve with a4 not in GF(3).
 B  Every tier: E' and the node. Points over GF(3), the image of pi - 1, its factorisation; the
    leak mechanism: for C of prime order r on E' (resp. the node), the generated walk over the
    rebuilt A gives [kappa(mu) mod r] A with mu the eigenvalue of pi on <A> (mu = -3 on the node),
    kappa(z) = sum c_j z^(M-1-j).
 C  End to end, WITHOUT the curve test (the curve test rejects every C used here; checked): one
    node point and an attacker who learns the receiver's shared point recovers the receiver's
    whole key (finite-field logs in GF(3^(2n)) by PARI fflog). Demo and Toy; Hobby did not
    finish within 1,500 s in Phase 1 (../history/twist/s7_partC.txt) and is not rerun.
Phase-1 results: ../history/twist/s7_certificate.json (the script, with the receiver written at field
level, was removed when ecbs.sudo replaced it).
Usage: python twist_s7.py A   > results/twist_s7_A.txt
       python twist_s7.py B,C > results/twist_s7_BC.txt    (B and C share one random stream)
  Both update results/twist_s7.json, with a provenance per part (the parts that ran). Part A
  reads ECBS_DEMO_EXHAUSTIVE=<prefix> (a finished demo_exhaustive.mjs run), else runs it.
  Timings go to stderr only.
"""
import json, math, os, random, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))   # proofs/: sudo_js
sys.dont_write_bytecode = True
from ecbs_oracle import Ref, TIERS, CELLS, pari, V as trace
import sudo_js as SJ
ECBS = "primitives/key_exchange/ecbs/ecbs.sudo"

S = None  # the generated code
lg = math.log2


def tr(R, a): return [".WR".index(c) for c in R.reg(a)]
def el(R, t): return R.el("".join(".WR"[d] for d in t))


def certificate(name, R, x, y):
    a = S.call("make_certificate", SJ.tier(name), {"x": tr(R, x), "y": tr(R, y)})
    return None if a is None else (el(R, a["x"]), el(R, a["y"]))


def walk(name, R, key, bx, by):
    w = S.call("walk_key", SJ.tier(name), key, {"x": tr(R, bx), "y": tr(R, by)})
    return None if w is None else (el(R, w["x"]), el(R, w["y"]))


def curve_test(name, R, x, y):
    return S.call("curve_test", SJ.tier(name), {"x": tr(R, x), "y": tr(R, y)})


def kappa(cells, z, mod):
    M = len(cells); return sum((1 if c == 1 else -1) * pow(z, M - 1 - j, mod) for j, c in enumerate(cells) if c) % mod


def rand_key(rnd, M):
    while True:
        k = [rnd.randrange(3) for _ in range(M)]
        if any(k): return k


class Node:
    """the node y^2 = x^3 - x^2: psi(x, y) = (y + i x)/(y - i x) into the norm-1 torus of GF(3^(2n))."""
    def __init__(self, R, n):
        self.R = R; self.w2 = pari(f"ffgen(3^{2 * n}, 'v)"); self.emb = pari.ffembed(R.w, self.w2)
        self.i = pari.sqrt(-1 + 0 * self.w2); assert self.i ** 2 == -1 + 0 * self.w2
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


def part_A():
    import gf37 as F
    from soundness_demo import exhaustive
    curve, cx, cy = exhaustive(4)
    Q = F.Q; R = F.R; nd = Node(R, 7)
    xs, ys = np.meshgrid(np.arange(Q), np.arange(Q), indexing="ij"); xs = xs.ravel(); ys = ys.ravel()
    keep = F.cube(xs) != xs
    assert ((cx >= 0) == keep).all(), "certificate exists exactly when x is not in GF(3)"
    xs, ys, nx, ny = xs[keep], ys[keep], cx[keep], cy[keep]
    b = F.add(F.sub(F.mul(ys, ys), F.cube(xs)), F.mul(xs, xs))            # b' = y^2 - x^3 + x^2
    res = {"pairs_x_not_in_GF3": int(len(xs))}
    cls = np.full(len(xs), -1)
    for a4 in range(3):
        for a6 in range(3):
            cls[b == F.add(F.mul(np.full(len(xs), a4), xs), a6)] = 3 * a4 + a6
    rnd = random.Random(3); gf3curves = {}
    for a4 in range(3):
        for a6 in range(3):
            idx = np.nonzero(cls == 3 * a4 + a6)[0]
            a6t = (a4 * a4 - a4 + a6) % 3
            name = {1: "E", 2: "E'", 0: "node"}[a6t]
            chk = 0; Sx = idx if len(idx) <= 400 else np.array(rnd.sample(list(idx), 400))
            for i in Sx:
                x, y = F.to_el(int(xs[i])), F.to_el(int(ys[i])); Ax, Ay = F.to_el(int(nx[i])), F.to_el(int(ny[i]))
                tx, tAx = x + a4, Ax + a4
                if name == "node":
                    chk += nd.on(tAx, Ay) and nd.psi(tAx, Ay) == nd.psi(tx, y) ** (-4)
                else:
                    Ec = pari.ellinit([0, 2, 0, 0, a6t], R.w); Cp = pari([tx, y])
                    Ap = pari.elladd(Ec, pari([tx ** 3, y ** 3]), pari.ellneg(Ec, Cp))
                    chk += len(Ap) == 2 and Ap[0] == tAx and Ap[1] == Ay
            gf3curves[f"a4={a4},a6={a6}"] = dict(points=int(len(idx)), isomorphic_to=name,
                                                 certificate_is_pi_minus_1_there=f"{chk}/{len(Sx)}",
                                                 passes_curve_test=bool(a4 == 0 and a6 == 1),
                                                 generated_curve_test_passes=int(curve[keep][idx].sum()))
    res["GF3_defined_curves"] = gf3curves
    o = np.nonzero(cls < 0)[0]
    x, y, Ax, Ay, bb = xs[o], ys[o], nx[o], ny[o], b[o]
    x3 = F.cube(x); bb3 = F.cube(bb)
    a4p = F.mul(F.sub(bb3, bb), F.inv(F.sub(x3, x)))
    a6p = F.sub(bb, F.mul(a4p, x))
    lhs = F.mul(Ay, Ay); rhs = F.add(F.add(F.sub(F.cube(Ax), F.mul(Ax, Ax)), F.mul(a4p, Ax)), a6p)
    rhs_E = F.add(F.sub(F.cube(Ax), F.mul(Ax, Ax)), F.ONE)
    in3 = lambda a: F.cube(a) == a
    res["other_pairs"] = dict(
        count=int(len(o)),
        rebuilt_A_on_y2_eq_x3_minus_x2_plus_a4x_plus_a6_with_a4_a6_from_pi_C_and_minus_C=int((lhs == rhs).sum()),
        a4_nonzero=int((a4p != 0).sum()),
        curve_of_A_defined_over_GF3=int((in3(a4p) & in3(a6p)).sum()),
        Frobenius_moves_that_curve=int((~(in3(a4p) & in3(a6p))).sum()),
        rebuilt_A_happens_to_lie_on_E=int((lhs == rhs_E).sum()),
        generated_curve_test_passes=int(curve[keep][o].sum()))
    tw = F.mul(ys, ys) == F.add(F.add(F.cube(xs), F.mul(xs, xs)), 2)
    tw2 = F.neg(F.mul(ys, ys)) == F.add(F.sub(F.cube(xs), F.mul(xs, xs)), F.ONE)
    res["quadratic_twist_points_x_not_in_GF3"] = dict(
        model_y2_eq_x3_plus_x2_plus_2=int(tw.sum()), of_which_on_a_GF3_defined_curve=int((tw & (cls >= 0)).sum()),
        model_minus_y2_eq_f=int(tw2.sum()), of_which_on_a_GF3_defined_curve_=int((tw2 & (cls >= 0)).sum()),
        twist_order_PARI=int(pari.ellcard(pari.ellinit([0, 1, 0, 0, 2], R.w))),
        generated_curve_test_rejects_all=bool(not (curve[keep] & tw).any()))
    return res


TW_CLAIMED = {179: dict(Eprime=[2, 16859153558033], node=[2, 2, 3755779, 47029186391731, 9248363581047133])}
def factor_full(n_, kind, N):
    if n_ in TW_CLAIMED:
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
        n, k = TIERS[name]; R = Ref(n, k); q = 3 ** n; M = CELLS[name]
        r_ = {}
        F3 = [(a, c) for a in range(3) for c in range(3)]
        r_["E'(GF(3)) affine"] = [p for p in F3 if (p[1] ** 2 - (p[0] ** 3 - p[0] ** 2 + 2)) % 3 == 0]
        r_["node ns(GF(3)) affine"] = [p for p in F3 if (p[1] ** 2 - (p[0] ** 3 - p[0] ** 2)) % 3 == 0 and p != (0, 0)]
        NEp = q + 1 - trace(n, 2); Nnode = q + 1
        Ep = pari.ellinit([0, 2, 0, 0, 2], R.w)
        if n <= 23: assert int(pari.ellcard(Ep)) == NEp
        imgE, imgN = NEp // 2, Nnode // 4
        fE = factor_full(n, "Eprime", NEp); fN = factor_full(n, "node", Nnode)
        def leak(ps, bound):
            small = [p for p in ps if p != 2 and p < bound]
            return round(lg(math.prod(small)), 1) if small else 0.0
        r_["E'"] = dict(order_bits=round(lg(NEp), 2), image_of_pi_minus_1=f"index 2, order 2^{lg(imgE):.2f}",
                        factors=[p if p < 10 ** 12 else f"p{p.bit_length()}" for p in fE],
                        image_is_odd_part=bool(imgE % 2 == 1),
                        leak_bits_primes_below_2_40=leak(fE, 2 ** 40), leak_bits_primes_below_2_60=leak(fE, 2 ** 60))
        r_["node"] = dict(order_bits=round(lg(Nnode), 2), image_of_pi_minus_1=f"index 4, order 2^{lg(imgN):.2f}",
                          image_is_odd_part=bool(imgN % 2 == 1),
                          factors=[p if p < 10 ** 12 else f"p{p.bit_length()}" for p in fN],
                          leak_bits_primes_below_2_40=leak(fN, 2 ** 40), leak_bits_primes_below_2_60=leak(fN, 2 ** 60),
                          image_bits=round(lg(imgN), 2), key_bits=round(lg(3 ** M - 1), 2))
        oddE = sorted({p for p in fE if p != 2})
        cand = [p for p in oddE if 2 ** 10 < p < 2 ** 24] or [p for p in oddE if p > 2 ** 6]
        r = max(cand) if cand else None
        mech = {"r": r, "trials": 0, "certificate_is_PARI_pi_minus_1": 0, "walk_is_kappa_mu_times_A": 0,
                "pi_acts_on_A_as_a_root_mu_of_z2_minus_2z_plus_3": 0, "curve_test_rejects_C": 0, "exceptional_reroll": 0}
        if r:
            for _ in range(4):
                while True:
                    P0 = pari.random(Ep); C = pari.ellmul(Ep, P0, NEp // r)
                    if len(C) == 2: break
                A = certificate(name, R, C[0], C[1]); Ax, Ay = A
                Ap = pari.elladd(Ep, pari([C[0] ** 3, C[1] ** 3]), pari.ellneg(Ep, C))
                mech["certificate_is_PARI_pi_minus_1"] += Ap[0] == Ax and Ap[1] == Ay
                roots = [int(z) for z in pari.polrootsmod(pari("x^2 - 2*x + 3"), r)]
                piA = pari([Ax ** 3, Ay ** 3]); mus = [z for z in roots if pari.ellmul(Ep, Ap, z) == piA]
                mech["pi_acts_on_A_as_a_root_mu_of_z2_minus_2z_plus_3"] += len(mus) == 1
                mu = mus[0]; key = rand_key(rnd, M)
                W = walk(name, R, key, Ax, Ay)
                if W is None: mech["exceptional_reroll"] += 1; continue
                Wp = pari.ellmul(Ep, Ap, kappa(key, mu, r))
                mech["walk_is_kappa_mu_times_A"] += len(Wp) == 2 and Wp[0] == W[0] and Wp[1] == W[1]
                mech["curve_test_rejects_C"] += not curve_test(name, R, C[0], C[1]); mech["trials"] += 1
        r_["E' mechanism"] = mech
        Nd = Node(R, n); nm = {"trials": 0, "two_cell_walk_WW_is_torus_power_minus_2": 0, "pi_is_torus_power_minus_3": 0,
                               "certificate_is_psi_C_to_minus_4": 0, "walk_is_psi_A_to_kappa_minus_3": 0,
                               "curve_test_rejects_C": 0, "exceptional_reroll": 0}
        for _ in range(6):
            P1 = Nd.rand_point(rnd)
            W2 = walk(name, R, [1, 1], *P1)                       # pi(B) + B by the generated chord / F-form add
            if W2 is not None:
                nm["two_cell_walk_WW_is_torus_power_minus_2"] += Nd.psi(*W2) == Nd.psi(*P1) ** (-2)
            nm["pi_is_torus_power_minus_3"] += Nd.psi(P1[0] ** 3, P1[1] ** 3) == Nd.psi(*P1) ** (-3)
            C = Nd.rand_point(rnd)
            A = certificate(name, R, *C)
            if A is None: continue
            Ax, Ay = A
            nm["certificate_is_psi_C_to_minus_4"] += Nd.psi(Ax, Ay) == Nd.psi(*C) ** (-4)
            key = rand_key(rnd, M)
            W = walk(name, R, key, Ax, Ay)
            if W is None: nm["exceptional_reroll"] += 1; continue
            kap = sum((1 if c == 1 else -1) * (-3) ** (M - 1 - j) for j, c in enumerate(key) if c)
            nm["walk_is_psi_A_to_kappa_minus_3"] += Nd.psi(*W) == Nd.psi(Ax, Ay) ** kap
            nm["curve_test_rejects_C"] += not curve_test(name, R, *C); nm["trials"] += 1
        r_["node mechanism"] = nm
        res[name] = r_
        print(name, json.dumps(r_, default=str), flush=True)
    return res


def part_C(names, rnd):
    res = {}
    for name in names:
        n, k = TIERS[name]; R = Ref(n, k); q = 3 ** n; M = CELLS[name]; Nd = Node(R, n)
        t0 = time.time(); out = {}
        img = (q + 1) // 4
        while True:
            C = Nd.rand_point(rnd)
            A = certificate(name, R, *C)
            if A is None: continue
            z = Nd.psi(*A)
            if pari.fforder(z) == img: break
        out["curve_test_rejects_C"] = not curve_test(name, R, *C)
        out["rebuilt_A_order"] = f"(q+1)/4 = 2^{lg(img):.2f}"; out["key_cells"] = M; out["key_space_bits"] = round(lg(3 ** M), 2)
        key = rand_key(rnd, M)
        W = walk(name, R, key, *A)
        if W is None: out["exceptional"] = True; res[name] = out; continue
        zW = Nd.psi(*W)
        e = int(pari.fflog(zW, z, img))
        print(f"{name} fflog: {time.time() - t0:.1f} s", file=sys.stderr, flush=True)
        assert img > 3 ** M
        v = e if e <= img // 2 else e - img
        digits = []
        for _ in range(M):
            d = ((v % 3) + 1) % 3 - 1
            digits.append(d); v = (v - d) // -3
        assert v == 0
        rec = [{0: 0, 1: 1, -1: 2}[d] for d in reversed(digits)]
        out["recovered_key_equals_receivers_key"] = rec == key
        res[name] = out
        print(name, json.dumps(out), flush=True)
    return res


def main():
    global S
    parts = sys.argv[1].split(",") if len(sys.argv) > 1 else ["A", "B", "C"]
    rnd = random.Random(20261003); t0 = time.time()
    S = SJ.Sudo(ECBS)
    path = os.path.join(HERE, "results", "twist_s7.json")
    OUT = json.load(open(path)) if os.path.exists(path) else {}
    OUT.pop("provenance", None)                       # older files: one stamp for all parts
    prov = OUT.setdefault("provenance_by_part", {})
    for p in parts:
        prov[p] = SJ.provenance(ECBS)
    if "A" in parts:
        OUT["A_demo_exhaustive"] = part_A(); print("A", json.dumps(OUT["A_demo_exhaustive"], indent=1), flush=True)
    if "B" in parts:
        OUT["B_invalid_GF3_curves"] = part_B(["Demo", "Toy", "Hobby", "Serious"], rnd)
    if "C" in parts:
        OUT["C_whole_key_from_one_node_point"] = part_C(["Demo", "Toy"], rnd)
    S.close()
    json.dump(OUT, open(path, "w"), indent=1, default=str)
    print(f"twist_s7 {','.join(parts)}: {time.time() - t0:.1f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
