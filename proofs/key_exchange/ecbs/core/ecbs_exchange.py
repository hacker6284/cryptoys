#!/usr/bin/env python3
"""End-to-end ECBS verification with the colour-only peg recipes (ecbs_pegs.py) checked against
PARI (ecbs_ref.py).  For each tier: field arithmetic, base point, Frobenius eigenvalue, key walks for
each key encoding, validation checks, both parties' shared secret, move counts.
Usage: ecbs_exchange.py [tier ...]   (default: all tiers)"""
import sys, time, random, json, math
from ecbs_pegs import Board, MIRROR
from ecbs_ref import Ref, TIERS, pari
import ecbs_keys as K

def hdr(s): print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78, flush=True)
def s(reg): return "".join(reg)

class Tier:
    def __init__(self, name):
        self.name = name; n, k, G = TIERS[name]; self.n, self.k, self.G = n, k, G
        self.R = Ref(n, k); self.l = self.R.l
        # base point BY RULE (visual edition, TOYMASTER_IDEAS F3, re-verified in ecbs_basepoint.py):
        # x = one white peg in hole j (j = 1, 2, ...), y = rhs^((3^n+1)/4) (the root strip); first j with
        # y*y = rhs; then P = 5 (x, y) (the white-red-white-red strip = tau^3 - tau^2 + tau - 1 = 5).
        w = self.R.w; e = (3 ** n + 1) // 4; j = 1
        while True:
            x = w ** j; rhs = x ** 3 - x ** 2 + 1; y = rhs ** e
            if y * y == rhs: break
            j += 1
        self.base_hole = j; self.Rbase = pari([x, y])
        P = self.R.mul(5, self.Rbase)
        assert len(P) == 2 and len(self.R.mul(self.l, P)) == 1
        self.Pref = P; self.P = self.R.unpt(P)
        lam = [int(z) for z in pari.polrootsmod(pari("x^2+x+3"), self.l)]
        self.lam = [z for z in lam if self.R.mul(z, P) == self.R.frob(P)][0]
        self.lbar = (-1 - self.lam) % self.l                     # tau-bar = -1 - tau
        self.mus = [pow(self.lbar, g, self.l) for g in range(8)]
    def board(self): return Board(self.n, self.k)

def arith_check(T, rnd, reps=20):
    B = T.board(); R = T.R; ok = [0, 0, 0]
    for _ in range(reps):
        a, b = R.rand_el(rnd), R.rand_el(rnd)
        ok[0] += R.el(B.mul(a, b)) == R.el(a) * R.el(b)
        ok[1] += R.el(B.cube_keep(a)) == R.el(a) ** 3
        if any(c != '.' for c in a): ok[2] += R.el(B.invert(a)) == 1 / R.el(a)
        else: ok[2] += 1
    return ok

def op_costs(T, rnd, reps=10):
    """average moves of one multiply, cube, inversion, mixed addition at this n."""
    R = T.R; res = {}
    B = T.board(); tot = 0
    for _ in range(reps):
        a, b = R.rand_el(rnd), R.rand_el(rnd); m0 = B.moves; B.mul(a, b); tot += B.moves - m0
    res['mul'] = tot / reps
    tot = 0
    for _ in range(reps):
        a = R.rand_el(rnd); m0 = B.moves; B.cube(a); tot += B.moves - m0
    res['cube'] = tot / reps
    tot = 0
    for _ in range(max(2, reps // 3)):
        a = R.rand_el(rnd); m0 = B.moves; B.invert(a); tot += B.moves - m0
    res['inv'] = tot / max(2, reps // 3)
    # mixed addition on real points
    tot = 0; cnt = 0
    for _ in range(max(2, reps // 3)):
        Q1 = R.mul(rnd.randrange(1, T.l), T.Pref); Q2 = R.mul(rnd.randrange(1, T.l), T.Pref)
        x1, y1 = R.unpt(Q1); x2, y2 = R.unpt(Q2)
        m0 = B.moves; B.mixed_add((x1, y1, B.single('W')), x2, y2); tot += B.moves - m0; cnt += 1
    res['ptadd'] = tot / cnt
    return res

def run_walk(T, walk, bases, terms=None, mus=None):
    """bases: list of affine peg points; returns (affine result, moves, ops)."""
    B = T.board()
    steps = [d if d == 'F' else ('A', d[1], bases[d[2]]) for d in walk]
    Q = B.walk(steps, *bases[0])
    A = B.to_affine(Q)
    return A, B.moves, dict(B.ops)

def tau_bar_chain(T, Bpt, count):
    """hand recipe: B_{g+1} = mirror( B_g + Frobenius(B_g) ), in affine form.  Returns list and moves."""
    Bd = T.board(); out = [Bpt]
    for _ in range(count):
        x, y = out[-1]
        tx = Bd.cube_keep(x); ty = Bd.cube_keep(y)
        Q = Bd.mixed_add((tx, ty, Bd.single('W')), x, y)
        nx, ny = Bd.to_affine(Q); Bd.mirror_in_place(ny); out.append((nx, ny))
    return out, Bd.moves

def trace_check(T, Bpt):
    """Subgroup check: S_m = B + tau B + ... + tau^(m-1) B via an addition chain on m (binary of n);
       accept iff the last step shows tau S_(n-1) = -B.  Any exceptional case -> reject."""
    Bd = T.board(); n = T.n; x0, y0 = Bpt
    S = (Bd.copy(x0), Bd.copy(y0)); m = 1
    bits = bin(n)[3:]
    try:
        for i, b in enumerate(bits):
            # double: S_2m = S_m + tau^m S_m
            tx, ty = Bd.copy(S[0]), Bd.copy(S[1])
            for _ in range(m): tx = Bd.cube(tx); ty = Bd.cube(ty)
            Q = Bd.mixed_add((tx, ty, Bd.single('W')), S[0], S[1])
            Bd.clear(S[0]); Bd.clear(S[1]); S = Bd.to_affine(Q); m *= 2
            if b == '1':
                tx = Bd.cube_keep(S[0]); ty = Bd.cube_keep(S[1])
                if m + 1 == n:                                   # final: tau S_(n-1) must equal -B
                    my = Bd.copy(y0); Bd.mirror_in_place(my)
                    ok = tx == x0 and ty == my
                    return ok, Bd.moves
                Q = Bd.mixed_add((tx, ty, Bd.single('W')), x0, y0)
                Bd.clear(S[0]); Bd.clear(S[1]); S = Bd.to_affine(Q); m += 1
    except ArithmeticError:
        return False, Bd.moves
    raise RuntimeError("chain ended without the final step")

def cofactor_strip(T, Bpt):
    """5B = tau^3 B - tau^2 B + tau B - B via the four-cell strip white, red, white, red."""
    Bd = T.board()
    try:
        Q = Bd.walk(['F', ('A', 'W', Bpt), 'F', ('A', 'R', Bpt), 'F', ('A', 'W', Bpt), 'F', ('A', 'R', Bpt)], *Bpt)
        return Bd.to_affine(Q), Bd.moves
    except ArithmeticError:
        return None, Bd.moves

def full_exchange(T, rnd, enc, param):
    """enc in {'three', 'pegs', 'six', 'twisted'}.  Returns a dict of results."""
    R = T.R; l = T.l; res = {"encoding": enc, "param": param}
    def make():
        if enc == 'three':  g = K.three_state(rnd, param); return K.walk_three_state(g)
        if enc == 'twisted': g = K.three_state(rnd, param); return K.walk_three_state(g, twisted=True)
        if enc == 'pegs':   c = K.pegs_only(rnd, param); return K.walk_pegs(c)
        if enc == 'six':    g = K.six_state(rnd, param); return K.walk_six(g)
    for attempt in range(50):
        (wa, ta), (wb, tb) = make(), make()
        ka = K.scalar(ta, T.lam, T.mus, l); kb = K.scalar(tb, T.lam, T.mus, l)
        nb = max(d[2] for d in wa + wb if d != 'F') + 1
        try:
            if enc == 'twisted':
                Pg = [R.unpt(R.mul(T.mus[g], T.Pref)) for g in range(nb)]     # published base points
            else:
                Pg = [T.P]
            A, mA, opsA = run_walk(T, wa, Pg); Bp, mB, opsB = run_walk(T, wb, Pg)
            res["pub_A_ok"] = R.pt(A) == R.mul(ka, T.Pref); res["pub_B_ok"] = R.pt(Bp) == R.mul(kb, T.Pref)
            # validation (Alice checks B, Bob checks A)
            chk = T.board(); onA = chk.on_curve(*A); onB = chk.on_curve(*Bp); m_on = chk.moves / 2
            trA, m_tr = trace_check(T, A); trB, _ = trace_check(T, Bp)
            # shared: bases derived from the peer point
            if enc == 'twisted':
                Bs, m_tb = tau_bar_chain(T, Bp, nb - 1); As, _ = tau_bar_chain(T, A, nb - 1)
            else:
                Bs, As, m_tb = [Bp], [A], 0
            KA, mKA, _ = run_walk(T, wa, Bs); KB, mKB, _ = run_walk(T, wb, As)
        except ArithmeticError as e:
            res.setdefault("rerolls", 0); res["rerolls"] += 1
            continue
        res.update(on_curve=(onA, onB), trace_ok=(trA, trB), agree=KA[0] == KB[0],
                   matches_ref=R.pt(KA) == R.mul(ka * kb % l, T.Pref),
                   adds_A=opsA.get('ptadd', 0), frob_A=sum(1 for d in wa if d == 'F'),
                   moves=dict(pub=mA, on_curve=m_on, trace=m_tr, tau_bar=m_tb, shared=mKA,
                              per_person=mA + m_on + m_tr + m_tb + mKA))
        return res
    raise RuntimeError("too many exceptional cases")

def adversarial(T, rnd):
    """small-subgroup and invalid-curve inputs against the checks."""
    R = T.R; out = {}
    # an order-5 point: E(GF(3)) embedded (only hole 0 pegged)
    pts5 = []
    for x in (0, 1):
        for y in (1, 2):
            P5 = pari([x * T.R.w ** 0, y * T.R.w ** 0]) if False else pari([pari(x) + 0 * R.w, pari(y) + 0 * R.w])
            if R.on(P5): pts5.append(P5)
    T5 = pts5[0]; T5p = R.unpt(T5)
    chk = T.board()
    out["order5_on_curve"] = chk.on_curve(*T5p); out["order5_in_F3_visual"] = chk.in_F3(*T5p)
    out["order5_trace"] = trace_check(T, T5p)[0]
    out["order5_cofactor"] = cofactor_strip(T, T5p)[0] is None
    # leak demonstration (reference arithmetic): on E(GF(3)) Frobenius is the identity, so the walk
    # over T5 returns (sum of signs) * T5 -- it leaks the sign sum mod 5.
    grids = K.three_state(rnd, 1); walk, terms = K.walk_three_state(grids)
    Q = pari([0])
    for d in walk:
        if d == 'F': Q = R.frob(Q) if len(Q) == 2 else Q
        else: Q = R.add(Q, T5 if d[1] == 'W' else R.neg(T5))
    sgn = sum(d for d, _, _ in terms)
    out["order5_walk_leak(ref)"] = (Q == R.mul(sgn, T5), f"reveals sum of signs mod 5 = {sgn % 5}")
    # mixed point P' = B + T5 with B honest
    Bh = R.mul(rnd.randrange(1, T.l), T.Pref); Mx = R.add(Bh, T5); Mxp = R.unpt(Mx)
    out["mixed_on_curve"] = chk.on_curve(*Mxp); out["mixed_trace"] = trace_check(T, Mxp)[0]
    c5, _ = cofactor_strip(T, Mxp); out["mixed_cofactor_equals_5B"] = c5 is not None and R.pt(c5) == R.mul(5, Bh)
    # invalid curve y^2 = x^3 + 2x^2 + 2 (same a, so the addition script is unchanged)
    R2 = Ref(T.n, T.k, b=2); N2 = 3 ** T.n + 1 - __import__('ecbs_ref').V(T.n, t=2)
    assert T.n > 59 or N2 == int(pari.ellcard(R2.E))
    if N2:
        f = pari.factor(N2, 10**7); small = [int(p) for p in f[0] if 2 < int(p) < 10**6]
        r = max(small) if small else None
        out["invalid_curve_b2_order"] = (N2, [(int(p), int(e)) for p, e in zip(f[0], f[1])])
        if r:
            G2 = pari.ellgenerators(R2.E)[0] if False else None
            while True:
                Z = pari.random(R2.E); Z = R2.mul(N2 // r, Z)
                if len(Z) == 2: break
            Zp = R2.unpt(Z)
            out["invalid_on_curve_check"] = chk.on_curve(*Zp)
            Bd = T.board()
            walk = K.walk_pegs(K.pegs_only(rnd, min(T.n, 25)))[0]
            try:
                Q = Bd.walk([d if d == 'F' else ('A', d[1], Zp) for d in walk], *Zp)
                Kz = R2.pt(Bd.to_affine(Q))
                j = next(j for j in range(r) if R2.mul(j, Z) == Kz)        # attacker's brute force
                out["invalid_leak"] = f"walk output lies in <Z> of order {r}: attacker learns a value mod {r} (index {j})"
            except (ArithmeticError, StopIteration) as e:
                out["invalid_leak"] = f"walk hit {type(e).__name__}"
        else:
            out["invalid_leak"] = "no odd prime factor below 10^6 in the b'=2 order"
    return out

def main(names):
    t0 = time.time(); summary = {}
    for name in names:
        T = Tier(name); rnd = random.Random(1000 + T.n)
        hdr(f"{name}: n = {T.n}, fold x^{T.n} = x^{T.k} + 1, l = {T.l} ({T.l.bit_length()} bits)")
        print("peg arithmetic vs PARI (mul / cube / invert):", arith_check(T, rnd))
        print("base point P (x, y registers, hole 0 first):"); print("  x =", s(T.P[0])); print("  y =", s(T.P[1]))
        print(f"lambda (Frobenius eigenvalue on <P>) = {T.lam}; lambda^n = 1: {pow(T.lam, T.n, T.l) == 1}; "
              f"tau-bar eigenvalue = {T.lbar}")
        oc = op_costs(T, rnd); print("average moves per op:", {k: round(v) for k, v in oc.items()})
        runs = [('three', T.G)]
        if name == "Serious": runs += [('three', 7), ('twisted', 6), ('pegs', 162), ('pegs', 175), ('six', 2)]
        if name == "Hobby": runs += [('twisted', 2), ('pegs', 55)]
        if name == "Toy": runs += [('pegs', 21)]
        summary[name] = {"ops": oc, "runs": []}
        for enc, param in runs:
            tt = time.time(); r = full_exchange(T, rnd, enc, param)
            print(f"\n[{enc} {param}] pub ok {r['pub_A_ok']},{r['pub_B_ok']}  on-curve {r['on_curve']}  trace-check {r['trace_ok']}  "
                  f"agree {r['agree']}  equals ref ab*P {r['matches_ref']}  rerolls {r.get('rerolls', 0)}  "
                  f"additions (Alice) {r['adds_A']}  Frobenius steps {r['frob_A']}   [{time.time()-tt:.0f}s]")
            print("   moves per person: " + ", ".join(f"{k} {v:,.0f}" for k, v in r['moves'].items()))
            summary[name]["runs"].append(r)
        c5 = cofactor_strip(T, T.P); print("\ncofactor strip on P gives 5P:", c5[0] is not None and T.R.pt(c5[0]) == T.R.mul(5, T.Pref), f"({c5[1]:,} moves)")
        adv = adversarial(T, rnd)
        for k_, v in adv.items(): print(f"  adversarial: {k_}: {v}")
        summary[name]["adversarial"] = {k_: str(v) for k_, v in adv.items()}
    json.dump(summary, open("ecbs_exchange.json" if len(names) == 4 else f"ecbs_exchange_{'_'.join(names)}.json", "w"), indent=1, default=str)
    print(f"\n(total {time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main(sys.argv[1:] or list(TIERS))
