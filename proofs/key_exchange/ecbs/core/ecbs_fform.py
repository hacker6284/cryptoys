#!/usr/bin/env python3
"""Review item Q13 (Mathematician, REVIEW.md 2026-09-30), re-derived and re-verified with Crypto's own harness.
(1) F-form mixed addition (char 3, a2 = -1), "the chord rule told from the base point":
      v = x2 Z - X,  u = y2 Z - Y                       (run, rise; slope = u/v)
      F = u^2 Z + v^2 (v + Z)  = v^2 Z (x3 - x2)        ("the gap": new x minus the base point's x, over v^2 Z)
      Z3 = v^3 Z,  X3 = v F + x2 Z3,  Y3 = -(u F + y2 Z3)
    so X3/Z3 = x2 + (x3 - x2) = x3 and Y3/Z3 = -(y2 + slope (x3 - x2)) = y3 (chord line through the base point).
    Scale identities checked in PARI on random points of <P> for every tier.
(2) Peg-level implementation on the workbench board (ecbs_workbench.WB: swap move, slides counted), with
    the receiver's trace chain re-ordered so each chord addition forms the second point's y only AFTER the
    inversion ("lazy y"; in the "+1" step the first point's y too).  Full exchanges checked against PARI;
    bands needed per phase measured; moves include slides.
(3) The same measurement for the current spec schedule (R7 + spec trace chain) on the same keys, for comparison."""
import sys, random, json, math
sys.dont_write_bytecode = True
import ecbs_exchange as X
import ecbs_walks as WK
from ecbs_workbench import WB, WBT, WBnoswap

def identities(name, reps=50, rnd=random.Random(99)):
    T = X.Tier(name); R = T.R; l = T.l; ok = 0
    for _ in range(reps):
        P1 = R.mul(rnd.randrange(1, l), T.Pref); P2 = R.mul(rnd.randrange(1, l), T.Pref)
        x1, y1, x2, y2 = P1[0], P1[1], P2[0], P2[1]
        Z = R.w ** rnd.randrange(1, 3 ** 5) + 1
        Xp, Yp = x1 * Z, y1 * Z
        v = x2 * Z - Xp; u = y2 * Z - Yp
        Fg = u * u * Z + v * v * (v + Z)
        Z3 = v ** 3 * Z; X3 = v * Fg + x2 * Z3; Y3 = -(u * Fg + y2 * Z3)
        lam = (y2 - y1) / (x2 - x1); x3 = lam ** 2 + 1 - x1 - x2; y3 = lam * (x1 - x3) - y1
        ok += (v == Z * (x2 - x1) and u == Z * (y2 - y1) and Fg == v * v * Z * (x3 - x2)
               and X3 / Z3 == x3 and Y3 / Z3 == y3 and Y3 / Z3 == -(y2 + lam * (x3 - x2))
               and R.pt((R.reg(x3), R.reg(y3))) == R.add(P1, P2))
    return ok, reps

class FMixin:
    def madd(self, Q, x2, y2, neg=False):
        """F-form, 12 multiplies, X and Y overwritten in place by v and u."""
        self.op('ptadd'); Xr, Yr, Zr = Q
        self.mirror_in_place(Xr); Zr = self.mac(Xr, x2, Zr, keep_b=True); self.script_step()     # 1 run  v = x2 Z - X
        v = Xr
        if self.is_empty(v):
            for r in (v, Yr, Zr): self.free(r)
            raise ArithmeticError("exceptional case: v is empty")
        self.mirror_in_place(Yr); Zr = self.mac(Yr, y2, Zr, keep_b=True, negate=neg); self.script_step()  # 2 rise u
        u = Yr
        G = self.sq_new(u); self.script_step()                                   # 3a  u^2
        Pg = self.zero(); self.mac(Pg, Zr, G); self.script_step()                # 3b  u^2 Z  (u^2 consumed)
        t = self.sq_new(v); self.script_step()                                   # 3c  v^2
        W = self.zero(); self.mac(W, t, Zr); self.script_step()                  # 3d  v^2 Z  (Z consumed)
        self.mac(Pg, v, t); self.script_step()                                   # 3e  + v^3  (v^2 consumed)
        self.add_in(Pg, W)                                                       # 3f  F = u^2 Z + v^3 + v^2 Z
        Z3 = self.zero(); self.mac(Z3, v, W); self.script_step()                 # 4   new Z = v (v^2 Z)
        X3 = self.zero(); self.mac(X3, Pg, v); self.script_step()                # 5a  v F   (v consumed)
        Z3 = self.mac(X3, x2, Z3, keep_b=True); self.script_step()               # 5b  + x2 Z3
        Y3 = self.zero(); self.mac(Y3, u, Pg, negate=True); self.free(u); self.script_step()   # 6a  -u F
        Z3 = self.mac(Y3, y2, Z3, keep_b=True, negate=not neg); self.script_step()             # 6b  - (+-y2) Z3
        return (X3, Y3, Z3)

    def aadd_lazy(self, x1, y1, x2, make_y2):
        """(x1, y1) kept; x2 consumed; the second point's y is MADE after the inversion."""
        dx = x2; self.add_in(dx, x1, True)
        if self.is_empty(dx):
            self.free(dx); raise ArithmeticError("exceptional: equal x")
        di = self.inv_new(dx)
        dy = make_y2(); self.add_in(dy, y1, True)
        lam = self.zero(); self.mac(lam, di, dy); self.free(di)
        x3 = self.sq_new(lam); self.drop(x3, 0, 'W')
        self.add_in(x3, x1); self.add_in(x3, dx, True); self.free(dx)
        t = self.new_copy(x1); self.add_in(t, x3, True)
        y3 = self.zero(); self.mac(y3, lam, t); self.free(lam)
        self.add_in(y3, y1, True)
        return x3, y3

    def trace_check(self, bx, by):
        n = self.n; S = (self.new_copy(bx), self.new_copy(by)); m = 1
        try:
            for b in bin(n)[3:]:
                tx = self.cube_times(S[0], m)
                nx, ny = self.aadd_lazy(S[0], S[1], tx, lambda m_=m, s=S[1]: self.cube_times(s, m_))
                for r in (S[0], S[1]): self.free(r)
                S = (nx, ny); m *= 2; self.script_step()
                if b == '1':
                    tx = self.cube_new(self.new_copy(S[0]))
                    if m + 1 == n:
                        ty = self.cube_new(self.new_copy(S[1])); my = self.new_copy(by, mirror=True)
                        ok = tx == bx and ty == my
                        for r in (tx, ty, my, S[0], S[1]): self.free(r)
                        return ok
                    self.free(S[0])
                    dx = self.new_copy(bx); self.add_in(dx, tx, True)            # run = B's x - tau(S)'s x
                    if self.is_empty(dx): raise ArithmeticError("exceptional")
                    di = self.inv_new(dx)
                    ty = self.cube_new(S[1])                                    # tau(S)'s y, made now (S_y consumed)
                    dy = self.new_copy(by); self.add_in(dy, ty, True)
                    lam = self.zero(); self.mac(lam, di, dy); self.free(di)
                    nx = self.sq_new(lam); self.drop(nx, 0, 'W'); self.add_in(nx, tx); self.add_in(nx, dx, True); self.free(dx)
                    t = self.new_copy(tx); self.add_in(t, nx, True)
                    ny = self.zero(); self.mac(ny, lam, t); self.free(lam); self.add_in(ny, ty, True)
                    self.free(tx); self.free(ty)
                    S = (nx, ny); m += 1; self.script_step()
        except ArithmeticError:
            return False

class WBF(FMixin, WB): pass
class WBFnoswap(FMixin, WBnoswap): pass

def measure(name, enc, p, kind, cls, reps, rnd):
    got = []; bands = {}; rer = 0; slides = []
    while len(got) < reps:
        B = [None]
        def mk(n, k, _c=cls): B[0] = _c(n, k); return B[0]
        try: r = WK.run(name, enc, p, rnd, kind, board=mk)
        except ArithmeticError: rer += 1; continue
        assert all(r['ok']) and r['leaks'] == 0, r
        got.append(r); slides.append(B[0].slide_moves)
        for ph, v in B[0].bands.items(): bands[ph] = max(bands.get(ph, 0), v)
    mv = sum(x['moves'] + x['ctrl'] for x in got) / reps
    return dict(bands=bands, moves=mv, slides=sum(slides) / reps, rerolls=rer, reps=reps,
                tally=max(x['tally_max'] for x in got), val=sum(x['val'] for x in got) / reps)

def bad_point_test(name, cls, rnd, reps=3):
    """receiver side only: honest B accepted, B + T5 rejected (T5 = (1,1), rational 5-torsion)"""
    T = X.Tier(name); R = T.R; l = T.l; res = []
    from ecbs_ref import pari
    T5 = pari([R.w ** 0, R.w ** 0]); assert R.on(T5)
    for kind in ['honest'] * reps + ['B+T5'] * reps:
        Bp = R.mul(rnd.randrange(1, l), T.Pref)
        if kind == 'B+T5': Bp = R.add(Bp, T5)
        bx, by = R.unpt(Bp); Bd = cls(T.n, T.k); bx, by = Bd.new_copy(bx), Bd.new_copy(by)
        res.append((kind, Bd.on_curve_check(bx, by), Bd.trace_check(bx, by)))
    return res

def main():
    rnd = random.Random(2026); out = {}
    print("== 1. F-form scale identities (PARI, random points of <P>)")
    for name in ("Demo", "Toy", "Hobby", "Serious"):
        ok, reps = identities(name); out[f"identities_{name}"] = ok
        print(f"  {name}: {ok}/{reps} additions satisfy run, rise, gap = v^2 Z (x3 - x2), X3/Z3 = x3, Y3/Z3 = y3 = -(y2 + slope*gap), equal PARI")
    print("\n== 2. Receiver check with lazy y: honest accepted, B + T5 rejected")
    for name in ("Toy", "Hobby", "Serious"):
        r = bad_point_test(name, WBF, rnd, 2); out[f"badpoint_{name}"] = r
        print(f"  {name}: " + "; ".join(f"{k}: on-curve {a}, trace {b}" for k, a, b in r))
    print("\n== 3. Full exchanges on the workbench board (pegs-only keys), spec schedule vs F-form + lazy y")
    plan = [("Demo", 2, 'affine', 20), ("Demo", 2, 'proj', 20), ("Toy", 16, 'proj', 10), ("Hobby", 51, 'proj', 5), ("Serious", 162, 'proj', 5)]
    only = sys.argv[1:]
    for name, p, kind, reps in plan:
        if only and name not in only: continue
        variants = [("spec", WB), ("F-form+lazy-y", WBF)] if kind == 'proj' else [("spec chord + trace chain", WB), ("chord + trace WALK", WBT), ("chord + lazy-y chain", WBF)]
        if name in ("Toy", "Hobby", "Serious") and kind == 'proj': variants.append(("F-form+lazy-y, NO swap", WBFnoswap))
        for lab, cls in variants:
            r = measure(name, 'pegs', p, kind, cls, reps, random.Random(f"{name}-{p}-{kind}"))   # same keys for every variant
            out[f"{name}_pegs{p}_{kind}_{lab}"] = r
            print(f"  {name:7s} pegs {p:3d} {kind:6s} [{lab:26s}] correct x{reps} (+{r['rerolls']} re-rolls): bands "
                  + ", ".join(f"{ph} {v}" for ph, v in r['bands'].items())
                  + f"; moves/person {r['moves']/1e6:.4f} M incl. slides {r['slides']/1e6:.4f} M; validation {r['val']/1e6:.4f} M; tally {r['tally']}", flush=True)
    json.dump(out, open("ecbs_fform%s.json" % ("_" + "_".join(only) if only else ""), "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
