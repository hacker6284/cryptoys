#!/usr/bin/env python3
"""No-paper ECBS: every piece of working state lives in pegs on grids.

This re-implements the ECBS recipes with explicit *register slots* so the peak number of live
registers can be measured, and with the "no hidden state" rules:
  * a multiply's outer loop walks the pegs of ONE factor (b) and LIFTS each peg as it is used, so
    progress is visible.  If b is still needed afterwards, each lifted peg is instead JUMPED into a
    fresh twin slot (b survives, moved) -> +1 slot while the multiply runs.
  * the product (or the multiply-accumulate) goes into a destination register plus an overflow
    area of n-1 holes; cubing uses a fresh destination plus 2n-2 overflow holes and consumes its input.
  * loop counters (the Itoh-Tsujii and trace-chain "cube m times") are unary tallies of pegs,
    the script position is a single marker peg, the walk position is a marker peg on a cursor grid.
All results are checked against PARI; peaks are measured, not assumed."""
import sys, random, json
from ecbs_pegs import Board, MIRROR, NEXT, PREV
import ecbs_exchange as X
import ecbs_keys as K

class PB(Board):
    def __init__(self, n, k):
        super().__init__(n, k)
        self.alive = set(); self.ovf = 0; self.phase = 'idle'; self.peak = {}; self.ctrl_moves = 0
        self.tally_max = 0
    # ---------------- slot accounting
    def _note(self):
        v = len(self.alive) + self.ovf_blocks()
        p = self.peak.setdefault(self.phase, [0, 0, 0])
        if (len(self.alive), self.ovf) > (p[1], p[2]) and v >= p[0]: pass
        if v > p[0]: self.peak[self.phase] = [v, len(self.alive), self.ovf]
    def ovf_blocks(self): return self.ovf          # 1 for a multiply (n-1 holes), 2 for a cube (2n-2)
    def reg(self, r): self.alive.add(id(r)); self._note(); return r
    def zero(self): return self.reg(['.'] * self.n)
    def free(self, r):
        self.moves += sum(c != '.' for c in r); r[:] = ['.'] * self.n; self.alive.discard(id(r))
    def new_copy(self, a, mirror=False):
        r = self.zero()
        for i, c in enumerate(a):
            if c != '.': r[i] = MIRROR[c] if mirror else c; self.moves += 1
        return r
    def add_in(self, r, s, mirror=False):
        for i, c in enumerate(s):
            if c != '.': self.drop(r, i, c, mirror)
    # ---------------- multiply-accumulate: dst += sign * a * b  (b consumed or moved to a twin)
    def mac(self, dst, a, b, keep_b=False, negate=False):
        self.op('mul'); n = self.n
        twin = self.zero() if keep_b else None
        self.ovf = 1; self._note()
        strip = dst[:] + ['.'] * (n - 1)
        for i in range(n - 1, -1, -1):                       # highest remaining peg of b first
            c = b[i]
            if c == '.': continue
            b[i] = '.'; self.moves += 1                        # lift it (progress is visible)
            if keep_b: twin[i] = c; self.moves += 1            # ... and place it in the twin (a jump)
            mir = (c == 'R') != negate
            for j, d in enumerate(a):
                if d != '.': self.drop(strip, i + j, d, mir)
        res = self.fold(strip); dst[:] = res
        self.ovf = 0
        self.alive.discard(id(b))
        if keep_b: return twin                                 # caller rebinds b to the twin
        return None
    def mul_new(self, a, b, keep_b=False):
        d = self.zero(); t = self.mac(d, a, b, keep_b); return d, t
    def sq_new(self, a):
        c = self.new_copy(a); d = self.zero(); self.mac(d, a, c); return d
    def cube_new(self, a):
        """fresh destination; the input's pegs jump (highest first) to hole 3i; then fold."""
        self.op('cube'); n = self.n
        d = self.zero(); self.ovf = 2; self._note()
        strip = ['.'] * (3 * n - 2)
        for i in range(n - 1, -1, -1):
            if a[i] != '.': strip[3 * i] = a[i]; a[i] = '.'; self.moves += 2
        self.alive.discard(id(a))
        d[:] = self.fold(strip); self.ovf = 0
        return d
    def cube_times(self, a, m, keep=True):
        """cube m times, counting with a unary tally (m pegs, moved one per cube)."""
        t = self.new_copy(a) if keep else a
        self.tally_max = max(self.tally_max, m); self.ctrl_moves += 3 * m
        for _ in range(m): t = self.cube_new(t)
        return t
    def script_step(self, k=1): self.ctrl_moves += 2 * k     # marker peg jumps to the next script line
    # ---------------- Itoh-Tsujii inversion with tallies; consumes nothing, returns new register
    def inv_new(self, x):
        self.op('inv'); n = self.n
        e = self.new_copy(x); m = 1
        for b in bin(n - 1)[3:]:
            t = self.cube_times(e, m)                          # t = e^(3^m)   (copy of e, cubed)
            ne, _ = self.mul_new(e, t); self.free(e); e = ne; m *= 2; self.script_step()
            if b == '1':
                t = self.cube_new(e)                           # e consumed
                e, _ = self.mul_new(x, t); m += 1; self.script_step()
        inv = self.cube_new(e)
        c = self.new_copy(x); norm, _ = self.mul_new(inv, c)
        assert all(q == '.' for q in norm[1:]) and norm[0] != '.'
        if norm[0] == 'R': self.mirror_in_place(inv)
        self.free(norm)
        return inv
    # ---------------- low-memory mixed addition  Q + (x2, s*y2)
    def madd(self, Q, x2, y2, neg=False):
        self.op('ptadd'); Xr, Yr, Zr = Q
        v = self.new_copy(Xr, mirror=True)                     # v = -X
        Zr = self.mac(v, x2, Zr, keep_b=True); self.script_step()          # v += x2 Z
        if self.is_empty(v):
            for r in (v, Xr, Yr, Zr): self.free(r)
            raise ArithmeticError("exceptional case: v is empty")
        u = self.new_copy(Yr, mirror=True)                     # u = -Y
        Zr = self.mac(u, y2, Zr, keep_b=True, negate=neg); self.script_step()   # u += +-y2 Z
        A = self.sq_new(u); self.script_step()                 # A = u^2
        A2 = self.zero(); self.mac(A2, Zr, A); A = A2; self.script_step()   # A = u^2 Z  (u^2 consumed)
        vv = self.sq_new(v); self.script_step()                # vv = v^2   (before w: keeps the peak at 10)
        w = self.new_copy(v); self.add_in(w, Xr, True); self.add_in(w, Zr, True); self.script_step()  # w = v - X - Z
        self.mac(A, vv, w, negate=True); self.script_step()    # A -= vv w   (w consumed)
        s = self.new_copy(A, mirror=True)                      # s = -A
        self.mac(s, vv, Xr); self.script_step()                # s += vv X  (X consumed)
        X3 = self.zero(); self.mac(X3, v, A); self.script_step()            # X3 = v A  (A consumed)
        vvv = self.zero(); self.mac(vvv, vv, v); self.free(vv); self.script_step()   # vvv = vv v (v consumed)
        Y3 = self.zero(); self.mac(Y3, s, u); self.free(s); self.script_step()   # Y3 = u s (u consumed)
        self.mac(Y3, vvv, Yr, negate=True); self.script_step() # Y3 -= vvv Y (Y consumed)
        Z3 = self.zero(); self.mac(Z3, vvv, Zr); self.free(vvv); self.script_step()   # Z3 = vvv Z
        return (X3, Y3, Z3)
    def frob(self, Q): return tuple(self.cube_new(c) for c in Q)
    def affine(self, Q):
        Xr, Yr, Zr = Q; zi = self.inv_new(Zr); self.free(Zr)
        x = self.zero(); self.mac(x, zi, Xr)                   # X consumed
        y = self.zero(); self.mac(y, zi, Yr)
        self.free(zi); return (x, y)
    def pwalk(self, digits, bx, by):
        Q = None
        for d in digits:
            if d == 'F':
                self.ctrl_moves += 2                            # cursor marker advances one cell
                if Q is not None: Q = self.frob(Q)
            else:
                _, colour, _ = d
                if Q is None:
                    Q = (self.new_copy(bx), self.new_copy(by, mirror=(colour == 'R')), self.reg(['W'] + ['.'] * (self.n - 1)))
                    self.moves += 1
                else:
                    Q = self.madd(Q, bx, by, neg=(colour == 'R'))
        return Q
    # ---------------- affine addition (for the trace check): (x1,y1) + (x2,y2), inputs kept
    def aadd(self, x1, y1, x2, y2, keep2=False):
        """(x1,y1) + (x2,y2), affine.  (x1,y1) kept; (x2,y2) consumed unless keep2.
           x3 = L^2 - a - x1 - x2 = L^2 + 1 + x1 - dx   (a = 2, -2 = 1 mod 3, dx = x2 - x1)
           y3 = L (x1 - x3) - y1"""
        if keep2: x2, y2 = self.new_copy(x2), self.new_copy(y2)
        dx = x2; self.add_in(dx, x1, True)                                # dx = x2 - x1, in place
        if self.is_empty(dx):
            self.free(dx); self.free(y2); raise ArithmeticError("exceptional: equal x")
        di = self.inv_new(dx)
        dy = y2; self.add_in(dy, y1, True)                                # dy = y2 - y1, in place
        lam = self.zero(); self.mac(lam, di, dy); self.free(di)          # dy consumed
        x3 = self.sq_new(lam); self.drop(x3, 0, 'W')                      # L^2 + 1  (-a = +1)
        self.add_in(x3, x1); self.add_in(x3, dx, True); self.free(dx)     # + x1 - dx
        t = self.new_copy(x1); self.add_in(t, x3, True)                   # x1 - x3
        y3 = self.zero(); self.mac(y3, lam, t); self.free(lam)           # t consumed
        self.add_in(y3, y1, True)
        return x3, y3
    def trace_check(self, bx, by):
        n = self.n; S = (self.new_copy(bx), self.new_copy(by)); m = 1
        try:
            for b in bin(n)[3:]:
                tx = self.cube_times(S[0], m); ty = self.cube_times(S[1], m)
                nx, ny = self.aadd(S[0], S[1], tx, ty)            # tx, ty consumed
                for r in (S[0], S[1]): self.free(r)
                S = (nx, ny); m *= 2; self.script_step()
                if b == '1':
                    tx = self.cube_new(self.new_copy(S[0])); ty = self.cube_new(self.new_copy(S[1]))
                    if m + 1 == n:
                        my = self.new_copy(by, mirror=True)
                        ok = tx == bx and ty == my
                        for r in (tx, ty, my, S[0], S[1]): self.free(r)
                        return ok
                    for r in (S[0], S[1]): self.free(r)
                    nx, ny = self.aadd(tx, ty, bx, by, keep2=True)
                    for r in (tx, ty): self.free(r)
                    S = (nx, ny); m += 1; self.script_step()
        except ArithmeticError:
            return False
    def on_curve_check(self, x, y):
        lhs = self.sq_new(y)
        rhs = self.cube_new(self.new_copy(x)); x2 = self.sq_new(x)
        self.add_in(rhs, x2, True); self.free(x2); self.drop(rhs, 0, 'W')
        ok = lhs == rhs; self.free(lhs); self.free(rhs); return ok

LAYOUT = {  # aligned layouts: (slot holes, slots per grid or grids per slot)
    "Demo": dict(slot="one 10-hole row per register (7 used)", per_grid=10),
    "Toy": dict(slot="one 5x5 quarter-grid per register (23 of 25 used)", per_grid=4),
    "Hobby": dict(slot="one grid per register (59 of 100 used)", per_grid=1),
    "Serious": dict(slot="two grids per register (179 of 200 used)", per_grid=0.5)}

def grids_needed(name, n, slots, ovf):
    ovf_holes = {0: 0, 1: n - 1, 2: 2 * n - 2}[ovf]
    per = LAYOUT[name]["per_grid"]
    unit = 100 / per                                   # holes per aligned slot
    ovf_units = -(-ovf_holes // int(unit)) if ovf_holes else 0
    aligned = (slots + ovf_units) / per
    aligned = -(-(slots + ovf_units) // per) if per >= 1 else (slots + ovf_units) * 2
    packed = -(-(slots * n + ovf_holes) // 100)
    return int(aligned), int(packed), slots * n + ovf_holes

def run(name, enc, param, rnd):
    T = X.Tier(name); R = T.R; n, l = T.n, T.l
    if enc == 'three': walk, terms = K.walk_three_state(K.three_state(rnd, param)); keygrids = param
    elif enc == 'pegs': walk, terms = K.walk_pegs(K.pegs_only(rnd, param)); keygrids = -(-param // 100)
    elif enc == 'six': walk, terms = K.walk_six(K.six_state(rnd, param)); keygrids = param
    ka = K.scalar(terms, T.lam, T.mus, l)
    B = PB(n, T.k)
    # public walk: the base point P must itself be pegged (2 registers)
    B.phase = 'public walk'
    px, py = B.new_copy(T.P[0]), B.new_copy(T.P[1])
    Q = B.pwalk(walk, px, py); A = B.affine(Q)
    ok_pub = R.pt(A) == R.mul(ka, T.Pref)
    B.free(px); B.free(py)
    m_pub = B.moves
    # the partner copies A; we receive and validate B (use an honest random public point)
    B.free(A[0]); B.free(A[1])
    kb = rnd.randrange(1, l); Bp = R.unpt(R.mul(kb, T.Pref))
    B.phase = 'validation'
    bx, by = B.new_copy(Bp[0]), B.new_copy(Bp[1])
    oc = B.on_curve_check(bx, by); tc = B.trace_check(bx, by)
    m_val = B.moves - m_pub
    B.phase = 'shared walk'
    Q = B.pwalk(walk, bx, by); Kx, Ky = B.affine(Q)
    ok_sh = R.pt((Kx, Ky)) == R.mul(ka * kb % l, T.Pref)
    B.free(bx); B.free(by)
    left = len(B.alive) - 2
    return dict(ok=(ok_pub, oc, tc, ok_sh), leaks=left, peaks=B.peak, moves=B.moves, ctrl=B.ctrl_moves,
                pub=m_pub, val=m_val, tally_max=B.tally_max, keygrids=keygrids, n=n)

def main():
    rnd = random.Random(4242); out = {}
    plan = {"Demo": [('three', 1), ('pegs', 3)], "Toy": [('three', 1), ('pegs', 19)],
            "Hobby": [('three', 2), ('pegs', 55), ('six', 1)],
            "Serious": [('three', 6), ('pegs', 175), ('six', 2)]}
    budget = {"Demo": 2, "Toy": 5, "Hobby": 11, "Serious": 32}
    for name, runs in plan.items():
        print("=" * 78); print(f"{name}: proposed no-paper budget {budget[name]} grids per player; aligned layout: {LAYOUT[name]['slot']}")
        print("=" * 78)
        for enc, p in runs:
            for attempt in range(20):
                try: r = run(name, enc, p, rnd); break
                except ArithmeticError: continue
            n = r['n']
            print(f"[{enc} {p}] correct (pub, on-curve, trace, shared) = {r['ok']}; stray registers left = {r['leaks']}; "
                  f"moves per person {r['moves']:,} (+ control-marker moves {r['ctrl']:,}); max tally {r['tally_max']}")
            worst_a = worst_p = 0
            for ph, (v, s, o) in r['peaks'].items():
                a, pk, holes = grids_needed(name, n, s, o)
                worst_a = max(worst_a, a); worst_p = max(worst_p, pk)
                print(f"    peak in {ph:12s}: {s} live registers + overflow({'n-1' if o == 1 else '2n-2' if o == 2 else '0'}) "
                      f"= {holes} holes -> workspace grids aligned {a}, packed {pk}")
            key = r['keygrids']; cursor = 1
            ctrl_holes = r['tally_max'] + 16 + 12 + 8          # colour-flip tally, script marker line, chain line, fleet index
            print(f"    + key {key} grid(s) + cursor grid 1 + control ({ctrl_holes} holes: tally, script line, chain line, fleet index)")
            print(f"    TOTAL aligned: {worst_a + key + cursor} grids + control;  packed: {worst_p + key + cursor} grids + control "
                  f"(budget {budget[name]})")
            out[f"{name}_{enc}{p}"] = dict(r, worst_aligned=worst_a, worst_packed=worst_p, ctrl_holes=ctrl_holes)
    json.dump(out, open("ecbs_physical.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
