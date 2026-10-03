#!/usr/bin/env python3
"""Walk variants for the visual edition, all checked against PARI:
  * 'proj'  : the 12-multiply mixed-addition walk of ecbs_physical (fast; needs the 3-line verse)
  * 'affine': the textbook chord walk  (slope = dy/dx; x3 = slope^2 + 1 + x1 - dx; y3 = slope(x1 - x3) - y1),
              base point kept, accumulator consumed; no final inversion
  * DemoPB  : Demo-only 'slide' arithmetic with NO overflow holes (Horner: slide the product one hole,
              the peg pushed off the 7th hole drops on hole 0 and 2 holes back), so Demo fits one target grid.
Also the control inventory (every marker row that must exist) and the band-layout grid count per tier."""
import sys, random, json
import ecbs_physical as PH
from ecbs_physical import PB
import ecbs_exchange as X
import ecbs_keys as K
from ecbs_layout import Tower

class APB(PB):
    def awalk(self, digits, bx, by):
        Q = None
        for d in digits:
            if d == 'F':
                self.ctrl_moves += 2
                if Q is not None: Q = (self.cube_new(Q[0]), self.cube_new(Q[1]))
            else:
                _, colour, _ = d
                if Q is None:
                    Q = (self.new_copy(bx), self.new_copy(by, mirror=(colour == 'R'))); continue
                if colour == 'R': self.mirror_in_place(by)
                try:
                    Q = self.aadd(bx, by, Q[0], Q[1]); self.script_step(5)
                finally:
                    if colour == 'R': self.mirror_in_place(by)
        if Q is None: raise ArithmeticError("empty key")
        return Q

class DemoPB(APB):
    """no overflow: every product is built by Horner 'slides' inside the register's own row
       (the row's first spare hole catches the peg pushed off the end for one moment)."""
    def slide(self, D):
        n, k = self.n, self.k
        spill = D[n - 1]
        self.moves += 2 * sum(c != '.' for c in D)           # every peg jumps one hole on
        D[1:] = D[:-1]; D[0] = '.'
        if spill != '.':
            self.moves += 1                                     # lift it from the spare hole
            self.drop(D, 0, spill); self.drop(D, k, spill)      # hole 0 and "2 holes back" (hole 5)
    def horner(self, a, b, keep_b=False, negate=False):
        n = self.n; D = self.zero(); twin = self.zero() if keep_b else None
        for i in range(n - 1, -1, -1):
            if any(c != '.' for c in D): self.slide(D)
            c = b[i]
            if c == '.': continue
            b[i] = '.'; self.moves += 1
            if keep_b: twin[i] = c; self.moves += 1
            self.add_in(D, a, mirror=((c == 'R') != negate))
        self.alive.discard(id(b))
        return D, twin
    def mac(self, dst, a, b, keep_b=False, negate=False):
        self.op('mul')
        if all(c == '.' for c in dst):                          # empty destination: build it in place
            self.alive.discard(id(dst))
            D, twin = self.horner(a, b, keep_b, negate); dst[:] = D; self.alive.discard(id(D)); self.alive.add(id(dst))
        else:
            D, twin = self.horner(a, b, keep_b, negate); self.add_in(dst, D); self.free(D)
        return twin
    def mul_new(self, a, b, keep_b=False):
        self.op('mul'); D, t = self.horner(a, b, keep_b); return D, t
    def cube_new(self, a):
        self.op('cube'); n = self.n; D = self.zero()
        for i in range(n - 1, -1, -1):
            if any(c != '.' for c in D):
                for _ in range(3): self.slide(D)
            if a[i] != '.': c = a[i]; a[i] = '.'; self.moves += 1; self.drop(D, 0, c)
        self.alive.discard(id(a)); return D

    def trace_walk_check(self, bx, by):
        """Demo validation as a WALK: n-1 all-white cells over B (S <- tau S + B), then one more
           Frobenius must give the mirror of B.  Any exceptional chord -> reject."""
        try:
            S = self.awalk(['F', ('A', 'W', 0)] * (self.n - 1), bx, by)
        except ArithmeticError:
            return False
        tx, ty = self.cube_new(S[0]), self.cube_new(S[1])
        my = self.new_copy(by, mirror=True)
        ok = tx == bx and ty == my
        for r in (tx, ty, my): self.free(r)
        return ok
    trace_check = trace_walk_check

def run(name, enc, param, rnd, walk_kind='affine', board=None):
    T = X.Tier(name); R = T.R; n, l = T.n, T.l
    if enc == 'three': walk, terms = K.walk_three_state(K.three_state(rnd, param)); keygrids = param
    elif enc == 'pegs': walk, terms = K.walk_pegs(K.pegs_only(rnd, param)); keygrids = -(-param // 100)
    elif enc == 'six': walk, terms = K.walk_six(K.six_state(rnd, param)); keygrids = param
    ka = K.scalar(terms, T.lam, T.mus, l)
    B = (board or APB)(n, T.k)
    def do_walk(bx, by):
        if walk_kind == 'affine': return B.awalk(walk, bx, by)
        Q = B.pwalk(walk, bx, by)
        if Q is None: raise ArithmeticError("empty key")
        return B.affine(Q)
    B.phase = 'public walk'
    px, py = B.new_copy(T.P[0]), B.new_copy(T.P[1])
    A = do_walk(px, py); ok_pub = R.pt(A) == R.mul(ka, T.Pref)
    B.free(px); B.free(py); m_pub = B.moves
    B.free(A[0]); B.free(A[1])
    kb = rnd.randrange(1, l); Bp = R.unpt(R.mul(kb, T.Pref))
    B.phase = 'validation'
    bx, by = B.new_copy(Bp[0]), B.new_copy(Bp[1])
    oc = B.on_curve_check(bx, by); tc = B.trace_check(bx, by); m_val = B.moves - m_pub
    B.phase = 'shared walk'
    Kx, Ky = do_walk(bx, by)
    ok_sh = R.pt((Kx, Ky)) == R.mul(ka * kb % l, T.Pref)
    B.free(bx); B.free(by)
    return dict(ok=(ok_pub, oc, tc, ok_sh), leaks=len(B.alive) - 2, peaks=B.peak, moves=B.moves, ctrl=B.ctrl_moves,
                pub=m_pub, val=m_val, tally_max=B.tally_max, keygrids=keygrids, n=n, ops=dict(B.ops))

def chain_len(m): return len(bin(m)) - 3            # one program hole per step after the leading 1
def control_items(name, walk_kind, tally_max, fleets):
    n = TIERS_N[name]
    items = {"tally (colour-flip)": tally_max,
             "script line marker": 12 if walk_kind == 'proj' else 5,
             "validation script marker (chord add)": 5,
             "inversion chain row (from n-1)": chain_len(n - 1),
             "trace chain row (from n)": chain_len(n),
             "walk ruler: row": 10, "walk ruler: column": 10,
             "cell phase (cube x, cube y[, cube Z], add)": 4 if walk_kind == 'proj' else 3,
             "protocol phase (walk, check, walk, extract)": 4}
    if fleets > 1: items["fleet index"] = fleets
    return items
TIERS_N = {"Demo": 7, "Toy": 23, "Hobby": 59, "Serious": 179}

WIDTH = {"Demo": 10, "Toy": 5, "Hobby": 10, "Serious": 10}     # Toy registers live in 5x5 quarter-grids
def ctrl_rows(items):
    """each control item gets its own 10-hole row(s), except that two items of <= 5 holes may share a
       row (left half / right half)."""
    big = sum(-(-v // 10) for v in items.values() if v > 5)
    small = sum(1 for v in items.values() if v <= 5)
    return big + -(-small // 2)
def grid_count(name, peaks, items, keygrids):
    n = TIERS_N[name]; w = WIDTH[name]
    H = -(-n // w)
    bands = max(s + o for (_, s, o) in peaks.values())
    cr = ctrl_rows(items)
    if w == 5:                                   # quarter-grids: 4 per grid; control on its own grid(s)
        work = -(-bands // 4); ctrl = -(-cr // 10); spare = (work * 4 - bands) * 25
        return dict(bands=bands, band_rows=f"{H} (5-wide)", ctrl_rows=cr, work_grids=work + ctrl, total=work + ctrl + keygrids,
                    spare_rows=f"{ctrl*10 - cr} control rows + {work*4-bands} quarter-grid(s)")
    rows = bands * H
    ws = -(-(rows + cr) // 10)
    return dict(bands=bands, band_rows=H, work_rows=rows, ctrl_rows=cr, work_grids=ws, total=ws + keygrids,
                spare_rows=ws * 10 - rows - cr)

def demo_exhaustive(out):
    """every affine point of E(GF(3^7)): on-curve + trace-walk check must accept exactly <P> minus O;
       honest subgroup points must never hit an exceptional chord; and the one-grid hole plan must fit."""
    from ecbs_ref import pari
    T = X.Tier("Demo"); R = T.R; l = T.l
    pts = []
    tot = acc = acc_sub = 0; bad = 0; exc_honest = 0; peak = 0
    w = R.w
    for i in range(3 ** 7):
        # element with base-3 digits of i as coefficients
        digs = []; t = i
        for _ in range(7): digs.append(t % 3); t //= 3
        x = sum(int(d) * w ** j for j, d in enumerate(digs)) if i else 0 * w
        rhs = x ** 3 + 2 * x ** 2 + 1
        if rhs == 0 * w: ys = [0 * w]
        elif pari.issquare(rhs): y = pari.sqrt(rhs); ys = [y, -y]
        else: continue
        for y in ys:
            Pt = pari([x, y]); insub = len(R.mul(l, Pt)) == 1
            B = DemoPB(7, 5); bx, by = R.unpt(Pt); bx, by = B.new_copy(bx), B.new_copy(by)
            ok = B.on_curve_check(bx, by) and B.trace_walk_check(bx, by)
            peak = max(peak, max(v[1] + v[2] for v in B.peak.values()))
            tot += 1; acc += ok; acc_sub += ok and insub; bad += ok != insub
    print(f"  exhaustive over all {tot} affine points: accepted {acc}, of which in <P>: {acc_sub}; "
          f"misclassified {bad}; worst peak during checks {peak} registers")
    # honest exceptional chords in the trace walk: tau S_m = +-B with S_m = (1 + lam + ... + lam^(m-1)) B
    lam = T.lam; exc = []
    for m in range(1, 6):                       # steps S_{m+1} = tau S_m + B actually performed (m = 1..n-2)
        sm = sum(pow(lam, j, l) for j in range(m)) % l
        if (lam * sm) % l in (1, l - 1): exc.append(m)
    print(f"  honest trace-walk exceptional steps among the performed m = 1..5 (lam*s_m = +-1 mod l; m = 6 is the final check itself): {exc or 'none'}")
    # hole plan for the single target grid (10 x 10): rows 0-6 registers (cols 0-6) + slide hole (col 7)
    plan = {"registers (rows 0-6, holes 0-6)": 7 * 7, "slide holes (col 7, rows 0-6; empty between slides)": 7,
            "cell phase + protocol phase (cols 8-9, rows 0-6)": 3 + 4,
            "walk ruler row (row 7) - reused as the trace-walk position": 10, "walk ruler column (row 8)": 10,
            "row 9: tally 3 + chord-script marker 5 + inversion chain 2": 3 + 5 + 2}
    used = sum(plan.values())
    print(f"  one-grid hole plan: {used} of 100 holes named ({100 - used} unassigned): " + "; ".join(f"{k}: {v}" for k, v in plan.items()))
    out['Demo_exhaustive'] = dict(accepted=acc, accepted_in_subgroup=acc_sub, misclassified=bad, peak=peak,
                                  honest_exceptional=exc, plan=plan, plan_used=used)

def main():
    rnd = random.Random(777); out = {}
    tiers = sys.argv[1:] or ["Demo", "Toy", "Hobby", "Serious"]
    plan = {"Demo": [('three', 1), ('pegs', 3)], "Toy": [('three', 1), ('pegs', 19)],
            "Hobby": [('three', 2), ('pegs', 55), ('six', 1)],
            "Serious": [('three', 6), ('three', 7), ('pegs', 175), ('pegs', 200), ('six', 2)]}
    for name in tiers:
        print("=" * 78 + f"\n{name}\n" + "=" * 78, flush=True)
        for enc, p in plan[name]:
            for kind in ('proj', 'affine'):
                reps = 3 if name != 'Serious' else 1
                res = []
                while len(res) < reps:
                    try: r = run(name, enc, p, rnd, kind)
                    except ArithmeticError: continue
                    assert all(r['ok']) and r['leaks'] == 0, r
                    res.append(r)
                mv = sum(r['moves'] + r['ctrl'] for r in res) / reps
                pk = res[0]['peaks']; items = control_items(name, kind, max(r['tally_max'] for r in res), p if enc == 'three' else 1)
                g = grid_count(name, pk, items, res[0]['keygrids'])
                print(f"[{enc} {p} {kind:6s}] all correct x{reps}; moves/person {mv/1e6:.3f} M; peaks "
                      + ", ".join(f"{ph}: {s}+{o}ovf" for ph, (_, s, o) in pk.items())
                      + f"; bands {g['bands']} x {g['band_rows']} rows + control {sum(items.values())} holes in {g['ctrl_rows']} rows"
                      f" -> workspace {g['work_grids']} grids + key {res[0]['keygrids']} = {g['total']} grids (spare rows {g['spare_rows']})", flush=True)
                out[f"{name}_{enc}{p}_{kind}"] = dict(moves=mv, peaks=pk, items=items, grids=g, ops=res[0]['ops'])
    # Demo half-set: slide arithmetic, one target grid
    if "Demo" in tiers:
        print("-" * 78 + "\nDemo 1/2 set: DemoPB slide arithmetic (no overflow), affine walk; target grid = 10 rows x (7 register + 1 slide hole + 2 control holes)")
        worst = 0; mvs = []; fails = 0; tot = 0
        for trial in range(300):
            tot += 1
            try: r = run("Demo", 'three', 1, rnd, 'affine', board=DemoPB)
            except ArithmeticError: fails += 1; continue
            assert all(r['ok']) and r['leaks'] == 0
            worst = max(worst, max(s + o for (_, s, o) in r['peaks'].values())); mvs.append(r['moves'] + r['ctrl'])
        print(f"  validation = trace WALK (n-1 white cells over B, then Frobenius must give the mirror of B)")
        print(f"  {len(mvs)} exchanges correct ({fails} of {tot} key draws hit an exceptional chord and were re-rolled); "
              f"worst peak {worst} live registers, 0 overflow; mean moves/person {sum(mvs)/len(mvs):,.0f}")
        out['Demo_halfset'] = dict(worst_peak=worst, runs=len(mvs), rerolled=fails, mean_moves=sum(mvs) / len(mvs))
        demo_exhaustive(out)
    json.dump(out, open("ecbs_walks%s.json" % ("" if not sys.argv[1:] else "_" + "_".join(tiers)), "w"), indent=1, default=str)

if __name__ == "__main__":
    main()
