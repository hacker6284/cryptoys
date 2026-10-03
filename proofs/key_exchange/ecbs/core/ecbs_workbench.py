#!/usr/bin/env python3
"""Independent re-verification of Toymaster's lane layout + workbench (TOYMASTER_IDEAS.md F1, F2, C1, W1,
H1, D1) with Crypto's own harness (ecbs_pegs / ecbs_physical, checked against PARI).

Lane layout: lane width w, band height h, n = w*h - 1 ("a band less its last hole"); tap with n - k = w*r.
  Fold (strip in reading order down the lane): from the far end, lift each peg beyond the register and
  drop it "h rows up and one hole on" and "r rows up".
  Comb cube: source row rr (w holes) goes to strip band rr (3 rows), a peg on every third hole.
Workbench: every multiply / cube is built on one fixed 3-band area (destination + 2 overflow bands),
  and the finished result slides to a free register band ("same hole, other band").  An accumulate
  destination slides onto the workbench first.  Bands needed = live registers not on the workbench.
W1: walk cursor kept on the ship grid (marker peg in a water hole / sign peg in the parking hole)."""
import sys, random, json
from ecbs_pegs import Board
from ecbs_ref import TIERS
import ecbs_keys as K
import ecbs_walks as WK
from ecbs_walks import APB, DemoPB

LANES = {"Demo": (2, 4, 1), "Toy": (8, 3, 1), "Hobby": (20, 3, 1), "Serious": (20, 9, 6)}   # w, h, r

def lane_fold(strip, n, w, h, r):
    s = strip[:]; B = Board(n, 0); moves = 0
    for e in range(len(s) - 1, n - 1, -1):
        c = s[e]
        if c == '.': continue
        s[e] = '.'; moves += 1
        row, col = divmod(e, w)
        r1, c1 = row - h, col + 1
        if c1 == w: r1, c1 = r1 + 1, 0                        # "one on" at a row end = next row's first hole
        d1 = r1 * w + c1; d2 = (row - r) * w + col
        B.drop(s, d1, c); B.drop(s, d2, c)
    return s[:n], moves + B.moves

def comb(reg, n, w):
    rows = -(-n // w); strip = ['.'] * (3 * rows * w + 2); clash = 0
    for rr in range(rows):
        for c in range(w):
            i = rr * w + c
            if i < n and reg[i] != '.':
                band_row, band_col = divmod(3 * c, w)            # every third hole, carrying on across row ends
                strip[(3 * rr + band_row) * w + band_col] = reg[i]
        g = 3 * rr * w + 1                                          # patrol boat parks on holes g, g+1 of the band
        if strip[g] != '.' or strip[g + 1] != '.': clash += 1
    return strip, clash

def verify_geometry(rnd):
    out = {}
    for name, (n, k, _) in TIERS.items():
        w, h, r = LANES[name]
        assert n == w * h - 1 and n - k == w * r, (name, n, k, w, h, r)
        Bd = Board(n, k); okf = okc = clash = 0; cap = 3 * w * h
        for _ in range(300):
            a = [rnd.choice('.WR') for _ in range(n)]; b = [rnd.choice('.WR') for _ in range(n)]
            strip = ['.'] * (2 * n - 1)
            for i, c in enumerate(b):
                if c != '.': Bd.add_into(strip, a, offset=i, mirror=(c == 'R'))
            okf += lane_fold(strip, n, w, h, r)[0] == Bd.fold(strip[:])
            st, cl = comb(a, n, w); clash += cl
            okc += lane_fold(st[:3 * n - 2] if all(x == '.' for x in st[3 * n - 2:]) else st, n, w, h, r)[0] == Bd.cube(a[:])
        need = 3 * n - 2 + 2
        out[name] = dict(w=w, h=h, r=r, k=k, fold_ok=okf, comb_ok=okc, clash=clash, strip_need=need, workbench=cap)
        print(f"  {name}: x^{n} = x^{k} + 1, lane {w} wide, band {h} rows less its last hole, tap {r} row(s) up: "
              f"fold {okf}/300, comb cube {okc}/300 equal Board (PARI-checked); patrol-boat clashes {clash}; "
              f"cube strip + comb gap {need} <= workbench {cap}: {need <= cap}")
    return out

class WB(APB):
    """workbench accounting on top of PB.  At most one register sits on the workbench: the destination of
       the op in progress, or (between ops) the newest register -- a fresh result or a fresh copy/empty
       register -- until another op needs the workbench, when it slides to a free band ("same hole, other
       band", 2 moves per peg).  An existing register used as an accumulate destination slides onto the
       workbench first.  Bands needed = live registers not on the workbench."""
    def __init__(self, n, k):
        super().__init__(n, k); self.depth = 0; self.bands = {}; self.slide_moves = 0; self.bench = None; self.fresh = {}
    def _note(self):
        super()._note()
        live = [i for i in self.alive if not (i in self.fresh and all(c == '.' for c in self.fresh[i]))]
        v = len(live) - (1 if (self.bench is not None and self.bench in live) else 0)
        if v > self.bands.get(self.phase, 0): self.bands[self.phase] = v
    def _slide(self, r):
        m = 2 * sum(c != '.' for c in r); self.slide_moves += m; self.moves += m
    def reg(self, r):
        if self.depth == 0 and (self.bench is None or self.bench not in self.alive):
            self.bench = id(r); self._bench_reg = r
        return super().reg(r)
    def _claim(self, dst, dst_live):
        """the workbench is needed for dst.  If dst holds pegs in a band and something else is on the
           workbench, the two SWAP hole by hole (lift both pegs of a hole, place each in the other's place);
           otherwise the old occupant slides off / dst slides on.  An empty fresh dst never needs a band."""
        old = self._bench_reg if (self.bench is not None and self.bench in self.alive and self.bench != id(dst)) else None
        if old is not None: self._slide(old)
        if self.bench != id(dst) and dst_live: self._slide(dst)
        self.fresh.pop(id(dst), None); self.bench = id(dst); self._bench_reg = dst
    def zero(self):
        r = ['.'] * self.n
        if self.depth == 0 and (self.bench is None or self.bench not in self.alive):
            self._bench_reg = r
        if self.depth == 0: self.fresh[id(r)] = r          # an empty register made for the next op's result
        return self.reg(r)
    def new_copy(self, a, mirror=False):
        r = super().new_copy(a, mirror)
        self.fresh.pop(id(r), None); self._note()
        if self.bench == id(r): self._bench_reg = r
        return r
    def mac(self, dst, a, b, keep_b=False, negate=False):
        self._claim(dst, id(dst) in self.alive and any(c != '.' for c in dst))
        self.depth += 1
        try: t = super().mac(dst, a, b, keep_b, negate)
        finally: self.depth -= 1
        self.bench = id(dst); self._bench_reg = dst; self._note(); return t
    def mul_new(self, a, b, keep_b=False):
        d = ['.'] * self.n; self._claim(d, False)
        self.depth += 1
        try: super().reg(d); t = PB_mac(self, d, a, b, keep_b)
        finally: self.depth -= 1
        self.bench = id(d); self._bench_reg = d; self._note(); return d, t
    def sq_new(self, a):
        c = self.new_copy(a); d, _ = self.mul_new(a, c); return d
    def cube_new(self, a):
        d = ['.'] * self.n; self._claim(d, False)
        self.depth += 1
        try:
            super().reg(d); d2 = PB_cube_body(self, a, d)
        finally: self.depth -= 1
        self.bench = id(d); self._bench_reg = d; self._note(); return d
from ecbs_physical import PB
PB_mac = PB.mac
def PB_cube_body(self, a, d):
    """PB.cube_new with the destination supplied (same moves)"""
    self.op('cube'); n = self.n
    self.ovf = 2; self._note()
    strip = ['.'] * (3 * n - 2)
    for i in range(n - 1, -1, -1):
        if a[i] != '.': strip[3 * i] = a[i]; a[i] = '.'; self.moves += 2
    self.alive.discard(id(a))
    d[:] = self.fold(strip); self.ovf = 0
    return d
class WBT(WB):
    trace_walk_check = DemoPB.trace_walk_check
    trace_check = DemoPB.trace_walk_check

def w1_cursor(rnd, trials=300):
    """three-state fleet keys; sign pegs live in ship holes.  Walk every cell in reading order; at each
       hands-off moment exactly one cursor must be visible; digits read must equal the key."""
    ok = amb = restored = 0
    for t in range(trials):
        G = rnd.choice([1, 2, 6]); grids = K.three_state(rnd, G)
        ship_hole = [{c: g[c] for c in range(100) if g[c] != '.'} for g in grids]     # sign pegs in ships
        grid_hole = [set() for _ in grids]; parking = None; read = []
        for gi, g in enumerate(grids):
            for c in range(100):
                if c in ship_hole[gi]: parking = ship_hole[gi].pop(c); read.append(parking)
                else: grid_hole[gi].add(c); read.append('.')
                # hands off: count cursors
                cur = sum(len(s) for s in grid_hole) + sum(1 for gj, g2 in enumerate(grids) for cc in range(100)
                                                            if g2[cc] != '.' and cc not in ship_hole[gj])
                amb += cur != 1
                if parking is not None: ship_hole[gi][c] = parking; parking = None
                else: grid_hole[gi].discard(c)
        ok += read == [x for g in grids for x in g]
        restored += all(ship_hole[gi] == {c: g[c] for c in range(100) if g[c] != '.'} for gi, g in enumerate(grids))
    return dict(trials=trials, digits_ok=ok, ambiguous_moments=amb, restored=restored)

def main():
    rnd = random.Random(5150); out = {}
    print("== A. Lane fold + comb cube (Toymaster F1/F2/C1), re-implemented here")
    out['geometry'] = verify_geometry(rnd)
    print("\n== B. W1 ship-grid cursor")
    out['w1'] = w1_cursor(rnd); print("  ", out['w1'])
    print("\n== C. Workbench schedule: register bands needed (live registers NOT on the workbench), per phase")
    plan = {"Demo": [('three', 1, 'affine', WB), ('three', 1, 'affine', WBT), ('three', 1, 'proj', WB)],
            "Toy": [('three', 1, 'proj', WB), ('pegs', 19, 'proj', WB), ('three', 1, 'affine', WB)],
            "Hobby": [('three', 2, 'proj', WB), ('pegs', 55, 'proj', WB), ('six', 1, 'proj', WB)],
            "Serious": [('three', 6, 'proj', WB), ('three', 7, 'proj', WB), ('pegs', 175, 'proj', WB), ('pegs', 200, 'proj', WB), ('six', 2, 'proj', WB)]}
    for name in sys.argv[1:] or plan:
        for enc, p, kind, cls in plan[name]:
            reps = 20 if name == 'Demo' else (3 if name != 'Serious' else 1)
            got = []; rer = 0
            while len(got) < reps:
                try: r = WK.run(name, enc, p, rnd, kind, board=cls)
                except ArithmeticError: rer += 1; continue
                assert all(r['ok']) and r['leaks'] == 0, r
                got.append(r)
            # re-run one to read the band counts (run() does not return the board)
            bands = {}
            for _ in range(reps):
                while True:
                    try:
                        T = None
                        B = [None]
                        def mk(n, k, _c=cls): B[0] = _c(n, k); return B[0]
                        r = WK.run(name, enc, p, rnd, kind, board=mk); break
                    except ArithmeticError: continue
                for ph, v in B[0].bands.items(): bands[ph] = max(bands.get(ph, 0), v)
                slide = B[0].slide_moves
            mv = sum(x['moves'] + x['ctrl'] for x in got) / reps
            label = f"{enc} {p} {kind}{' +trace-walk' if cls is WBT else ''}"
            print(f"  {name:7s} [{label:24s}] correct x{reps} (+{rer} re-rolls); bands needed: "
                  + ", ".join(f"{ph} {v}" for ph, v in bands.items()) + f"; moves/person {mv/1e6:.3f} M incl. slides "
                  f"(slides in last run {slide/1e6:.3f} M); tally max {max(x['tally_max'] for x in got)}", flush=True)
            out[f"{name}_{label}"] = dict(bands=bands, moves=mv, slide_last=slide, rerolls=rer, tally=max(x['tally_max'] for x in got))
    json.dump(out, open("ecbs_workbench.json" if not sys.argv[1:] else f"ecbs_workbench_{'_'.join(sys.argv[1:])}.json", "w"), indent=1, default=str)

if __name__ == "__main__":
    main()

class WBnoswap(WB):
    """same schedule, but WITHOUT the swap move: the old workbench occupant must slide to a free band
       before an accumulate target (holding pegs, in a band) slides onto the workbench."""
    def _claim(self, dst, dst_live):
        old = self._bench_reg if (self.bench is not None and self.bench in self.alive and self.bench != id(dst)) else None
        if old is not None and dst_live and self.bench != id(dst):
            self._slide(old); self.bench = None; self._note()          # both now in bands for a moment
        super()._claim(dst, dst_live)

def noswap_main():
    rnd = random.Random(6060)
    for name, enc, p in (("Demo", 'three', 1), ("Toy", 'three', 1), ("Hobby", 'three', 2)):
        B = [None]
        def mk(n, k): B[0] = WBnoswap(n, k); return B[0]
        while True:
            try: r = WK.run(name, enc, p, rnd, 'proj', board=mk); break
            except ArithmeticError: continue
        assert all(r['ok'])
        print(f"  NO SWAP {name} [{enc} {p} proj]: bands needed " + ", ".join(f"{ph} {v}" for ph, v in B[0].bands.items()))
