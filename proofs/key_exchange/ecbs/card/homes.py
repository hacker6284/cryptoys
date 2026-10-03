"""Fixed-home peg board for the ECBS player's card (scratch).  Reads the drafts' modules in
../core (read-only) for the tier data, PARI reference and key encoding; the board itself is
re-implemented here so that every number lives in a NAMED HOME BAND and every step is the literal
spoken rule of PLAYER_CARD_v2.md.

Move convention = the drafts' (ecbs_pegs / ecbs_physical / ecbs_workbench): place, lift or drop a peg
= 1 move; a jump or a slide = 2 moves per peg; clearing = 1 per peg.  Control-row moves (tallies,
ladder parking, script marker) are counted separately in .ctrl.

Board geometry: the workbench is 3 bands of the lane (destination band on top, 2 overflow bands);
the 7 homes are other bands.  A multiply lifts the SECOND number's pegs (highest first) and lays the
FIRST number from that hole; the fold is the lane fold ("one band up and one hole on, and again r
rows up"), computed geometrically and checked to stay inside the workbench strip."""
import sys, os
sys.dont_write_bytecode = True
ECBS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "core")   # the core evidence modules
if ECBS not in sys.path: sys.path.insert(0, ECBS)
from ecbs_pegs import NEXT, PREV, MIRROR
from ecbs_workbench import LANES

HOMES = ['across', 'up', 'bottom', 'base across', 'base up', 'gap', 'spare']

def npeg(r): return sum(c != '.' for c in r)

class Exceptional(Exception): pass

class Tally:
    """colour-flip tally row: m pegs; each cube turns one white peg red; done when all are red."""
    def __init__(self, hb, name):
        self.hb, self.name, self.row, self.max = hb, name, [], 0
    def start(self):
        self.hb.ctrl += npeg(self.row); self.row = ['W']; self.hb.ctrl += 1; self._m()
    def _m(self):
        self.max = max(self.max, len(self.row))
        both = len(self.hb.inv_tally.row) + len(self.hb.trace_tally.row)
        self.hb.tally_holes_peak = max(self.hb.tally_holes_peak, both)
    def clear(self):
        self.hb.ctrl += len(self.row); self.row = []
    def rebuild(self, rungs):
        """'Rebuild the tally from the ladder: one white peg, then for each rung already climbed,
            double it, and on a red rung add one more.'"""
        self.clear(); self.row = ['W']; self.hb.ctrl += 1; self._m()
        for r in rungs:
            self.double()
            if r == 'R': self.add_one()
    def cubes(self, fn):
        """cube once per tally peg: after each cube turn the next white peg red; stop when all red."""
        assert all(c == 'W' for c in self.row), "tally must be all white before counting"
        for i in range(len(self.row)):
            fn(); self.row[i] = 'R'; self.hb.ctrl += 1
    def whiten(self):                       # drop a red peg on each red peg: red -> one step back = white
        for i, c in enumerate(self.row):
            if c == 'R': self.row[i] = 'W'; self.hb.ctrl += 1
    def double(self):                       # turn it white again and lay as many white pegs again
        self.whiten(); m = len(self.row); self.row += ['W'] * m; self.hb.ctrl += m; self._m()
    def add_one(self):
        self.row.append('W'); self.hb.ctrl += 1; self._m()
    def __len__(self): return len(self.row)

def build_ladder(hb, pegs):
    """'Lay a band's worth of white pegs less ... Pair them off: a leftover peg makes a red rung,
       none a white rung. Throw the leftover away, keep one peg from each pair, repeat until one peg
       is left. Read the rungs from the last one.'  Returns rungs in climbing order."""
    row = pegs; rungs = []; hb.ctrl += pegs
    while row > 1:
        left = row % 2; rungs.append('R' if left else 'W'); hb.ctrl += 1       # lay the rung peg
        hb.ctrl += left + row // 2                                             # throw leftover, lift one of each pair
        row //= 2
    hb.ctrl += row                                                            # clear the last peg
    return rungs[::-1]

class HB:
    def __init__(self, name, n, k, homes=HOMES):
        w, h, r = LANES[name]; assert n == w * h - 1 and n - k == w * r
        self.name, self.n, self.k, self.w, self.h, self.r = name, n, k, w, h, r
        self.home = {x: None for x in homes}
        self.bench = None                       # (target home, strip)
        self.benchlen = 3 * (n + 1)             # three bands of the lane
        self.moves = self.slides = self.ctrl = 0
        self.peak = 0; self.peak_where = None; self.phase = ''; self.peak_strict = 0
        self.max_index = 0                      # highest workbench hole ever holding a peg
        self.ops = {'mul': 0, 'cube': 0, 'inv': 0, 'chord': 0, 'fadd': 0}
        self.line = None; self.line_log = []    # (line label, 'mul'|'cube') for the script-row check
        self.tally_holes_peak = 0
        self.inv_tally = Tally(self, 'inversion'); self.trace_tally = Tally(self, 'trace')
        self.inv_ladder = build_ladder(self, n - 1); self.trace_ladder = build_ladder(self, n)
        self.parked = {'inversion': None, 'trace': None}   # rung parking holes
    # ------------------------------------------------------------------ bookkeeping
    def _occ(self):
        v = sum(1 for x in self.home.values() if x is not None)
        if v > self.peak: self.peak = v; self.peak_where = (self.phase, self.line, [k for k, x in self.home.items() if x is not None])
    def _strict(self, extra=0):
        v = sum(1 for x in self.home.values() if x is not None) + extra
        self.peak_strict = max(self.peak_strict, v)
    def _log(self, kind):
        self.ops[kind] += 1
        if self.line is not None: self.line_log.append((self.line, kind))
    def _need_empty(self, h):
        if self.home[h] is not None: raise AssertionError(f"home clash: {h} already holds a number ({self.phase}, {self.line})")
    def settle(self):
        """slide the finished workbench number to its home ('same hole, other band')."""
        if self.bench is None: return
        t, s = self.bench
        assert all(c == '.' for c in s[self.n:]), "unfolded pegs left on the workbench"
        self._need_empty(t)
        m = 2 * npeg(s[:self.n]); self.moves += m; self.slides += m
        self.home[t] = s[:self.n]; self.bench = None; self._occ()
    def reg(self, h):
        """read a number where it is (home, or the workbench if it is the workbench's target)."""
        r = self.home.get(h)
        if r is not None: return r
        if self.bench is not None and self.bench[0] == h: return self.bench[1]
        raise AssertionError(f"{h} is empty")
    def value(self, h):
        return list(self.reg(h)[:self.n])
    def is_zero(self, h): return all(c == '.' for c in self.reg(h)[:self.n])
    # ------------------------------------------------------------------ single-band rules
    def put(self, h, reg):                      # lay a fresh number from the supply
        self._need_empty(h); self.home[h] = list(reg); self.moves += npeg(reg); self._occ()
    def white0(self, h):                        # one white peg in hole 0 (fresh number if the home is empty)
        if self.home.get(h) is None and not (self.bench and self.bench[0] == h):
            self.put(h, ['W'] + ['.'] * (self.n - 1))
        else: self._drop(self.reg(h), 0, 'W')
    def copy(self, dst, src, mirror=False):
        s = self.reg(src)[:self.n]; self._need_empty(dst)
        self.home[dst] = [MIRROR[c] if mirror else c for c in s]; self.moves += npeg(s); self._occ()
    def move(self, dst, src):                   # slide a whole number to another home
        self.settle(); self._need_empty(dst); r = self.home[src]; self.home[src] = None
        m = 2 * npeg(r); self.moves += m; self.slides += m; self.home[dst] = r; self._occ()
    def clear(self, h):
        if self.bench is not None and self.bench[0] == h and self.home[h] is None:
            s = self.bench[1]; self.moves += npeg(s); self.bench = None; return
        r = self.home[h]; assert r is not None; self.moves += npeg(r); self.home[h] = None
    def mirror(self, h):
        r = self.reg(h)
        for i, c in enumerate(r[:self.n]):
            if c != '.': r[i] = MIRROR[c]; self.moves += 1
    def _drop(self, reg, i, colour, mirror=False):
        if colour == '.': return
        if mirror: colour = MIRROR[colour]
        reg[i] = NEXT[reg[i]] if colour == 'W' else PREV[reg[i]]; self.moves += 1
    def add(self, dst, src, mirror=False):      # drop every peg of src onto the same holes of dst
        s = list(self.reg(src)[:self.n]); d = self.reg(dst)
        for i, c in enumerate(s): self._drop(d, i, c, mirror)
    # ------------------------------------------------------------------ workbench rules
    def _fold(self, strip):
        n, w, h, r = self.n, self.w, self.h, self.r
        top = max([i for i, c in enumerate(strip) if c != '.'], default=0)
        self.max_index = max(self.max_index, top)
        assert top < self.benchlen, "overflow past the workbench"
        for e in range(len(strip) - 1, n - 1, -1):
            c = strip[e]
            if c == '.': continue
            strip[e] = '.'; self.moves += 1
            row, col = divmod(e, w)
            r1, c1 = row - h, col + 1                                   # one band up and one hole on
            if c1 == w: r1, c1 = r1 + 1, 0                              # 'one on' at a row end
            d1 = r1 * w + c1; d2 = (row - r) * w + col                  # and again r rows up
            assert d1 == e - n and d2 == e - (n - self.k) and 0 <= d1 < e and 0 <= d2 < e
            self._drop(strip, d1, c); self._drop(strip, d2, c)
    def mul(self, dst, first, second, copy_second=False, onto=False, mirror=False):
        """dst (+)= first * second: lift the second number's pegs, highest first, and lay the first
           number from that hole (as is for white, mirrored for red; everything mirrored if mirror).
           copy_second: first copy the second number into the spare band and lift from the copy.
           onto: the result is added onto dst's number (dst slides onto the workbench first)."""
        self._log('mul')
        if onto and self.bench is not None and self.bench[0] == dst and self.home[dst] is None:
            strip = self.bench[1]
        else:
            self.settle()
            strip = ['.'] * self.benchlen
            if onto:
                r = self.home[dst]; self.home[dst] = None; m = 2 * npeg(r); self.moves += m; self.slides += m
                strip[:self.n] = r
            self.bench = (dst, strip)
        A = self.home[first]; assert A is not None, f"first number {first} not in its home"
        if copy_second:
            assert second != 'spare'; self.copy('spare', second); src = 'spare'
        else: src = second
        assert src != first, "a square needs a copy"
        self._strict()
        B = self.home[src]; assert B is not None; self.home[src] = None      # lifted: the band empties
        for i in range(self.n - 1, -1, -1):
            c = B[i]
            if c == '.': continue
            self.moves += 1                                                  # lift it
            mir = (c == 'R') != mirror
            for j, d in enumerate(A):
                if d != '.': self._drop(strip, i + j, d, mir)
        self._fold(strip); self._occ()
    def cube(self, dst, src):
        """comb cube: the source's rows are combed into the workbench bands, one peg on every third
           hole (each peg jumps: 2 moves); then fold.  The source band empties."""
        self._log('cube'); self.settle()
        self._strict()
        r = self.home[src]; assert r is not None; self.home[src] = None
        strip = ['.'] * self.benchlen
        for i, c in enumerate(r):
            if c != '.': strip[3 * i] = c; self.moves += 2
        assert 3 * (self.n - 1) + 2 < self.benchlen                          # comb gap fits
        self.bench = (dst, strip); self._fold(strip); self._occ()
    def bench_white0(self): self._drop(self.bench[1], 0, 'W')
    def bench_add(self, src, mirror=False):          # drop a home's pegs onto the workbench number
        for i, c in enumerate(self.home[src]): self._drop(self.bench[1], i, c, mirror)
    def bench_read_and_clear(self):
        t, s = self.bench; v = list(s[:self.n]); self.moves += npeg(v); self.bench = None; return v
    # ------------------------------------------------------------------ rung parking holes
    def park(self, which, rung):
        if self.parked[which] is not None: self.ctrl += 2        # put the previous rung back
        self.parked[which] = rung; self.ctrl += 2                # lift this rung into the parking hole
    def unpark(self, which):
        if self.parked[which] is not None: self.ctrl += 2; self.parked[which] = None

# ====================================================================== spoken procedures
def invert(hb, x):
    """Card: Invert (working number in the gap band, copies in the spare band).
       'Copy the number into the gap band and start the tally with one white peg. Climb the ladder
        from its last rung. At each rung: copy the gap into the spare band and cube the copy once for
        each tally peg; multiply the gap by it (lift the copy) and put the result back in the gap; then
        double the tally. On a red rung, then cube the gap once, multiply the number by it into the gap,
        and add a peg to the tally. (Skip the doubling and the extra peg at the last rung.) At the top,
        cube the gap once more: that is the inverse. The gap times a copy of the number must be one peg
        in hole 0; if it is red, mirror the gap.'"""
    hb.ops['inv'] += 1; T = hb.inv_tally
    hb.copy('gap', x); T.start()
    rungs = hb.inv_ladder
    for idx, rung in enumerate(rungs):
        last = idx == len(rungs) - 1
        hb.park('inversion', rung)
        hb.copy('spare', 'gap')
        T.cubes(lambda: hb.cube('spare', 'spare'))
        hb.mul('gap', 'gap', 'spare'); hb.clear('gap')           # lay the gap, lift the copy; old gap cleared
        if not last: T.double()
        if rung == 'R':
            hb.cube('spare', 'gap')                               # cube the gap once (into spare)
            hb.mul('gap', x, 'spare')                             # the number times it, into the gap
            if not last: T.add_one()
    hb.unpark('inversion')
    hb.cube('gap', 'gap'); hb.settle()                            # the inverse
    T.clear()                                                     # the tally row is free again

def invert_checked(hb, x):
    invert(hb, x)
    # 'The gap times a copy of the number must be one peg in hole 0': build it on the workbench, read, clear.
    hb.mul('(check)', 'gap', x, copy_second=True); v = hb.bench_read_and_clear()
    assert all(c == '.' for c in v[1:]) and v[0] != '.', "inverse check failed"
    if v[0] == 'R': hb.mirror('gap')

def start_walk(hb, red):
    """'At your first non-empty cell, copy the base point into across and up (mirror the up if the
        cell is red), and lay one white peg in hole 0 of the bottom.'"""
    hb.copy('across', 'base across'); hb.copy('up', 'base up', mirror=red); hb.white0('bottom')

def frobenius_point(hb):
    hb.line = 'cubes'
    for h in ('across', 'up', 'bottom'): hb.cube(h, h)
    hb.line = None

def fform_add(hb, red):
    """the six verse lines with homes (card step 9)."""
    hb.ops['fadd'] += 1
    hb.line = 'run'                                   # Run: mirror across; lay base across times a copy of the bottom onto it
    hb.mirror('across'); hb.mul('across', 'base across', 'bottom', copy_second=True, onto=True)
    if hb.is_zero('across'): raise Exceptional("run empty")
    hb.line = 'rise'                                  # Rise: mirror up; lay base up (mirrored on red) times a copy of the bottom onto it
    hb.mirror('up'); hb.mul('up', 'base up', 'bottom', copy_second=True, onto=True, mirror=red)
    hb.line = 'gap'
    hb.mul('gap', 'up', 'up', copy_second=True)       #  up times a copy of up                -> gap
    hb.mul('gap', 'bottom', 'gap')                    #  bottom times the gap (lift the gap)   -> gap
    hb.mul('spare', 'across', 'across', copy_second=True)   # across times a copy of across   -> spare
    hb.mul('bottom', 'spare', 'bottom')               #  spare times the bottom (lift bottom)  -> bottom  ("the kept one")
    hb.mul('gap', 'across', 'spare', onto=True)       #  across times the spare, onto the gap
    hb.add('gap', 'bottom')                           #  drop the bottom onto the gap
    hb.line = 'bottom'
    hb.mul('bottom', 'across', 'bottom')              # Bottom: across times the bottom (lift bottom) -> new bottom
    hb.line = 'new X'
    hb.mul('across', 'gap', 'across')                 # New X: gap times across (lift across)
    hb.mul('across', 'base across', 'bottom', copy_second=True, onto=True)   # plus base across times a copy of the bottom
    hb.line = 'new Y'
    hb.mul('up', 'gap', 'up', mirror=True)                     # New up: the gap times the up (lift the up), laid mirrored
    hb.mul('up', 'base up', 'bottom', copy_second=True, onto=True, mirror=not red)   # plus base up times a copy of the bottom, mirrored
    hb.clear('gap')                                   # clear the gap
    hb.line = None

def walk(hb, cells):
    """cells in reading order; returns True if the accumulator is live (non-empty key)."""
    live = False
    for c in cells:
        if live:
            frobenius_point(hb)
        if c == '.': continue
        if not live: start_walk(hb, c == 'R'); live = True
        else: fform_add(hb, c == 'R')
    return live

def finish(hb):
    """'Invert the bottom. Then gap times across into across, gap times up into up; clear the gap
        and the bottom.'  Leaves the affine point in across / up."""
    invert_checked(hb, 'bottom')
    hb.mul('across', 'gap', 'across'); hb.mul('up', 'gap', 'up')
    hb.settle(); hb.clear('gap'); hb.clear('bottom')

# ---------------------------------------------------------------------- receiver check (homes)
CHECK_HOMES = {'sum across': 'across', 'sum up': 'up', 'run': 'bottom', 'working': 'gap',
               'copy': 'spare', 'their across': 'base across', 'their up': 'base up'}

def on_curve(hb):
    """'Their up times a copy of itself (into the gap); a copy of their across cubed (in the bottom);
        their across times a copy of itself (into the spare), dropped mirrored onto the bottom; a white
        peg in hole 0 of the bottom. Gap and bottom must match.'"""
    hb.mul('gap', 'base up', 'base up', copy_second=True)
    hb.copy('bottom', 'base across'); hb.cube('bottom', 'bottom')
    hb.mul('spare', 'base across', 'base across', copy_second=True)
    hb.settle(); hb.add('bottom', 'spare', mirror=True); hb.clear('spare'); hb.white0('bottom')
    ok = hb.value('gap') == hb.value('bottom')
    hb.clear('gap'); hb.clear('bottom'); return ok

def chord_add(hb, make_run, make_rise):
    """first point in across/up.  make_run lays the run (second x - first x) in the bottom band;
       make_rise lays the rise (second y - first y) in the spare band -- ONLY after the inversion.
       New x = slope squared, plus one, plus the first x, minus the run.
       New y = slope times (first x minus new x), minus the first y."""
    hb.ops['chord'] += 1
    make_run()
    if hb.is_zero('bottom'): raise Exceptional("run empty")
    invert_checked(hb, 'bottom')                                  # inverse of the run -> gap
    make_rise()                                                   # lazy y
    hb.mul('gap', 'gap', 'spare'); hb.clear('gap'); hb.settle()  # slope = gap times the rise (lift the rise)
    hb.mul('bottom', 'gap', 'gap', copy_second=True)              # slope squared, on the workbench
    hb.bench_white0(); hb.bench_add('across'); hb.bench_add('bottom', mirror=True)   # +1, + first x, - run
    hb.clear('bottom'); hb.settle()                               # clear the run; new x -> bottom band
    hb.add('across', 'bottom', mirror=True)                       # first x minus new x, in place
    hb.mirror('up')                                               # minus the first y ...
    hb.mul('up', 'gap', 'across', onto=True)                      # ... plus slope times (first x - new x)
    hb.clear('gap'); hb.settle()
    hb.move('across', 'bottom')                                   # new x slides up to the sum's across

def trace_check(hb, replay=True):
    """card step 12 (fixed wording), homes: sum = across/up, run = bottom, working = gap,
       copy = spare, their point = base across / base up."""
    T = hb.trace_tally
    hb.copy('across', 'base across'); hb.copy('up', 'base up'); T.start()
    rungs = hb.trace_ladder
    try:
        for idx, rung in enumerate(rungs):
            last = idx == len(rungs) - 1
            hb.park('trace', rung)
            if replay and idx > 0: T.rebuild(rungs[:idx])
            def run_d():                               # copy of the sum's across, Frobenius'd tally times, minus the sum's across
                hb.copy('bottom', 'across'); T.cubes(lambda: hb.cube('bottom', 'bottom'))
                if replay: T.clear()                   # free the tally row for the inversion
                else: T.whiten()
                hb.add('bottom', 'across', mirror=True)
            def rise_d():                              # after the inversion: same with the up, into the spare
                if replay: T.rebuild(rungs[:idx])
                hb.copy('spare', 'up'); T.cubes(lambda: hb.cube('spare', 'spare'))
                hb.add('spare', 'up', mirror=True)
            chord_add(hb, run_d, rise_d)
            if rung == 'R' and last:
                hb.cube('across', 'across'); hb.cube('up', 'up'); hb.settle()
                ok = hb.value('across') == hb.value('base across') and hb.value('up') == [MIRROR[c] for c in hb.value('base up')]
                hb.clear('across'); hb.clear('up'); hb.unpark('trace'); T.clear(); return ok
            if replay: T.clear()
            elif not last: T.double()
            if rung == 'R':
                hb.cube('across', 'across'); hb.cube('up', 'up'); hb.settle()     # Frobenius the sum
                def run_r():                           # run: their across minus the sum's across
                    hb.copy('bottom', 'base across'); hb.add('bottom', 'across', mirror=True)
                def rise_r():                          # after the inversion: their up minus the sum's up
                    hb.copy('spare', 'base up'); hb.add('spare', 'up', mirror=True)
                chord_add(hb, run_r, rise_r)
                if not last and not replay: T.add_one()
        raise RuntimeError("ladder ended without the final red rung")
    except Exceptional:
        for h in ('across', 'up', 'bottom', 'gap', 'spare'):
            if hb.home[h] is not None: hb.clear(h)
        if hb.bench is not None: hb.bench_read_and_clear()
        hb.unpark('trace'); T.clear(); return False

# ---------------------------------------------------------------------- base point by rule
def root_strip_literal(hb):
    """rhs in the bottom band.  'Lay the root strip: a band's worth less one hole, red, empty, red,
        empty ... with the last hole white.  Start y (the up band) as one white peg in hole 0.  Square
        the rhs into the spare... For each strip hole from the first: cube y; on red multiply y by the
        rhs squared, on white by the rhs, on empty do nothing.'"""
    n = hb.n; strip = ['R', '.'] * ((n - 3) // 2) + ['R', 'W']; assert len(strip) == n - 1
    hb.mul('gap', 'bottom', 'bottom', copy_second=True); hb.settle()          # rhs squared -> gap
    hb.white0('up')
    for d in strip:
        hb.cube('up', 'up')
        if d == 'R': hb.copy('spare', 'gap'); hb.mul('up', 'up', 'spare')   # y times (a copy of) rhs squared
        elif d == 'W': hb.copy('spare', 'bottom'); hb.mul('up', 'up', 'spare')
        # hb.mul lays y and lifts the copy; the result replaces y
        if d != '.': hb.clear('up'); hb.settle()
    hb.settle(); hb.clear('gap')
    return strip

def base_point(hb):
    """card step 2: 'Put one white peg in hole 1 of the base across.  Rhs = its cube, minus its square,
        plus a white peg in hole 0.  Root it.  If root times root is not the rhs, move the peg one hole
        on and try again.  Then walk the four cells white, red, white, red over it and finish: that is P.'"""
    j = 1
    while True:
        x = ['.'] * hb.n; x[j] = 'W'; hb.put('base across', x)
        hb.copy('bottom', 'base across'); hb.cube('bottom', 'bottom')                # x cubed
        hb.mul('spare', 'base across', 'base across', copy_second=True)               # x squared
        hb.settle(); hb.add('bottom', 'spare', mirror=True); hb.clear('spare'); hb.white0('bottom')
        root_strip_literal(hb)                                                        # y -> up
        hb.mul('gap', 'up', 'up', copy_second=True); hb.settle()
        ok = hb.value('gap') == hb.value('bottom'); hb.clear('gap'); hb.clear('bottom')
        if ok: break
        hb.clear('up'); hb.clear('base across'); j += 1
    hb.move('base up', 'up')
    walk(hb, list('WRWR')); finish(hb)
    hb.clear('base across'); hb.clear('base up')
    hb.move('base across', 'across'); hb.move('base up', 'up')
    return j

# ---------------------------------------------------------------------- option D: the (tau - 1) certificate
def make_certificate(hb):
    """sender, after finishing the walk (C in across/up): 'Copy C into the base bands. Frobenius the
        point in across/up, then add C mirrored-up to it with the chord rule; that is the point you send
        as your key, C is its certificate.'  Leaves A in across/up, C in the base bands."""
    hb.move('base across', 'across'); hb.move('base up', 'up')           # C -> base (P already cleared)
    hb.copy('across', 'base across'); hb.copy('up', 'base up'); hb.cube('across', 'across'); hb.cube('up', 'up'); hb.settle()
    def run_c(): hb.copy('bottom', 'base across'); hb.add('bottom', 'across', mirror=True)
    def rise_c(): hb.copy('spare', 'base up', mirror=True); hb.add('spare', 'up', mirror=True)
    chord_add(hb, run_c, rise_c)                  # tau C + (-C)

def check_certificate(hb, A_sent):
    """receiver, C in the base bands: 'C must be on the curve. Rebuild the key from it exactly as the
        sender did; it must match their key peg for peg.'  A_sent is then copied into the base bands."""
    if not on_curve(hb): return False
    try: make_certificate_from_base(hb)
    except Exceptional:
        for h in ('across', 'up', 'bottom', 'gap', 'spare'):
            if hb.home[h] is not None: hb.clear(h)
        if hb.bench is not None: hb.bench_read_and_clear()
        return False
    ok = hb.value('across') == list(A_sent[0]) and hb.value('up') == list(A_sent[1])
    hb.moves += sum(c != '.' for c in A_sent[0]) + sum(c != '.' for c in A_sent[1])   # compare = read their pegs
    hb.clear('across'); hb.clear('up'); return ok

def make_certificate_from_base(hb):
    hb.copy('across', 'base across'); hb.copy('up', 'base up'); hb.cube('across', 'across'); hb.cube('up', 'up'); hb.settle()
    def run_c(): hb.copy('bottom', 'base across'); hb.add('bottom', 'across', mirror=True)
    def rise_c(): hb.copy('spare', 'base up', mirror=True); hb.add('spare', 'up', mirror=True)
    chord_add(hb, run_c, rise_c)
