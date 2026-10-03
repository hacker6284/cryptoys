"""PLAYER_CARD_v3 board (scratch).  Re-uses the v2 fixed-home board (homes.py, unchanged) for the
number rules, and adds what v3 changes:
  * the CONTROL ROW: the bottom row (row J) of the workspace grids, run on grid to grid, holding from the
    left: script marker (15 holes), phase hole (1), the ladder (one rung per hole), the parking hole, then
    the tally.  Every control peg is a real hole here; overruns and clashes are asserted.
  * one ladder (inversion), one tally; the trace ladder, trace tally and tally rebuild are gone.
  * the root strip lives in the across band during the base point; the white-red-white-red mini key
    lives in the first four key cells.
  * the certificate check (card step 8 + Play steps 14-17), with 'reject if the certificate is empty'.
Move convention as homes.py: place/lift/drop = 1, slide/jump = 2 per peg, clear = 1 per peg.
Calls (the spoken swap and compare) are counted separately in .calls: they move no pegs."""
import sys, os
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H
from homes import npeg, Exceptional
from ecbs_pegs import MIRROR

# row-J holes available in the workspace grids (ecbs_budget.py geometry: Toy 4 grids x 10,
# Hobby 4 double grids x 20, Serious 10 double grids x 20)
CONTROL_ROW = {'Toy': 40, 'Hobby': 80, 'Serious': 200}
SCRIPT, PHASE, CALLING = 15, 1, 1      # script marker, phase hole, 'calling in progress' hole

class EmptyCertificate(Exceptional): pass

class ControlRow:
    def __init__(self, hb, length):
        self.hb = hb; self.row = ['.'] * length; self.length = length
        self.script0, self.phase = 0, SCRIPT
        self.calling = SCRIPT + PHASE
        self.ladder0 = SCRIPT + PHASE + CALLING
        self.nrungs = 0; self.park_hole = None; self.tally0 = None
        self.marker = None; self.marker_max = -1
        self.parked_from = None; self.tally_len = 0; self.tally_max = 0; self.max_hole = -1
    def _set(self, i, c):
        assert 0 <= i < self.length, f"control row overrun at hole {i} of {self.length}"
        self.row[i] = c; self.max_hole = max(self.max_hole, i)
    # ---- ladder
    def lay_rung(self, colour):
        i = self.ladder0 + self.nrungs; assert self.row[i] == '.'; self._set(i, colour); self.nrungs += 1
        self.hb.ctrl += 1
    def ladder_done(self):
        self.park_hole = self.ladder0 + self.nrungs; self.tally0 = self.park_hole + 1
    def rung_holes_climb(self):          # climb from the last rung made (rightmost, next to the parking hole)
        return list(range(self.ladder0 + self.nrungs - 1, self.ladder0 - 1, -1))
    def park(self, hole):
        self.unpark()
        assert self.row[hole] in 'WR' and self.row[self.park_hole] == '.'
        self._set(self.park_hole, self.row[hole]); self.row[hole] = '.'; self.parked_from = hole; self.hb.ctrl += 2
        return self.row[self.park_hole]
    def unpark(self):
        if self.parked_from is None: return
        self._set(self.parked_from, self.row[self.park_hole]); self.row[self.park_hole] = '.'
        self.parked_from = None; self.hb.ctrl += 2
    # ---- script marker
    def marker_step(self):
        self.marker = 0 if self.marker is None else self.marker + 1
        assert self.marker < SCRIPT, "script marker ran past its 15 holes"
        self.marker_max = max(self.marker_max, self.marker); self.hb.ctrl += 1 if self.marker == 0 else 2
    def marker_lift(self):
        if self.marker is not None: self.marker = None; self.hb.ctrl += 1
    # ---- phase hole: drop a white peg (empty -> white -> red)
    def phase_drop(self):
        c = self.row[self.phase]; self._set(self.phase, {'.': 'W', 'W': 'R', 'R': '.'}[c]); self.hb.ctrl += 1
    def phase_clear(self):
        if self.row[self.phase] != '.': self.row[self.phase] = '.'; self.hb.ctrl += 1

class Tally3:
    """the colour-flip tally, laid in the control row after the parking hole."""
    def __init__(self, hb): self.hb = hb; self.cr = hb.cr
    @property
    def row(self): return self.cr.row[self.cr.tally0:self.cr.tally0 + self.cr.tally_len]
    def _put(self, j, c): self.cr._set(self.cr.tally0 + j, c)
    def start(self):
        assert self.cr.tally_len == 0, "a second tally would be needed"
        self._put(0, 'W'); self.cr.tally_len = 1; self.hb.ctrl += 1; self._m()
    def _m(self):
        self.cr.tally_max = max(self.cr.tally_max, self.cr.tally_len)
        self.hb.tally_holes_peak = max(self.hb.tally_holes_peak, self.cr.tally_len)
    def cubes(self, fn):
        assert all(self.cr.row[self.cr.tally0 + j] == 'W' for j in range(self.cr.tally_len))
        for j in range(self.cr.tally_len):
            fn(); self._put(j, 'R'); self.hb.ctrl += 1
    def double(self):
        m = self.cr.tally_len
        for j in range(m):                                   # drop a red peg on each red: back to white
            if self.cr.row[self.cr.tally0 + j] == 'R': self._put(j, 'W'); self.hb.ctrl += 1
        for j in range(m, 2 * m): assert self.cr.row[self.cr.tally0 + j] == '.'; self._put(j, 'W'); self.hb.ctrl += 1
        self.cr.tally_len = 2 * m; self._m()
    def add_one(self):
        j = self.cr.tally_len; assert self.cr.row[self.cr.tally0 + j] == '.'
        self._put(j, 'W'); self.cr.tally_len += 1; self.hb.ctrl += 1; self._m()
    def clear(self):
        for j in range(self.cr.tally_len): self._put(j, '.'); self.hb.ctrl += 1
        self.cr.tally_len = 0
    def __len__(self): return self.cr.tally_len

class HB3(H.HB):
    def __init__(self, name, n, k, extra_homes=()):
        super().__init__(name, n, k, homes=H.HOMES + list(extra_homes))
        self.ctrl = 0; self.calls = 0; self.ladder_moves = 0
        self.cr = ControlRow(self, CONTROL_ROW[name])
        self.inv_tally = Tally3(self); self.trace_tally = None; self.trace_ladder = None
        self.marker_on = False; self.key_grid_moves = 0; self.tally_holes_peak = 0
        self.cursor = None; self.call_log = []; self.cursor_steps = 0; self.stale_cleared = 0
        self.inv_ladder = self.build_ladder()
    def build_ladder(self):
        """Card 5: 'lay a number's worth of pegs less one in the spare, and pair them off. A leftover
        makes a red rung and none a white one. Throw the leftover away, keep one of each pair, and repeat
        down to one peg.'  Rungs go into the control row left to right as they are made."""
        m0 = self.moves; c = self.n - 1
        row = ['W'] * c + ['.'] * (self.n - c); self.put('spare', row)
        while c > 1:
            left = c % 2; self.cr.lay_rung('R' if left else 'W')
            self.moves += left + (c // 2)          # throw the leftover away; lift one peg of each pair
            c //= 2
        self.clear('spare'); self.cr.ladder_done()
        self.ladder_moves = self.moves - m0; self.moves = m0      # once per kit, reported separately
        climb = self.cr.rung_holes_climb()
        return [self.cr.row[h] for h in climb]
    # the inversion's 'park' hooks: homes.invert calls park('inversion', rung) per rung, unpark at the end
    def park(self, which, rung):
        idx = getattr(self, '_rung_idx', 0); holes = self.cr.rung_holes_climb()
        got = self.cr.park(holes[idx]); assert got == rung, "parked rung disagrees with the ladder"
        self._rung_idx = idx + 1
    def unpark(self, which):
        self.cr.unpark(); self._rung_idx = 0
    def _log(self, kind):
        super()._log(kind)
        if self.marker_on: self.cr.marker_step()

# ============================================================== v3 spoken procedures
def walk3(hb, cells):
    """Card 11-12 with the script marker: lift it at each new cell; one hole on after every cube or multiply."""
    live = False; hb.marker_on = True
    for c in cells:
        hb.cr.marker_lift()
        if live: H.frobenius_point(hb)
        if c == '.': continue
        if not live: H.start_walk(hb, c == 'R'); live = True
        else: H.fform_add(hb, c == 'R')
    hb.cr.marker_lift(); hb.marker_on = False
    return live

def curve_side(hb, src, dst):
    """'a copy of it cubed, take away it times a copy of itself, and drop a white peg in hole 0' -> dst."""
    hb.copy(dst, src); hb.cube(dst, dst)
    hb.mul('spare', src, src, copy_second=True)
    hb.settle(); hb.add(dst, 'spare', mirror=True); hb.clear('spare'); hb.white0(dst)

def base_point3(hb):
    """Card 9.  The root strip is laid in the across; the mini key white-red-white-red in the first
    four key cells."""
    j = 1
    while True:
        x = ['.'] * hb.n; x[j] = 'W'; hb.put('base across', x)
        curve_side(hb, 'base across', 'bottom')
        hb.mul('gap', 'bottom', 'bottom', copy_second=True); hb.settle()
        hb.white0('up')
        strip = ['R', '.'] * ((hb.n - 3) // 2) + ['R', 'W']; assert len(strip) == hb.n - 1
        hb.put('across', strip + ['.'])                       # the strip, in the across band
        hb.marker_on = True
        for d in strip:                                       # a cursor ship on the strip hole (no moves counted)
            hb.cr.marker_lift(); hb.line = 'root'
            hb.cube('up', 'up')
            if d != '.':
                hb.copy('spare', 'gap' if d == 'R' else 'bottom'); hb.mul('up', 'up', 'spare'); hb.clear('up')
            hb.settle()
        hb.cr.marker_lift(); hb.marker_on = False; hb.line = None
        hb.clear('gap')
        hb.mul('gap', 'up', 'up', copy_second=True); hb.settle()
        ok = hb.value('gap') == hb.value('bottom')
        if ok: break
        for h in ('gap', 'bottom', 'up', 'across', 'base across'): hb.clear(h)
        j += 1
    hb.clear('gap'); hb.clear('bottom'); hb.clear('across')
    hb.move('base up', 'up')
    hb.key_grid_moves += 4                                    # lay W R W R in the first four key cells
    walk3(hb, list('WRWR'))
    hb.key_grid_moves += 4                                    # clear them
    H.finish(hb)
    hb.clear('base across'); hb.clear('base up')
    hb.move('base across', 'across'); hb.move('base up', 'up')
    return j

def certificate(hb, X, Y):
    """Card 8, on the point in bands X (across) and Y (up):
    'Copy its across into the bottom, cube it, mirror it and add its across. If the bottom is empty, the
     certificate is empty. Invert the bottom. Copy its up into the spare, cube it, add its up and mirror
     it. Do the gap times the spare, into the gap, and Frobenius the point. Do the gap times a copy of
     itself, drop a white peg in hole 0, add its across, take away the bottom, and put it into the
     bottom. Take the bottom away from its across. Mirror its up and lay the gap times its across onto
     it. Clear the gap and slide the bottom into its across.'"""
    hb.ops['chord'] += 1
    hb.copy('bottom', X); hb.cube('bottom', 'bottom'); hb.settle(); hb.mirror('bottom'); hb.add('bottom', X)
    if hb.is_zero('bottom'):
        hb.clear('bottom'); raise EmptyCertificate("run empty: pi(C) = C")
    H.invert_checked(hb, 'bottom')                            # 1/run -> gap
    hb.copy('spare', Y); hb.cube('spare', 'spare'); hb.settle(); hb.add('spare', Y); hb.mirror('spare')
    hb.mul('gap', 'gap', 'spare'); hb.clear('gap'); hb.settle()          # slope -> gap
    hb.cube(X, X); hb.cube(Y, Y); hb.settle()                            # Frobenius the point
    hb.mul('bottom', 'gap', 'gap', copy_second=True)
    hb.bench_white0(); hb.bench_add(X); hb.bench_add('bottom', mirror=True)
    hb.clear('bottom'); hb.settle()                                      # new across -> bottom
    hb.add(X, 'bottom', mirror=True)                                     # first across minus new across
    hb.mirror(Y); hb.mul(Y, 'gap', X, onto=True)                         # lifts X
    hb.clear('gap'); hb.settle(); hb.move(X, 'bottom')

ANSWER = {'R': 'hit', 'W': 'miss', '.': 'misfire'}
HEAR = {v: k for k, v in ANSWER.items()}

# ---------------------------------------------------------------- board geometry for spoken coordinates
# Grids are numbered from the workbench's first grid on (ecbs_budget.py layout); homes fill the register
# grids after the workbench in the card's order; row J of every workspace grid is the control row.
GEOM = {'Toy':     dict(w=8,  rows=3, per=3, first=2, double=False, work=4,  key=[5]),
        'Hobby':   dict(w=20, rows=3, per=3, first=3, double=True,  work=8,  key=[9]),
        'Serious': dict(w=20, rows=9, per=1, first=7, double=True,  work=20, key=[21, 22])}

def coord(name, home, i):
    """hole i of a home band -> (grid, 'B7').  Hole 0 is the band's first hole in reading order."""
    g = GEOM[name]; h = H.HOMES.index(home); w = g['w']
    unit, band = divmod(h, g['per'])
    r, c = divmod(i, w); row = band * g['rows'] + r
    if g['double']:
        grid = g['first'] + 2 * unit + (c >= 10); col = c % 10 + 1
    else:
        grid = g['first'] + unit; col = c + 1
    return grid, 'ABCDEFGHIJ'[row] + str(col)

def coord_inverse(name):
    m = {}
    for home in H.HOMES:
        n = {'Toy': 23, 'Hobby': 59, 'Serious': 179}[name]
        for i in range(n): m[coord(name, home, i)] = (home, i)
    return m

PLANS = {'C': [('base across', 'across'), ('base up', 'up')],      # their C: called before any certificate
         'A': [('bottom', 'across'), ('gap', 'up')]}               # their A: called once your phase peg is red

def plan_for(hb):
    ph = hb.cr.row[hb.cr.phase]
    return PLANS['C'] if ph == '.' else PLANS['A'] if ph == 'R' else None

def start_calling(hb):
    """'Stand a peg in the calling hole and put the cursor ships on hole 0 of the first home named.'"""
    assert hb.cursor is None and hb.cr.row[hb.cr.calling] == '.', "calling already in progress"
    plan = plan_for(hb); assert plan is not None, "nothing to call in this phase"
    for dst, _ in plan:                                          # 'clear the homes named' first
        if hb.home[dst] is not None:
            hb.stale_cleared += npeg(hb.home[dst]); hb.clear(dst)
        assert hb.home[dst] is None, "receiving home not empty when calling starts"
    hb.cr._set(hb.cr.calling, 'W'); hb.ctrl += 1
    hb.cursor = (plan[0][0], 0); hb.ctrl += 1; hb.cursor_steps += 1

def call_step(hb, sender):
    """One call, driven only by what is on the receiver's board (phase hole, calling hole, cursor):
    'Call the matching hole of their band aloud by grid and
     coordinate; they answer from the peg: red hits, white misses, empty misfires.  Lay the answer in the
     cursor hole.  Move the cursor ships to the next hole to call; after the last, park them off the board
     and lift the calling peg.'"""
    assert hb.cr.row[hb.cr.calling] == 'W' and hb.cursor is not None
    plan = plan_for(hb); dst, i = hb.cursor; src = dict(plan)[dst]
    if i == 0:                                                   # cleared at the start of calling
        assert hb.home[dst] is None, "receiving home not empty when its calling starts"
        hb.home[dst] = ['.'] * hb.n; hb._occ()                   # the (empty) band is now the receiving home
    rec = hb.home[dst]
    assert all(c == '.' for c in rec[i:]), "a hole at or after the cursor already holds a peg"
    g, cell = coord(hb.name, src, i)
    assert cell[0] != 'J' and g <= GEOM[hb.name]['work'] and g not in GEOM[hb.name]['key']
    peg = sender.home[src][i]                                    # the sender looks and answers
    heard = HEAR[ANSWER[peg]]
    if heard != '.': rec[i] = heard; hb.moves += 1               # a red peg on a hit, white on a miss
    hb.calls += 1; hb.call_log.append((dst, src, i, g, cell))
    order = [d for d, _ in plan]
    if i + 1 < hb.n: hb.cursor = (dst, i + 1)
    elif order.index(dst) + 1 < len(order): hb.cursor = (order[order.index(dst) + 1], 0)
    else:
        hb.cursor = None; hb.cr._set(hb.cr.calling, '.'); hb.ctrl += 1   # park off the board; lift the peg
    hb.ctrl += 1; hb.cursor_steps += 1

def call_session(hb, sender, rnd=None, letgo=3):
    """Call every published band of the current plan.  At `letgo` random points the player lets go; the
    session then resumes from the board alone, and the board is checked to say exactly where it stood."""
    plan = plan_for(hb); before = {s: list(sender.home[s]) for _, s in plan}
    start_calling(hb)
    total = len(plan) * hb.n
    stops = set(rnd.sample(range(total), min(letgo, total))) if rnd else set()
    k = 0; resumes = 0
    while hb.cr.row[hb.cr.calling] == 'W':
        if k in stops:                                           # let go here: check the board says it all
            dst, i = hb.cursor; src = dict(plan_for(hb))[dst]; resumes += 1
            if hb.home[dst] is not None:
                assert hb.home[dst][:i] == sender.home[src][:i] and all(c == '.' for c in hb.home[dst][i:])
        call_step(hb, sender); k += 1
    assert k == total, "not every hole was called"
    for d, s in plan:
        assert hb.home[d] == sender.home[s], "copy differs from the published band"
        assert sender.home[s] == before[s], "sender's published band changed during the calls"
    return resumes

def receive_certificate(hb):
    """'The bottom must match the base across and the gap the base up, peg for peg; otherwise reject.'"""
    return hb.value('bottom') == hb.value('base across') and hb.value('gap') == hb.value('base up')
