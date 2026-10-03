"""Demo board (n = 7, the 1/2 set) for the certificate card.  Evidence harness, not a reference.
Re-uses the card harness (../card/homes.py, ../card/homes_v3.py) unchanged and changes only what Demo
changes (CARD.md, "Demo"):
  * board: one target grid in five 2-wide lanes.  Lane 1 (columns 1-2, all 10 rows = 20 holes) is the
    workbench; a number is 4 rows of a lane less its last hole (7 holes).  The 7 homes are the 4-row slots
    of lanes 2-5, rows A-D first (across, up, bottom, base across), then rows E-H (base up, gap, spare);
    lanes 5 rows E-H is free.  Key: 2 cells of the ocean grid (WRWR uses its first 4).
  * control row: rows I and J of lanes 2-5 (columns 3-10), run on: row I then row J = 16 holes.
    Script marker (SCRIPT_DEMO holes), phase hole, calling hole, ladder, parking hole, tally.
  * the cube: a Demo row is 2 holes, so a finger keeps the place; no comb gap and no cursor ship
    (the 19-hole cube strip fits the 20-hole workbench).
  * the walk: the CHORD RULE (affine), same words as the certificate's chord: Frobenius = cube the
    across and the up; no bottom, no finish.  The script marker moves one hole per cube or multiply of
    the walk and stands still during the inversion (the parked rung and the tally hold that place).
Move convention as homes.py.  Every assertion of homes.py / homes_v3.py still runs."""
import sys, os
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'card'))
import homes as H, homes_v3 as V
from homes import npeg, Exceptional

DEMO_CONTROL = 16          # rows I-J of lanes 2-5
DEMO_BENCH = 20            # lane 1: 10 rows x 2
SCRIPT_DEMO = int(os.environ.get('ECBS_DEMO_SCRIPT', '5'))   # script holes; 5 = measured need (see card_sim_demo)

class ControlRowDemo(V.ControlRow):
    def __init__(self, hb, length, script):
        super().__init__(hb, length)
        self.script = script
        self.script0, self.phase = 0, script
        self.calling = script + V.PHASE
        self.ladder0 = script + V.PHASE + V.CALLING
    def marker_step(self):
        self.marker = 0 if self.marker is None else self.marker + 1
        assert self.marker < self.script, f"script marker ran past its {self.script} holes"
        self.marker_max = max(self.marker_max, self.marker); self.hb.ctrl += 1 if self.marker == 0 else 2

class HBDemo(V.HB3):
    def __init__(self, name='Demo', n=7, k=5, extra_homes=(), script=None):
        script = SCRIPT_DEMO if script is None else script
        V.CONTROL_ROW.setdefault('Demo', DEMO_CONTROL)
        self._script = script
        super().__init__(name, n, k, extra_homes)
        self.inv_tally.cr = self.cr          # Tally3 bound the row before build_ladder swapped it in
        assert isinstance(self.cr, ControlRowDemo)
        self.benchlen = DEMO_BENCH
    def build_ladder(self):
        # swap in the Demo control row before the ladder is laid (HB3.__init__ calls this once)
        self.cr = ControlRowDemo(self, DEMO_CONTROL, self._script)
        return super().build_ladder()
    def cube(self, dst, src):
        """comb cube on the 20-hole Demo workbench: no comb gap (a finger holds the 2-hole row)."""
        self._log('cube'); self.settle(); self._strict()
        r = self.home[src]; assert r is not None; self.home[src] = None
        strip = ['.'] * self.benchlen
        for i, c in enumerate(r):
            if c != '.': strip[3 * i] = c; self.moves += 2
        assert 3 * (self.n - 1) < self.benchlen                 # the 19-hole cube strip fits
        self.bench = (dst, strip); self._fold(strip); self._occ()

# ---------------------------------------------------------------- Demo chord walk (CARD.md, Demo 11-12)
def chord_add_demo(hb, red):
    """'Add the base point by the chord rule (the base up mirrored throughout for red):
       Run: copy the base across into the bottom and take the across away. Empty? Reroll your key.
       Invert the bottom.  Rise: copy the base up into the spare and take the up away.
       Then as the certificate: the gap times the spare, into the gap.  The gap times a copy of itself,
       drop a white peg in hole 0, add the across, take away the bottom, and put it into the bottom.
       Take the bottom away from the across.  Mirror the up and lay the gap times the across onto it.
       Clear the gap and slide the bottom into the across.'"""
    hb.ops['chord'] += 1
    hb.copy('bottom', 'base across'); hb.add('bottom', 'across', mirror=True)          # run
    if hb.is_zero('bottom'): raise Exceptional("run empty")
    on = hb.marker_on; hb.marker_on = False                                               # marker holds still
    H.invert_checked(hb, 'bottom')                                                        # 1/run -> gap
    hb.marker_on = on
    hb.copy('spare', 'base up', mirror=red); hb.add('spare', 'up', mirror=True)          # rise (lazy y)
    hb.mul('gap', 'gap', 'spare'); hb.clear('gap'); hb.settle()                          # slope
    hb.mul('bottom', 'gap', 'gap', copy_second=True)
    hb.bench_white0(); hb.bench_add('across'); hb.bench_add('bottom', mirror=True)
    hb.clear('bottom'); hb.settle()                                                       # new across -> bottom
    hb.add('across', 'bottom', mirror=True)
    hb.mirror('up'); hb.mul('up', 'gap', 'across', onto=True)
    hb.clear('gap'); hb.settle(); hb.move('across', 'bottom')

def frobenius_affine(hb):
    hb.line = 'cubes'
    for h in ('across', 'up'): hb.cube(h, h)
    hb.settle(); hb.line = None

def walk_demo(hb, cells):
    """Card 11-12 (Demo): start = copy the base bands into the across and up (up mirrored for red);
    no white peg in the bottom.  At each later cell: Frobenius the point, then the chord add."""
    live = False; hb.marker_on = True
    for c in cells:
        hb.cr.marker_lift()
        if live: frobenius_affine(hb)
        if c == '.': continue
        if not live:
            hb.copy('across', 'base across'); hb.copy('up', 'base up', mirror=(c == 'R')); live = True
        else: chord_add_demo(hb, c == 'R')
    hb.cr.marker_lift(); hb.marker_on = False
    return live

def base_point_demo(hb):
    """Card 9 with the Demo walk: identical to homes_v3.base_point3 up to the W R W R walk, which is the
    chord walk; there is no finish (the point is already affine)."""
    j = 1
    while True:
        x = ['.'] * hb.n; x[j] = 'W'; hb.put('base across', x)
        V.curve_side(hb, 'base across', 'bottom')
        hb.mul('gap', 'bottom', 'bottom', copy_second=True); hb.settle()
        hb.white0('up')
        strip = ['R', '.'] * ((hb.n - 3) // 2) + ['R', 'W']; assert len(strip) == hb.n - 1
        hb.put('across', strip + ['.'])
        hb.marker_on = True
        for d in strip:
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
    hb.key_grid_moves += 4
    walk_demo(hb, list('WRWR'))
    hb.key_grid_moves += 4
    hb.clear('base across'); hb.clear('base up')
    hb.move('base across', 'across'); hb.move('base up', 'up')
    return j

# ---------------------------------------------------------------- Demo coordinates (calling)
SLOTS = {'across': (2, 0), 'up': (3, 0), 'bottom': (4, 0), 'base across': (5, 0),
         'base up': (2, 1), 'gap': (3, 1), 'spare': (4, 1)}          # (lane, 0 = rows A-D / 1 = rows E-H)
CONTROL_HOLES = [('I', c) for c in range(3, 11)] + [('J', c) for c in range(3, 11)]

def coord_demo(home, i):
    lane, s = SLOTS[home]; r, c = divmod(i, 2)
    return 1, 'ABCDEFGHIJ'[4 * s + r] + str(2 * lane - 1 + c)

def install_demo_coords():
    """make homes_v3's calling use the Demo grid (grid 1 = the target grid; key grid = grid 2)."""
    V.GEOM['Demo'] = dict(work=1, key=[2])
    orig = V.coord
    def coord(name, home, i):
        return coord_demo(home, i) if name == 'Demo' else orig(name, home, i)
    V.coord = coord
    def coord_inverse(name):
        if name != 'Demo': return orig_inv(name)
        return {coord_demo(h, i): (h, i) for h in H.HOMES for i in range(7)}
    orig_inv = V.coord_inverse; V.coord_inverse = coord_inverse
install_demo_coords()
