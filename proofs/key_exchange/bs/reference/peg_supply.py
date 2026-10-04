"""No-paper audit helper: peak number of WHITE and RED pegs on the table during a full BS exchange
(one player's registers X, Y, C, strip, toll register, own public value until copied, received value,
key pegs).  Mirrors bspegs.walk/multiply but samples the live peg count after every lay and every fold lift."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent                        # every path below is built from this directory
sys.path.insert(0, str(HERE.parent / "ships-pegs"))
import keygrid as KG
KEY = lambda rng: [KG.board_string(rng)]                    # one ships+pegs key grid (BS SPEC §4.2-§4.3)
import json, random
import bspegs as P, bsref as R
PAR = json.load(open(HERE / "params.json"))
cnt = lambda reg: (sum(x == 'W' for x in reg), sum(x == 'R' for x in reg))
class Board:
    def __init__(s, fixed): s.live = {}; s.fixed = fixed; s.peak = [0, 0]
    def sample(s, strip=None):
        w, r = s.fixed
        for reg in list(s.live.values()) + ([strip] if strip is not None else []):
            a, b = cnt(reg); w += a; r += b
        s.peak = [max(s.peak[0], w), max(s.peak[1], r)]
def mul(F, bd, A, B, nudge=0):
    strip = F.empty(2*F.n + nudge)
    for i, b in enumerate(B):
        if b != '.': P.lay(strip, A, i + nudge, 1 if b == 'W' else 2); bd.sample(strip)
    n = F.n; h = len(strip) - 1
    while h >= n:
        c = strip[h]
        if c == '.': h -= 1; continue
        strip[h] = '.'
        for _ in range(1 if c == 'W' else 2):
            for j, t in F.toll_pegs: P.drop(strip, h - n + j, t)
        bd.sample(strip)
    return strip[:n]
def walk(F, bd, fleets, base=None):
    """Evidence harness, not a reference: mirrors bspegs.walk, which check_oracle.py cross-checks
    against bs.sudo (normative, with the SPEC)."""
    X = None
    for board in fleets:
        for cell in board:
            if X is None:
                if cell == '.': continue
                if base is None: X = F.empty(); X[1 if cell == 'W' else 2] = 'W'
                else: X = base[:] if cell == 'W' else mul(F, bd, base, base)
                bd.live['X'] = X; continue
            Y = mul(F, bd, X, X); bd.live['Y'] = Y               # Y's old pegs are lifted as the square slides in
            nud = 0 if (base is not None or cell == '.') else (1 if cell == 'W' else 2)
            X = mul(F, bd, Y, X, nud); bd.live['X'] = X          # Y keeps X x X until the next square (B6)
            if base is not None and cell != '.':
                for _ in range(1 if cell == 'W' else 2): X = mul(F, bd, X, base); bd.live['X'] = X
    return P.tidy(F, X)
out = {}
import sys
PLAN = [("T1", 1, 20), ("T2", 1, 5), ("T6demo", 1, 1)]   # G = 1 key grid in every tier
if sys.argv[1:] == ["R1024"]: PLAN = [("R1024", 1, 1)]
for tier, G, runs in PLAN:
    d = PAR[tier]; n = d['n']; p = int(d['p']); toll = R.enc(int(d['c']), n)
    while toll[-1] == '.': toll.pop()
    F = P.Field(n, toll); rng = random.Random(8); peaks = []
    stored_toll = cnt(toll) if n >= 100 else (0, 0)       # toy tolls are kept in the head
    for _ in range(runs):
        fa = KEY(rng); fb = KEY(rng)
        if tier == "R1024":            # steady-state spot check: the first 30 key cells only
            fa = [fa[0][:30]]
        key = [sum(c == 'W' for b in fa for c in b), sum(c == 'R' for b in fa for c in b)]
        fixed = stored_toll      # key pegs reported separately (they are fixed)
        bd = Board(fixed)
        A = walk(F, bd, fa); B = R.enc(pow(3, R.exponent(fb), p), n)
        bd.live = {'A(own, until copied)': A, 'B(received, in Y)': B}; bd.sample()
        C = mul(F, bd, B, B); bd.live = {'C': C}; bd.sample()
        walk(F, bd, fa, C)
        peaks.append(bd.peak)
    mw, mr = max(x[0] for x in peaks), max(x[1] for x in peaks)
    holes = 5*n + (len(toll) if n >= 100 else 0)
    out[tier] = dict(n=n, runs=runs, note="registers only; add key pegs", peak_white=mw, peak_red=mr, holes_in_use=holes,
                     peak_red_per_hole=round(mr/holes, 3), peak_white_per_hole=round(mw/holes, 3))
    print(tier, json.dumps(out[tier]))
json.dump(out, open(HERE / ("peg_supply_output%s.json" % ("_R1024" if sys.argv[1:] else "")), "w"), indent=1)
