"""(a) keypad wording vs the kit's d10 rule; (b) root-strip digits; (c) per-operation costs on the
fixed-home board; (d) sparse +-tau^e relation search at Toy (meet in the middle) + count heuristic."""
import sys, os, random, json, math, itertools
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'card'))   # homes.py lives with the card harness
import homes as H
os.chdir(H.ECBS)
import ecbs_exchange as X
os.chdir(HERE)
out = {}
# (a) keypad: kit rule = group (1-3 / 4-6 / 7-9) then place in group; low/mid/high = empty/white/red (RANDOMIZER_KIT s3)
Tk = lambda x, lo, n: ("low", "mid", "high")[(x - lo) * 3 // n]
colour = {"low": '.', "mid": 'W', "high": 'R'}
KEYPAD = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
def card_rule(f):          # 'the row the number sits in gives the first hole's peg, its column gives the second's;
    r = [i for i in range(3) if f in KEYPAD[i]][0]; c = KEYPAD[r].index(f)   # top row / left column = no peg, middle = white, bottom row / right column = red'
    return '.WR'[r] + '.WR'[c]
kit = {f: colour[Tk(f, 1, 9)] + colour[("low", "mid", "high")[(f - 1) % 3]] for f in range(1, 10)}
card = {f: card_rule(f) for f in range(1, 10)}
out['keypad'] = dict(card=card, kit=kit, agree=card == kit, pairs_each_once=len(set(card.values())) == 9, six=card[6])
# (b) root strip = base-3 digits of (3^n+1)/4, most significant first
def trits(e):
    d = []
    while e: d.append(e % 3); e //= 3
    return d[::-1]
out['root strip'] = {}
for name, n in (('Toy', 23), ('Hobby', 59), ('Serious', 179)):
    pat = ''.join('.WR'[t] for t in trits((3 ** n + 1) // 4)); want = 'R.' * ((n - 3) // 2) + 'RW'
    out['root strip'][name] = dict(len=len(pat), equals_card_strip=pat == want)
# (c) per-op costs, averaged over random elements
rnd = random.Random(99)
costs = {}
for name in ('Toy', 'Hobby', 'Serious'):
    T = X.Tier(name); R = T.R; c = {}
    def fresh():
        hb = H.HB(name, T.n, T.k); return hb
    reps = 20 if name != 'Serious' else 8
    acc = {'multiply': [], 'cube': [], 'invert (with its check)': [], 'chord add': [], 'F-form add + Frobenius': []}
    for _ in range(reps):
        hb = fresh(); hb.put('across', R.rand_el(rnd)); hb.put('up', R.rand_el(rnd))
        m = hb.moves; hb.mul('gap', 'across', 'up', copy_second=True); hb.settle(); acc['multiply'].append(hb.moves - m)
        m = hb.moves; hb.cube('gap', 'gap'); hb.settle(); acc['cube'].append(hb.moves - m)
        hb.clear('gap'); hb.clear('up'); hb.move('bottom', 'across')
        m = hb.moves; H.invert_checked(hb, 'bottom'); acc['invert (with its check)'].append(hb.moves - m)
        # chord add of two random subgroup points (first in across/up, second in base)
        P1 = R.unpt(R.mul(rnd.randrange(1, T.l), T.Pref)); P2 = R.unpt(R.mul(rnd.randrange(1, T.l), T.Pref))
        hb = fresh(); hb.put('across', P1[0]); hb.put('up', P1[1]); hb.put('base across', P2[0]); hb.put('base up', P2[1])
        def run(): hb.copy('bottom', 'base across'); hb.add('bottom', 'across', mirror=True)
        def rise(): hb.copy('spare', 'base up'); hb.add('spare', 'up', mirror=True)
        m = hb.moves; H.chord_add(hb, run, rise); acc['chord add'].append(hb.moves - m)
        assert R.pt((hb.value('across'), hb.value('up'))) == R.add(R.pt(P1), R.pt(P2))
        hb = fresh(); hb.put('base across', P2[0]); hb.put('base up', P2[1]); H.start_walk(hb, False)
        H.frobenius_point(hb); H.fform_add(hb, False)          # warm-up so Z is a general number
        m = hb.moves; H.frobenius_point(hb); H.fform_add(hb, rnd.random() < .5); acc['F-form add + Frobenius'].append(hb.moves - m)
    costs[name] = {k: round(sum(v) / len(v)) for k, v in acc.items()}
    print(name, costs[name], flush=True)
out['per-op moves (mean)'] = costs
# (d) sparse relations sum(+-tau^e) that kill <P> but not E(GF(3)), at Toy, up to 7 terms
T = X.Tier('Toy'); l, lam, n = T.l, T.lam, T.n
pw = [pow(lam, e, l) for e in range(n)]
def combos(t):
    for es in itertools.combinations(range(n), t):
        for sg in itertools.product((1, -1), repeat=t):
            yield sum(s * pw[e] for s, e in zip(sg, es)) % l, tuple(zip(sg, es))
half = {}
for t in (1, 2, 3):
    for v, c in combos(t): half.setdefault(v, []).append(c)
found = []
for t in (1, 2, 3, 4):
    for v, c in combos(t):
        for d in half.get((-v) % l, []):
            es = {e for _, e in c} | {e for _, e in d}
            if len(es) != len(c) + len(d): continue
            f1 = sum(s for s, _ in c) + sum(s for s, _ in d)
            if f1 % 5: found.append((len(c) + len(d), c + d))
out['sparse relations at Toy (<=7 terms, killing <P>, nonzero on GF(3) points)'] = len(found)
heur = {}
for name, nn, tmax in (('Toy', 23, 7), ('Hobby', 59, 9), ('Serious', 179, 11)):
    lt = (3 ** nn + 1 - [None] * 0 .__len__()) if False else None
    TT = X.Tier(name)
    heur[name] = {f'{t} terms': f"{math.comb(nn, t) * 2 ** t / TT.l:.2e}" for t in range(2, tmax + 1)}
out['expected number of relations (count / l)'] = heur
print(json.dumps(out, indent=1, default=str))
json.dump(out, open(os.path.join(HERE, 'extras.json'), 'w'), indent=1, default=str)
