"""Fast attack engine for Scramble v2 (and v1), written from primitives/hash/scramble/SPEC.md
(snapshot e01b982): a direct cubie model plus the facelet-permutation engine the attacks use.
It is not the reference: scramble.sudo is normative. It is checked against the 10 SPEC vectors
by selfcheck(), and the attack results are re-checked through the JS that sudoc generates from
scramble.sudo (scramble_sudo_check.mjs).

State = colour of each of the 54 facelet slots (position p, outward direction d).
Every face turn and whole-cube rotation is a permutation of slots, so a state update is
new[perm[i]] = old[i]. `selfcheck()` reproduces all 10 SPEC KATs (digest, final facelets,
step count) with BOTH the direct cubie model and the permutation engine.
Stage-3 review script (PYTHONDONTWRITEBYTECODE=1). Not a security claim. Write-up: REPORT.md.
"""
import itertools, math

W, Y, R, O, B, G = 1, 2, 3, 4, 5, 6
LET = {W: 'W', Y: 'Y', R: 'R', O: 'O', B: 'B', G: 'G'}
AXC = {(0, 1, 0): W, (0, -1, 0): Y, (1, 0, 0): R, (-1, 0, 0): O, (0, 0, 1): G, (0, 0, -1): B}

# ---- slots
SLOTS = []
for p in itertools.product((-1, 0, 1), repeat=3):
    if p == (0, 0, 0):
        continue
    for ax in range(3):
        if p[ax] != 0:
            d = [0, 0, 0]; d[ax] = p[ax]; SLOTS.append((p, tuple(d)))
SIDX = {s: i for i, s in enumerate(SLOTS)}
assert len(SLOTS) == 54
SOLVED = tuple(AXC[d] for (p, d) in SLOTS)

def kind(p): return sum(1 for v in p if v)    # 1 centre, 2 edge, 3 corner
CENTER_SLOTS = [i for i, (p, d) in enumerate(SLOTS) if kind(p) == 1]
CORNER_SLOTS = [i for i, (p, d) in enumerate(SLOTS) if kind(p) == 3]
EDGE_SLOTS = [i for i, (p, d) in enumerate(SLOTS) if kind(p) == 2]

MAPS = {  # SPEC "Moves" table: (layer test, map)
    'U': (lambda p: p[1] == 1, lambda v: (v[2], v[1], -v[0])),
    'D': (lambda p: p[1] == -1, lambda v: (v[2], v[1], -v[0])),
    'R': (lambda p: p[0] == 1, lambda v: (v[0], v[2], -v[1])),
    'L': (lambda p: p[0] == -1, lambda v: (v[0], -v[2], v[1])),
    'F': (lambda p: p[2] == 1, lambda v: (v[1], -v[0], v[2])),
    'B': (lambda p: p[2] == -1, lambda v: (-v[1], v[0], v[2])),
}

def perm_of(fn_slot):
    """perm[i] = index where slot i's sticker goes."""
    return tuple(SIDX[fn_slot(s)] for s in SLOTS)

def move_perm(face):
    test, m = MAPS[face]
    return perm_of(lambda s: (m(s[0]), m(s[1])) if test(s[0]) else s)

def dot(a, b): return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
def cross(a, b): return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])
def rot_perm(e, t):
    n = cross(e, t)
    f = lambda v: (dot(n, v), dot(e, v), dot(t, v))
    return perm_of(lambda s: (f(s[0]), f(s[1])))

def apply(state, perm):
    out = [0] * 54
    for i, j in enumerate(perm):
        out[j] = state[i]
    return tuple(out)

QT = {f: move_perm(f) for f in MAPS}
AXES = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
ROT = {}
for e in AXES:
    for t in AXES:
        if dot(e, t) == 0:
            ROT[(e, t)] = rot_perm(e, t)
assert len(ROT) == 24
UFR_UP = SIDX[((1, 1, 1), (0, 1, 0))]
UFR_FR = SIDX[((1, 1, 1), (0, 0, 1))]
CENTER_AT = {SLOTS[i][0]: i for i in CENTER_SLOTS}

def rot_for(state, up, front):
    e = next(p for p, i in CENTER_AT.items() if state[i] == up)
    t = next(p for p, i in CENTER_AT.items() if state[i] == front)
    return ROT[(e, t)]

def rule_b(state):
    return apply(state, rot_for(state, state[UFR_UP], state[UFR_FR]))

V2 = ['UR', 'UF', 'UL', 'UB', 'DR', 'DF', 'RU', 'RD', 'FU', 'FD', 'BU', 'FR', 'LU', 'FL', 'RF', 'RB']
V1 = ["U", "U'", "D", "D'", "L", "L'", "R", "R'", "F", "F'", "B", "B'", "U2", "D2", "L2", "R2"]

def turns(state, face, n):
    for _ in range(n):
        state = apply(state, QT[face])
    return state

def pad_v2(ny):
    out = list(ny) + [8]; k = 0
    while len(out) < 12:
        out.append([6, 0, 7, 1][k % 4]); k += 1
    return out

def pad_v1(ny):
    tf = [6, 0, 7, 1, 8, 2, 9, 3]
    out = list(ny) + [8]
    n = (8 - len(out) % 8) % 8
    out += tf[:n]
    while len(out) < 24:
        out += tf
    return out

def nybbles(msg): return [x for b in msg for x in (b >> 4, b & 15)]

def v2_symbol(state, n):
    a, b = V2[n]
    state = turns(state, a, 1); state = turns(state, b, 1)
    return rule_b(state)

def close_and_seat(state):
    state = turns(state, 'F', 2); state = turns(state, 'B', 2)
    return apply(state, rot_for(state, W, G))

def hash_v2_state(msg):
    """state after the padded tape, before the closer; and step count"""
    s = SOLVED; steps = 0
    for n in pad_v2(nybbles(msg)):
        s = v2_symbol(s, n); steps += 3
    return s, steps

def hash_v1_state(msg):
    s = SOLVED; steps = 0; tape = pad_v1(nybbles(msg))
    for i, n in enumerate(tape):
        tok = V1[n]; face = tok[0]; k = 1 if len(tok) == 1 else (3 if tok[1] == "'" else 2)
        s = turns(s, face, k); steps += 1
        if i % 8 == 7:
            s = rule_b(s); steps += 1
    return s, steps

# ---- digest (SPEC "Digest")
CSLOT = [((1, 1, 1), ((0, 1, 0), (1, 0, 0), (0, 0, 1))), ((-1, 1, 1), ((0, 1, 0), (0, 0, 1), (-1, 0, 0))),
         ((-1, 1, -1), ((0, 1, 0), (-1, 0, 0), (0, 0, -1))), ((1, 1, -1), ((0, 1, 0), (0, 0, -1), (1, 0, 0))),
         ((1, -1, 1), ((0, -1, 0), (0, 0, 1), (1, 0, 0))), ((-1, -1, 1), ((0, -1, 0), (-1, 0, 0), (0, 0, 1))),
         ((-1, -1, -1), ((0, -1, 0), (0, 0, -1), (-1, 0, 0))), ((1, -1, -1), ((0, -1, 0), (1, 0, 0), (0, 0, -1)))]
CPIECE = [{W, G, R}, {W, G, O}, {W, B, O}, {W, B, R}, {Y, G, R}, {Y, G, O}, {Y, B, O}, {Y, B, R}]
ESLOT = [((1, 1, 0), ((0, 1, 0), (1, 0, 0))), ((0, 1, 1), ((0, 1, 0), (0, 0, 1))), ((-1, 1, 0), ((0, 1, 0), (-1, 0, 0))),
         ((0, 1, -1), ((0, 1, 0), (0, 0, -1))), ((1, -1, 0), ((0, -1, 0), (1, 0, 0))), ((0, -1, 1), ((0, -1, 0), (0, 0, 1))),
         ((-1, -1, 0), ((0, -1, 0), (-1, 0, 0))), ((0, -1, -1), ((0, -1, 0), (0, 0, -1))), ((1, 0, 1), ((0, 0, 1), (1, 0, 0))),
         ((-1, 0, 1), ((0, 0, 1), (-1, 0, 0))), ((-1, 0, -1), ((0, 0, -1), (-1, 0, 0))), ((1, 0, -1), ((0, 0, -1), (1, 0, 0)))]
EPIECE = [{R, W}, {G, W}, {O, W}, {B, W}, {R, Y}, {G, Y}, {O, Y}, {B, Y}, {G, R}, {G, O}, {B, O}, {B, R}]

def rank_perm(p):
    return sum(sum(1 for j in range(n + 1, len(p)) if p[j] < p[n]) * math.factorial(len(p) - 1 - n) for n in range(len(p)))

def digest_of_seated(s):
    cp, co = [], []
    for pos, axes in CSLOT:
        cols = [s[SIDX[(pos, a)]] for a in axes]
        cp.append(CPIECE.index(set(cols)))
        co.append(next(k for k, c in enumerate(cols) if c in (W, Y)))
    ep, eo = [], []
    for pos, axes in ESLOT:
        cols = [s[SIDX[(pos, a)]] for a in axes]
        ep.append(EPIECE.index(set(cols)))
        eo.append(0 if cols[0] in (W, Y, R, O) else 1)
    v = rank_perm(cp)
    v = v * 2187 + sum(co[i] * 3 ** i for i in range(7))
    v = v * 239500800 + rank_perm(ep) // 2
    v = v * 2048 + sum(eo[i] << i for i in range(11))
    return v

FACE_SPOTS = {
    'U': [(-1, 1, -1), (0, 1, -1), (1, 1, -1), (-1, 1, 0), (0, 1, 0), (1, 1, 0), (-1, 1, 1), (0, 1, 1), (1, 1, 1)],
    'R': [(1, 1, 1), (1, 1, 0), (1, 1, -1), (1, 0, 1), (1, 0, 0), (1, 0, -1), (1, -1, 1), (1, -1, 0), (1, -1, -1)],
    'F': [(-1, 1, 1), (0, 1, 1), (1, 1, 1), (-1, 0, 1), (0, 0, 1), (1, 0, 1), (-1, -1, 1), (0, -1, 1), (1, -1, 1)],
    'D': [(-1, -1, 1), (0, -1, 1), (1, -1, 1), (-1, -1, 0), (0, -1, 0), (1, -1, 0), (-1, -1, -1), (0, -1, -1), (1, -1, -1)],
    'L': [(-1, 1, -1), (-1, 1, 0), (-1, 1, 1), (-1, 0, -1), (-1, 0, 0), (-1, 0, 1), (-1, -1, -1), (-1, -1, 0), (-1, -1, 1)],
    'B': [(1, 1, -1), (0, 1, -1), (-1, 1, -1), (1, 0, -1), (0, 0, -1), (-1, 0, -1), (1, -1, -1), (0, -1, -1), (-1, -1, -1)],
}
FACE_AX = {'U': (0, 1, 0), 'R': (1, 0, 0), 'F': (0, 0, 1), 'D': (0, -1, 0), 'L': (-1, 0, 0), 'B': (0, 0, -1)}
def facelets(s):
    return ''.join(LET[s[SIDX[(p, FACE_AX[f])]]] for f in 'URFDLB' for p in FACE_SPOTS[f])

def digest_v2(msg):
    s, _ = hash_v2_state(msg)
    return digest_of_seated(close_and_seat(s))

def evaluate(msg, version=2):
    s, steps = (hash_v2_state if version == 2 else hash_v1_state)(msg)
    s = close_and_seat(s)
    return '%017X' % digest_of_seated(s), facelets(s), steps + 3

KATS = {
    1: [(b'', '09A5C17D19DDDBEB4', 'YYGGWWWWWOOOGRYOYBRBBGGOBYGRBWRYGBBRGWGOORYWWYORRBBYRO', 30),
        (b'a', '08BA8C16E8074354D', 'WBBBWGRWGORORRRYOBBOWYGBYGOGOBGYYYYWRWYYORGWRWOGWBBRGO', 30),
        (bytes([0xA7]), '12326FE0A08A76C41', 'WWBWWGYRWBWYORGYRGRWROGYOGGBYOBYYRRWROBOOGGYWOBGRBBOBY', 30),
        (b'hello', '0DF7902ED206DF88C', 'BBWBWWRRBWBGGRRWGGBWOWGYYYRORBOYWYGWOOYOOORGGRYYBBYORG', 30),
        (b'cube', '01F2D89DA1132D945', 'YRRBWGWRWRWGYRBWRYBBGWGGWOBGYOGYYYWORWRBOOGOOYGBYBOBRO', 30)],
    2: [(b'', '06024E9B61052F461', 'RRORWBOYOWRBGRWROOBGGWGRYYWGBGGYWWOYBWWOOGRORYYYBBBGYB', 39),
        (b'a', '1588A6469CFE7B286', 'RRYBWYGGGROBGRYBWWYWYGGOGBOOOWRYRBBRGROWOYYGWRYWBBOBWO', 39),
        (bytes([0xA7]), '1552B6EF7DA10C2E8', 'OGBYWYBWRYORWROGWRRGGBGROROWGYBYOBBWYRWBOWOOGYYBGBRGYW', 39),
        (b'hello', '052A3C7D12291D140', 'ORWWWWWYWGRRORWGBOROORGBOBYBRRGYYYWYYOGGOGBYWBYBBBOGGR', 39),
        (b'cube', '132FDCE0BF26E5898', 'OGBYWWWYYGBRBRWGRORGROGOBRWOYORYGRBWGOGWOWBBYYOYGBRBYW', 39)],
}
GROUP = math.factorial(8) * 3 ** 7 * math.factorial(12) // 2 * 2 ** 11

def selfcheck(verbose=True):
    ok = True
    assert facelets(SOLVED) == 'WWWWWWWWWRRRRRRRRRGGGGGGGGGYYYYYYYYYOOOOOOOOOBBBBBBBBB'
    for v, rows in KATS.items():
        for msg, dg, fl, st in rows:
            got = evaluate(msg, v)
            good = got == (dg, fl, st)
            ok &= good
            if verbose:
                print(f"  KAT v{v} {msg!r:10}: {'ok' if good else 'MISMATCH ' + str(got)}")
    return ok

if __name__ == '__main__':
    print('Scramble engine self-check (10 SPEC KATs):')
    r = selfcheck()
    print(f'  |G| = {GROUP} = 2^{math.log2(GROUP):.3f}; sqrt = 2^{math.log2(GROUP) / 2:.3f}')
    print('ALL OK' if r else 'FAILED')
