"""Faithful Python transliteration of the frozen v1 megadreifach.sudo (MegaDreifach v1 Hash;
primitives/hash/megadreifach/v1/megadreifach.sudo, deprecated).

Positions are tuples (cp, co, ep, eo) of lists.  compose(g, h) applies h first,
then g, exactly as in the sudo: cp[s] = h.cp[g.cp[s]], co[s] = h.co[g.cp[s]] + g.co[s].
Verified against the v1 KATs
(primitives/hash/megadreifach/kats/megaminx_hash_kats_v1.json) by `python3 md.py`.
"""
import os
from math import factorial
from tables import OPP, NBRS, FT_CP, FT_CO, FT_EP, FT_EO, ROTS, CORNER_FACES

PAD_BLOCK, LEN_FIELD, DIGEST_LEN, BODY_LEN, F3_T = 28, 8, 29, 52, 12

def identity():
    return (list(range(20)), [0]*20, list(range(30)), [0]*30)

def compose(g, h):
    gcp, gco, gep, geo = g; hcp, hco, hep, heo = h
    return ([hcp[gcp[s]] for s in range(20)],
            [(hco[gcp[s]] + gco[s]) % 3 for s in range(20)],
            [hep[gep[s]] for s in range(30)],
            [(heo[gep[s]] + geo[s]) % 2 for s in range(30)])

def inverse(g):
    cp, co, ep, eo = g
    cpi = [0]*20
    for s in range(20): cpi[cp[s]] = s
    coi = [(-co[cpi[s]]) % 3 for s in range(20)]
    epi = [0]*30
    for s in range(30): epi[ep[s]] = s
    eoi = [(-eo[epi[s]]) % 2 for s in range(30)]
    return (cpi, coi, epi, eoi)

FACE = [(FT_CP[f], FT_CO[f], FT_EP[f], FT_EO[f]) for f in range(12)]

def face_turn(g, face, amount):
    a = amount % 5
    t = FACE[face]
    for _ in range(a):
        g = compose(t, g)
    return g

def iv_cook12():
    g = identity()
    for f in range(12):
        g = face_turn(g, f, 1)
    return g

def noon_phys(phys, o):
    up, front = o[0], o[1]
    if phys == up: return front
    nb = NBRS[phys]
    if up in nb: return up
    upn = NBRS[up]
    for x in nb:
        if x in upn: return x
    return nb[0]

def spin_about_up(o, k):
    k %= 5
    if k == 0: return o
    up = o[0]; down = OPP[up]; nb = NBRS[up]; dn = NBRS[down]
    phys = list(range(12))
    for i in range(5): phys[nb[i]] = nb[(i + k) % 5]
    for i in range(5): phys[dn[i]] = dn[(i - k + 5) % 5]
    return [phys[x] for x in o]

ROT_BY = {(r[0], r[1]): r for r in ROTS}
def abs_reorient(c1, c2):
    return list(ROT_BY[(c1, c2)])

SLOT_OF = {}
for s, (a, b, c) in enumerate(CORNER_FACES):
    for t in ((a, b, c), (b, c, a), (c, a, b)):
        SLOT_OF[t] = s

def colour_on(face, f0, f1, f2, c0, c1, c2, ori):
    loc = 0
    if face == f1: loc = 1
    if face == f2: loc = 2
    k = (loc - ori + 3) % 3
    return (c0, c1, c2)[k]

def colours_at(g, a, b, c):
    slot = SLOT_OF[(a, b, c)]
    f0, f1, f2 = CORNER_FACES[slot]
    cub = g[0][slot]; ori = g[1][slot]
    c0, c1, c2 = CORNER_FACES[cub]
    return (colour_on(a, f0, f1, f2, c0, c1, c2, ori), colour_on(b, f0, f1, f2, c0, c1, c2, ori))

def recipe_a(g, phys, o):
    noon = noon_phys(phys, o)
    nb = NBRS[phys]
    ni = nb.index(noon) if noon in nb else 0
    nxt = nb[(ni + 1) % 5]
    c1, c2 = colours_at(g, phys, noon, nxt)
    return abs_reorient(c1, c2)

def g2_step(g, o, card, trace=None):
    rank, suit = card // 4, card % 4
    amt = suit + 1
    held = rank
    if rank < 12:
        f = o[held]; g = face_turn(g, f, amt)
        if trace is not None: trace.append((f, amt))
    else:
        held = 0
        f = o[held]; g = face_turn(g, f, (5 - amt) % 5)
        if trace is not None: trace.append((f, (5 - amt) % 5))
        o = spin_about_up(o, amt)
    noon = noon_phys(o[held], o)
    if noon != o[held]:
        g = face_turn(g, noon, 1)
        if trace is not None: trace.append((noon, 1))
    g = face_turn(g, o[1], 1)
    if trace is not None: trace.append((o[1], 1))
    return g, recipe_a(g, o[held], o)

def f3_step(g, o, trace=None):
    g = face_turn(g, o[0], 1)
    if trace is not None: trace.append((o[0], 1))
    return g, recipe_a(g, o[0], o)

def em_block(h, deal, trace=None):
    g = h; o = list(range(12))
    for c in deal[:52]:
        g, o = g2_step(g, o, c, trace)
    for _ in range(F3_T):
        g, o = f3_step(g, o, trace)
    return g

def dm_step(h, deal):
    return compose(h, em_block(h, deal))

def pad_message(msg):
    z = (PAD_BLOCK - (len(msg) + 1 + LEN_FIELD) % PAD_BLOCK) % PAD_BLOCK
    return list(msg) + [0x80] + [0]*z + list((8*len(msg)).to_bytes(8, 'big'))

def phi_unrank(n):
    avail = list(range(52)); out = []
    for i in range(52):
        d = 51 - i
        f = factorial(d)
        idx, n = divmod(n, f)
        out.append(avail.pop(idx))
    return out

def phi_rank(deal):
    avail = list(range(52)); n = 0
    for i, v in enumerate(deal):
        idx = avail.index(v); n = n*(52 - i) + idx; avail.pop(idx)
    return n

def phi_chunk(chunk):
    assert len(chunk) == 28
    return phi_unrank(int.from_bytes(bytes(chunk), 'big'))

def even_perm_rank(perm):
    n = len(perm); avail = list(range(n)); r = 0
    for i in range(n - 2):
        idx = avail.index(perm[i]); r = r*(n - i) + idx; avail.pop(idx)
    return r

def rank_position(p):
    cp, co, ep, eo = p
    n = even_perm_rank(cp)
    o3 = 0
    for i in range(19): o3 = o3*3 + co[i]
    n = n*3**19 + o3
    n = n*(factorial(30)//2) + even_perm_rank(ep)
    o2 = 0
    for i in range(29): o2 = o2*2 + eo[i]
    return n*2**29 + o2

def position_to_bytes(p):
    return rank_position(p).to_bytes(DIGEST_LEN, 'big')

def chain(msg, h=None):
    padded = pad_message(msg)
    h = iv_cook12() if h is None else h
    for b in range(0, len(padded), 28):
        h = dm_step(h, phi_chunk(padded[b:b+28]))
    return h

def Hash(msg):
    return position_to_bytes(chain(msg))

GROUP_ORDER = (factorial(20)//2) * 3**19 * (factorial(30)//2) * 2**29

# The v1 KATs (no copy here; the path is relative to this file, so the
# script runs from any working directory).
KATS_JSON = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..',
                         'primitives', 'hash', 'megadreifach', 'kats',
                         'megaminx_hash_kats_v1.json')

if __name__ == '__main__':
    import json
    with open(KATS_JSON) as f:
        kats = json.load(f)
    assert position_to_bytes(iv_cook12()).hex() == kats['iv_cook12_digest_hex']
    assert hex(GROUP_ORDER) == kats['group_order_hex']
    fails = 0
    for v in kats['vectors']:
        d = Hash(bytes.fromhex(v['msg_hex'])).hex()
        fails += d != v['digest_hex']
        print(v['name'], 'OK' if d == v['digest_hex'] else 'FAIL ' + d)
    raise SystemExit(1 if fails else 0)
