"""M9 (MegaDreifach v2): exhaustive search of the 2-card window of E_m.

Stdlib only.  Reuses the tables of ../lean/MegaDreifach/Em.lean and reproduces the
8 v2 KATs before searching (evidence, not identity, that this Python matches Em).
The search is computational evidence, not a proof.  The Lean proof of M9 for 2-card
windows (`twoCard_ne`, ../lean/MegaDreifach/M9.lean) does not use it; it is kept as an
independent cross-check (all 60 grips, no covariance).  See README.md in this
directory for what the numbers mean and what they do not.  Asserts the counts it
reports.

    python3 m9_search.py          # about 20 s in CI, under 100 MB
"""
import itertools
import json
import re
import sys
from collections import defaultdict
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
EM_LEAN = HERE.parent / "lean" / "MegaDreifach" / "Em.lean"
KATS = (HERE.parents[2] / "primitives" / "hash" / "megadreifach" / "kats"
        / "megaminx_hash_kats_v2.json")

SRC = EM_LEAN.read_text()


def nat_table(name):
    m = re.search(r"def " + name + r" : List \(List Nat\) := \[(.*?)\]\]", SRC, re.S)
    body = "[" + m.group(1) + "]]"
    rows = re.findall(r"\[([^\[\]]*)\]", body)
    return [[int(x) for x in re.findall(r"\d+", row)] for row in rows]


FT_CP, FT_CO, FT_EP, FT_EO, ROTS, NBRS, CORNER_FACES = (
    nat_table(n) for n in ["ftCp", "ftCo", "ftEp", "ftEo", "rots", "nbrsTab", "cornerFacesTab"])
EDGE_FLAT = [int(x) for x in re.findall(
    r"\d+", re.search(r"def edgeFacesFlat : List Nat := \[(.*?)\]", SRC, re.S).group(1))]
OPP = [int(x) for x in re.findall(
    r"\d+", re.search(r"def oppTab : List Nat := \[(.*?)\]", SRC, re.S).group(1))]
ROTS = [tuple(r) for r in ROTS]
assert len(ROTS) == 60 and len(FT_CP) == 12 and len(CORNER_FACES) == 20 and len(EDGE_FLAT) == 60

# ---- E_m, transliterated from Em.lean -------------------------------------------------
ID = (tuple(range(20)), (0,) * 20, tuple(range(30)), (0,) * 30)


def compose(g, h):  # h first, then g (the sudo / Lean convention)
    gcp, gco, gep, geo = g
    hcp, hco, hep, heo = h
    return (tuple(hcp[gcp[s]] for s in range(20)),
            tuple((hco[gcp[s]] + gco[s]) % 3 for s in range(20)),
            tuple(hep[gep[s]] for s in range(30)),
            tuple((heo[gep[s]] + geo[s]) % 2 for s in range(30)))


FM = [(tuple(FT_CP[f]), tuple(FT_CO[f]), tuple(FT_EP[f]), tuple(FT_EO[f])) for f in range(12)]


def face_turn(g, f, a):
    for _ in range(a % 5):
        g = compose(FM[f], g)
    return g


def vnoon(p, o):
    return o[1] if p == 0 else o[0] if p < 6 else o[p - 5] if p < 11 else o[6]


def spin_phys(up, k, x):
    down = OPP[up]
    if x in (up, down):
        return x
    if x in NBRS[up]:
        return NBRS[up][(NBRS[up].index(x) + k) % 5]
    if x in NBRS[down]:
        return NBRS[down][(NBRS[down].index(x) + 5 - k) % 5]
    return x


def spin(o, k):
    return o if k % 5 == 0 else tuple(spin_phys(o[0], k % 5, o[h]) for h in range(12))


def abs_reorient(c1, c2):
    for r in ROTS:
        if r[0] == c1 and r[1] == c2:
            return r
    raise ValueError("trap: abs_reorient")


def colour_on(face, f1, f2, c, ori):
    loc = 2 if face == f2 else 1 if face == f1 else 0
    return c[(loc + 3 - ori) % 3]


def corner_slot(a, b, c):
    t = (c, a, b) if c < a and c < b else (b, c, a) if b < a and b < c else (a, b, c)
    return [tuple(x) for x in CORNER_FACES].index(t)


def edge_slot(a, b):
    for s in range(30):
        if {EDGE_FLAT[2 * s], EDGE_FLAT[2 * s + 1]} == {a, b}:
            return s
    raise ValueError("trap: edge_slot")


def corner_after_noon(phys, noon):
    return NBRS[phys][(NBRS[phys].index(noon) + 1) % 5]


def read_colours_piece(kind, slot, piece, ori, phys, noon):
    """Colours shown on (phys, noon) when `piece` sits at `slot` with `ori`."""
    if kind == "c":
        f1, f2 = CORNER_FACES[slot][1], CORNER_FACES[slot][2]
        c = CORNER_FACES[piece]
        return (colour_on(phys, f1, f2, c, ori), colour_on(noon, f1, f2, c, ori))
    loc = 0 if phys == EDGE_FLAT[2 * slot] else 1
    p0, p1 = EDGE_FLAT[2 * piece], EDGE_FLAT[2 * piece + 1]
    return (p0, p1) if (loc + ori) % 2 == 0 else (p1, p0)


def read_slot(phys, noon, pos):
    if pos % 2 == 1:
        return "c", corner_slot(phys, noon, corner_after_noon(phys, noon))
    return "e", edge_slot(phys, noon)


def held_turn(g, o, card, noon_of=None):
    """First half of a card step: the held-face turn, and the read's (phys, noon).
    noon_of(phys, o) overrides the visual noon (None: SPEC §5.5 visual noon, vnoon)."""
    rank, amt = card // 4, card % 4 + 1
    if rank < 12:
        g1, ow, held = face_turn(g, o[rank], amt), o, rank
    else:
        ow = spin(o, amt)
        g1, held = face_turn(g, o[0], (5 - amt) % 5), 0
    phys = ow[held]
    return g1, ow, phys, vnoon(held, ow) if noon_of is None else noon_of(phys, ow)


def g2_step(st, card, pos, noon_of=None):
    g, o = st
    g1, ow, phys, noon = held_turn(g, o, card, noon_of)
    kind, s = read_slot(phys, noon, pos)
    piece, ori = (g1[0][s], g1[1][s]) if kind == "c" else (g1[2][s], g1[3][s])
    new_o = abs_reorient(*read_colours_piece(kind, s, piece, ori, phys, noon))
    return face_turn(face_turn(g1, noon, 1), ow[1], 1), new_o


def em_block(h, deal, noon_of=None, t=36, grips=None):
    """E_m (v2: visual noon, t = 36 F3 rounds).  noon_of(phys, o) and t select the
    comparison rules of ../security/v2/engine.py; grips, if a list, collects the grip
    after every re-grip (52 card steps, then t F3 rounds)."""
    st = (h, ROTS[0])
    for i, c in enumerate(deal[:52]):
        st = g2_step(st, c, i + 1, noon_of)
        if grips is not None:
            grips.append(st[1])
    for rnd in range(1, t + 1):
        g = face_turn(st[0], st[1][0], 1)
        phys = st[1][0]
        noon = vnoon(0, st[1]) if noon_of is None else noon_of(phys, st[1])
        kind, s = read_slot(phys, noon, rnd)
        piece, ori = (g[0][s], g[1][s]) if kind == "c" else (g[2][s], g[3][s])
        st = (g, abs_reorient(*read_colours_piece(kind, s, piece, ori, phys, noon)))
        if grips is not None:
            grips.append(st[1])
    return st[0]


# ---- hash wrapper (grip-rule independent), for the KAT self-check --------------------
def pad(msg):
    z = (28 - (len(msg) + 9) % 28) % 28
    return list(msg) + [0x80] + [0] * z + list((8 * len(msg)).to_bytes(8, "big"))


def phi_unrank(n):
    avail, out = list(range(52)), []
    for i in range(52):
        idx, n = divmod(n, factorial(51 - i))
        out.append(avail.pop(idx))
    return out


def even_rank(perm):
    avail, r = list(range(len(perm))), 0
    for i in range(len(perm) - 2):
        idx = avail.index(perm[i])
        r = r * (len(perm) - i) + idx
        avail.pop(idx)
    return r


def to_bytes(p):
    cp, co, ep, eo = p
    n = even_rank(cp)
    n = n * 3 ** 19 + int("".join(map(str, co[:19])), 3)
    n = n * (factorial(30) // 2) + even_rank(ep)
    n = n * 2 ** 29 + int("".join(map(str, eo[:29])), 2)
    return n.to_bytes(29, "big")


def hash_(msg):
    h = ID
    for f in range(12):
        h = face_turn(h, f, 1)
    m = pad(msg)
    for b in range(0, len(m), 28):
        h = compose(h, em_block(h, phi_unrank(int.from_bytes(bytes(m[b:b + 28]), "big"))))
    return to_bytes(h)


def kat_check():
    vecs = json.loads(KATS.read_text())["vectors"]
    for v in vecs:
        assert hash_(bytes.fromhex(v["msg_hex"])).hex() == v["digest_hex"], v
    return len(vecs)


# ---- the search -----------------------------------------------------------------------
def code(p):
    """Position as 50 combined codes: corner slot s -> 3*piece+ori, edge 60+2*piece+ori."""
    return (tuple(3 * p[0][s] + p[1][s] for s in range(20))
            + tuple(60 + 2 * p[2][s] + p[3][s] for s in range(30)))


def right_map(p):
    """M with code(compose(x, p))[s] = M[code(x)[s]]."""
    m = [0] * 120
    for q in range(20):
        for x in range(3):
            m[3 * q + x] = 3 * p[0][q] + (p[1][q] + x) % 3
    for q in range(30):
        for x in range(2):
            m[60 + 2 * q + x] = 60 + 2 * p[2][q] + (p[3][q] + x) % 2
    return m


def read_injectivity():
    """Read injectivity ACROSS all read configurations: for each kind (corner / edge),
    over every (phys, noon) that a read can use, every piece and every orientation,
    one ordered colour pair never comes from two different pieces.  So two windows
    whose second reads see different pieces of W get different colour pairs, even
    when their read configurations differ (different intermediate grips / cards).
    Also used by ../security/v2/experiments.py (suit_exact).  Raises AssertionError
    on a failure; returns {kind: {colour pair: piece}}."""
    out = {}
    for kind in ("c", "e"):
        pos = 1 if kind == "c" else 2
        seen = {}
        for phys in range(12):
            for noon in NBRS[phys]:
                k, s = read_slot(phys, noon, pos)
                for q in range(20 if kind == "c" else 30):
                    for x in range(3 if kind == "c" else 2):
                        r = read_colours_piece(k, s, q, x, phys, noon)
                        assert seen.setdefault(r, q) == q, (phys, noon, kind, r)
        # 20 corners x 3 cyclic ordered pairs; 30 edges x 2 ordered pairs.
        assert len(seen) == 60, (kind, len(seen))
        # abs_reorient: every read pair is some rotation's (up, front) pair (no trap),
        # and the rotation returned has that pair, so abs_reorient is injective on them.
        for r in seen:
            assert abs_reorient(*r)[:2] == r
        out[kind] = seen
    return out


def main():
    print("KATs reproduced by the Python E_m (tables from Em.lean):", kat_check())
    # Nets: g2Step((W, o), card, pos).1 = compose(net(o, card), W)  (`g2Step_fst_net`).
    nets = [[g2_step((ID, o), c, 1)[0] for c in range(52)] for o in ROTS]
    codes = [[bytes(code(n)) for n in row] for row in nets]
    ok = all(len(set(row)) == 52 for row in codes)
    print("M8 (60x52 nets pairwise distinct per grip):", ok)
    assert ok

    read_injectivity()
    print("read -> grip injective on pieces, across all read configurations: True")

    # Stage 1: two-card position products compose(net(o1, b), net(o, a)), grouped by o.
    swaps = general = 0
    sig_eq = 0

    def sigma(o, a, o1, b, p):
        """W-slot whose piece the second card's read sees (first card a at grip o)."""
        g1, _, phys, noon = held_turn(nets[ROTS.index(o)][a], o1, b)
        kind, s = read_slot(phys, noon, p + 1)
        return kind, (g1[0][s] if kind == "c" else g1[2][s])

    for oi, o in enumerate(ROTS):
        groups = defaultdict(list)
        for a in range(52):
            m = right_map(nets[oi][a])
            mg = m.__getitem__
            for o1 in range(60):
                row = codes[o1]
                for b in range(52):
                    groups[bytes(map(mg, row[b]))].append((a, o1, b))
        for v in groups.values():
            if len({x[0] for x in v}) < 2:
                continue
            for (a, o1, b), (c, o2, d) in itertools.combinations(v, 2):
                if a == c:
                    continue
                if a > c:
                    (a, o1, b), (c, o2, d) = (c, o2, d), (a, o1, b)
                general += 1
                if b == c and d == a:
                    swaps += 1
                for p in (1, 2):
                    if sigma(o, a, ROTS[o1], b, p) == sigma(o, c, ROTS[o2], d, p):
                        sig_eq += 1
    print("2-card position-equality candidates (o, a, o1, b) ~ (o, c, o2, d), a < c:", general)
    print("  of which adjacent swaps (c, d) = (b, a):", swaps)
    print("candidate x read parity with the same second-read W-slot:", sig_eq, "of", 2 * general)
    assert (general, swaps, sig_eq) == (24300, 420, 0), (general, swaps, sig_eq)
    print("=> no different-first-card 2-card window collision from any position with "
          "injective cp/ep (computational cross-check; the proof is M9.twoCard_ne)")


if __name__ == "__main__":
    sys.exit(main())
