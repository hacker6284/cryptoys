"""MegaDreifach v2 (C36) and its grip-rule relatives: fast engine plus self-check.

Stdlib only.  Evidence, not proof: nothing here is a security claim.

Sources (nothing new is transcribed by hand):
  * face-turn, rotation, neighbour, corner and edge tables, and the slow reference E_m:
    ../../m9/m9_search.py, which reads them out of ../../lean/MegaDreifach/Em.lean;
  * pad, phi, digest encoding, compose / inverse (grip-rule independent, unchanged from v1)
    and v1's table noon `noon_phys` (used only by rule 'A' below): ../md.py, the
    transliteration of the frozen v1 sudo.

Rules.  All read ONE piece right after the held-face turn (King: after the Up counter-turn
and the spin), odd positions the noon corner, even positions the noon edge, then turn the
noon face +1 and Front +1 and re-grip (SPEC §5.3 / §5.5).  They differ only in the noon and
in the number t of F3 rounds:
  C36   visual noon, t = 36: MegaDreifach v2 itself.
  A_vn  visual noon, t = 12: "the v2 card rule with 12 F3 rounds" (SPEC §8).  Its 52 card
        steps are v2's.
  C76   visual noon, t = 76: the heavier alternative the grip-rule review compared.
  A     v1's table noon, t = 12: the review's "A" / "v2e", kept only as the control for the
        visual-noon repair (SPEC §1 naming note, §8).
The engine is a port of the review engine `md3.py` (rules of the same names), restricted to
these four; see README.md.

STATE ENCODING (as md3.py): st[s] = 3*cp[s] + co[s] for corner slots s < 20 and
st[20+s] = 2*ep[s] + eo[s] for edge slots.  Grips are indices into ROTS (0 = home grip).

`selfcheck()` must pass before any experiment runs (experiments.py calls it):
  1. the Em.lean tables equal ../tables.py (the v1 sudo tables; the face turns did not change);
  2. the fast engine's Hash reproduces all 8 v2 KAT digests, the IV-COOK12 digest, |G| and
     the HashDeck vector of primitives/hash/megadreifach/kats/megaminx_hash_kats_v2.json;
  3. the slow reference (m9_search's Em.lean transliteration) reproduces the 8 digests too;
  4. fast == slow E_m, grip sequence included, on random states for every rule above;
  5. Hash('') and Hash('abc') of rules A_vn, C36 and A start with the prefixes the review
     engine printed (its out/md3_selfcheck.txt), so this port computes the review's rules.
"""
import json
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SEC = os.path.dirname(HERE)
sys.path.insert(0, SEC)
sys.path.insert(0, os.path.join(SEC, '..', 'm9'))
import m9_search as ref  # noqa: E402  (tables from Em.lean; slow reference E_m)
import md as v1  # noqa: E402  (v1 sudo transliteration: grip-rule independent parts)
import tables as v1_tables  # noqa: E402

KATS_V2 = os.path.join(SEC, '..', '..', '..', 'primitives', 'hash', 'megadreifach', 'kats',
                       'megaminx_hash_kats_v2.json')

identity, compose, inverse = v1.identity, v1.compose, v1.inverse
phi_chunk, phi_rank, pad_message = v1.phi_chunk, v1.phi_rank, v1.pad_message
position_to_bytes, GROUP_ORDER = v1.position_to_bytes, v1.GROUP_ORDER

NBRS = [list(r) for r in ref.NBRS]
GRIPS = [tuple(r) for r in ref.ROTS]
RI = {(g[0], g[1]): i for i, g in enumerate(GRIPS)}      # (Up, Front) -> grip index
ADDC = [[(x // 3) * 3 + (x % 3 + d) % 3 for x in range(60)] for d in range(3)]
ADDE = [[(x // 2) * 2 + (x % 2 + d) % 2 for x in range(60)] for d in range(2)]
LIM = 2 ** 224

RULES = {  # name: (noon, F3 rounds)
    'C36': ('visual', 36),
    'A_vn': ('visual', 12),
    'C76': ('visual', 76),
    'A': ('table', 12),
}


def to_st(p):
    cp, co, ep, eo = p
    return [3 * cp[s] + co[s] for s in range(20)] + [2 * ep[s] + eo[s] for s in range(30)]


def from_st(st):
    return ([x // 3 for x in st[:20]], [x % 3 for x in st[:20]],
            [x // 2 for x in st[20:]], [x % 2 for x in st[20:]])


def visual_noon(phys, o):
    """SPEC §5.5 visual noon (the same as m9_search.vnoon, keyed by the face)."""
    return ref.vnoon(o.index(phys), o)


def table_noon(phys, o):
    """v1's table noon (md.noon_phys); rule 'A' only."""
    return v1.noon_phys(phys, list(o))


NOONS = {'visual': visual_noon, 'table': table_noon}


def face_pos(f, a):
    return ref.face_turn(ref.ID, f, a)


def word_elem(turns):
    w = ref.ID
    for f, a in turns:
        if a % 5:
            w = ref.compose(face_pos(f, a % 5), w)
    return w


def make_op(G):
    """G a position; returns (srcs, dsts, tabs) implementing st <- compose(G, st)."""
    srcs, dsts, tabs = [], [], []
    for s in range(20):
        if G[0][s] != s or G[1][s]:
            srcs.append(G[0][s]); dsts.append(s); tabs.append(ADDC[G[1][s]])
    for s in range(30):
        if G[2][s] != s or G[3][s]:
            srcs.append(20 + G[2][s]); dsts.append(20 + s); tabs.append(ADDE[G[3][s]])
    return (tuple(srcs), tuple(dsts), tuple(tabs))


def apply(st, op):
    srcs, dsts, tabs = op
    vals = [st[i] for i in srcs]
    for d, t, v in zip(dsts, tabs, vals):
        st[d] = t[v]


def read_table(phys, noon, parity):
    """(state index of the read slot, code -> new grip index) for a read at (phys, noon)."""
    kind, slot = ref.read_slot(phys, noon, 1 if parity else 2)
    out = []
    if kind == 'c':
        for x in range(60):
            out.append(RI[ref.read_colours_piece('c', slot, x // 3, x % 3, phys, noon)])
        return slot, out
    for x in range(60):
        out.append(RI[ref.read_colours_piece('e', slot, x // 2, x % 2, phys, noon)])
    return 20 + slot, out


class Engine:
    """steps[parity][gi][card] = (op1, reads, op2, turns); f3[parity][gi] = (op, reads, None, turns).
    parity = position & 1 (odd positions read the corner).  reads = ((slot, table),)."""

    def __init__(self, name):
        self.name = name
        noon, self.t = RULES[name]
        nf = self.noonf = NOONS[noon]
        opc, rdc = {}, {}

        def op(turns):
            key = tuple(turns)
            if key not in opc:
                opc[key] = make_op(word_elem(turns))
            return opc[key]

        def rd(phys, n, par):
            key = (phys, n, par)
            if key not in rdc:
                rdc[key] = read_table(phys, n, par)
            return (rdc[key],)

        self.steps = [[None] * 60 for _ in range(2)]
        self.f3 = [[None] * 60 for _ in range(2)]
        for par in (0, 1):
            for gi in range(60):
                o = GRIPS[gi]; row = []
                for card in range(52):
                    rank, amt = card // 4, card % 4 + 1
                    if rank < 12:
                        o2 = o; phys = o[rank]; first = [(phys, amt)]
                    else:
                        first = [(o[0], 5 - amt)]; o2 = ref.spin(o, amt); phys = o2[0]
                    n = nf(phys, o2)
                    assert n != phys
                    rest = [(n, 1), (o2[1], 1)]
                    row.append((op(first), rd(phys, n, par), op(rest), first + rest))
                self.steps[par][gi] = row
                phys = o[0]
                self.f3[par][gi] = (op([(phys, 1)]), rd(phys, nf(phys, o), par), None, [(phys, 1)])

    def run(self, st, deal, gi=0, start=0, stop=None, f3=True, rec=None, grips=None, trace=None):
        """Mutates st.  Cards deal[start:stop] at 1-based positions start+1.., then the F3
        rounds if f3.  rec collects (state index, code) of every read."""
        stop = len(deal) if stop is None else stop
        steps = self.steps
        for i in range(start, stop):
            op1, rd, op2, turns = steps[(i + 1) & 1][gi][deal[i]]
            apply(st, op1)
            s, tab = rd[0]
            if rec is not None:
                rec.append((s, st[s]))
            ng = tab[st[s]]
            apply(st, op2); gi = ng
            if grips is not None:
                grips.append(gi)
            if trace is not None:
                trace.extend(turns)
        if f3:
            for r in range(self.t):
                op1, rd, _, turns = self.f3[(r + 1) & 1][gi]
                apply(st, op1)
                s, tab = rd[0]
                if rec is not None:
                    rec.append((s, st[s]))
                gi = tab[st[s]]
                if grips is not None:
                    grips.append(gi)
                if trace is not None:
                    trace.extend(turns)
        return gi

    def step_grip(self, st, par, gi, card):
        """Grip produced by one card from (st, gi) at a position of parity par (st is mutated:
        the held-face turn is applied)."""
        op1, rd, _, _ = self.steps[par][gi][card]
        apply(st, op1)
        s, tab = rd[0]
        return tab[st[s]]

    def em(self, h_st, deal, **kw):
        st = list(h_st); self.run(st, deal, **kw); return st

    def dm(self, h_st, deal):
        return compose_st(h_st, self.em(h_st, deal))


def compose_st(g, h):
    """compose(g, h) on encoded states (h applied first)."""
    out = [0] * 50
    for s in range(20):
        x = g[s]; y = h[x // 3]; out[s] = (y // 3) * 3 + (y % 3 + x % 3) % 3
    for s in range(20, 50):
        x = g[s]; y = h[20 + x // 2]; out[s] = (y // 2) * 2 + (y % 2 + x % 2) % 2
    return out


_ENG = {}


def engine(name):
    if name not in _ENG:
        _ENG[name] = Engine(name)
    return _ENG[name]


IV_ST = to_st(v1.iv_cook12())


def Hash(msg, rule='C36'):
    E = engine(rule); padded = pad_message(msg); h = list(IV_ST)
    for b in range(0, len(padded), 28):
        h = E.dm(h, phi_chunk(padded[b:b + 28]))
    return position_to_bytes(from_st(h))


def HashDeck(deal, rule='C36'):
    """SPEC §2: Hash(phi^-1(deal)) when the deal's factoradic rank is < 2^224."""
    n = phi_rank(deal)
    if sorted(deal) != list(range(52)) or n >= LIM:
        raise ValueError('not a message deal')
    return Hash(n.to_bytes(28, 'big'), rule)


def HashDeckBodyFrom(deal, h_st, rule='C36'):
    """SPEC §2: one DM compression from the caller's chaining value (free-start surface)."""
    return position_to_bytes(from_st(engine(rule).dm(list(h_st), list(deal))))


# ---------------------------------------------------------------- slow reference

def ref_noon_t(rule):
    """Keyword arguments of m9_search.em_block (the slow reference E_m, transliterated from
    Em.lean) for a rule: its noon (None = m9_search's own visual noon) and F3 count."""
    noon, t = RULES[rule]
    return {'noon_of': None if noon == 'visual' else NOONS[noon], 't': t}


def ref_hash(msg, rule='C36'):
    """Slow Hash: m9_search's IV, pad and digest code around m9_search.em_block."""
    h = ref.ID
    for f in range(12):
        h = ref.face_turn(h, f, 1)
    m = ref.pad(msg)
    for b in range(0, len(m), 28):
        deal = ref.phi_unrank(int.from_bytes(bytes(m[b:b + 28]), 'big'))
        h = ref.compose(h, ref.em_block(h, deal, **ref_noon_t(rule)))
    return ref.to_bytes(h)


def ref_body_from(deal, h, rule='C36'):
    """Slow HashDeckBodyFrom: position_to_bytes(compose(h, E_m(h)))."""
    return ref.to_bytes(ref.compose(h, ref.em_block(h, deal, **ref_noon_t(rule))))


def as_tuple_pos(p):
    return tuple(tuple(x) for x in p)


# ---------------------------------------------------------------- helpers (as md3 / md.py)

def perm_parity(q):
    n = len(q); seen = [False] * n; par = 0
    for i in range(n):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]:
                seen[j] = True; j = q[j]; L += 1
            par ^= (L - 1) & 1
    return par


def legal(p):
    cp, co, ep, eo = p
    return (sorted(cp) == list(range(20)) and sorted(ep) == list(range(30)) and perm_parity(cp) == 0
            and perm_parity(ep) == 0 and sum(co) % 3 == 0 and sum(eo) % 2 == 0)


def uniform_pos(rng):
    """Exactly uniform legal position (the review's md.uniform_pos, draw for draw)."""
    cp = list(range(20)); rng.shuffle(cp)
    if perm_parity(cp): cp[0], cp[1] = cp[1], cp[0]
    ep = list(range(30)); rng.shuffle(ep)
    if perm_parity(ep): ep[0], ep[1] = ep[1], ep[0]
    co = [rng.randrange(3) for _ in range(19)]; co.append((-sum(co)) % 3)
    eo = [rng.randrange(2) for _ in range(29)]; eo.append(sum(eo) % 2)
    return (cp, co, ep, eo)


def uniform_st(rng):
    return to_st(uniform_pos(rng))


def rand_deal(rng):
    return phi_chunk([rng.randrange(256) for _ in range(28)])


def read_hslots(h_st, rec):
    """Map recorded reads (state index, code) back to slots of the INPUT h: each read reveals
    one piece of h, and the piece's slot in h is returned."""
    posc = {h_st[s] // 3: s for s in range(20)}; pose = {h_st[20 + s] // 2: s for s in range(30)}
    return [('c', posc[x // 3]) if s < 20 else ('e', pose[x // 2]) for s, x in rec]


def ci95(k, n):
    """Wilson 95% interval for k/n; for k = 0 the exact one-sided 95% upper bound 1 - 0.05^(1/n)."""
    if n == 0:
        return (0, 1)
    if k == 0:
        return (0.0, 1 - 0.05 ** (1 / n))
    z = 1.96; p = k / n; den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den; w = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (max(0, c - w), min(1, c + w))


# ---------------------------------------------------------------- self-check

def selfcheck(n_random=40):
    """Returns the report lines; raises AssertionError on any mismatch."""
    out = []
    # 1. tables
    ft = [tuple(tuple(x) for x in ref.FM[f]) for f in range(12)]
    ft1 = [(tuple(v1_tables.FT_CP[f]), tuple(v1_tables.FT_CO[f]), tuple(v1_tables.FT_EP[f]),
            tuple(v1_tables.FT_EO[f])) for f in range(12)]
    assert ft == ft1, 'Em.lean face-turn tables differ from tables.py'
    assert GRIPS == [tuple(r) for r in v1_tables.ROTS], 'Em.lean rots differ from tables.py'
    assert NBRS == [list(r) for r in v1_tables.NBRS] and list(ref.OPP) == list(v1_tables.OPP)
    assert [tuple(c) for c in ref.CORNER_FACES] == [tuple(c) for c in v1_tables.CORNER_FACES]
    out.append('tables: Em.lean face turns, 60 rotations, neighbours, opposites and corner faces '
               '== ../tables.py (v1 sudo): yes')
    # 2. KATs (fast engine)
    with open(KATS_V2) as f:
        kats = json.load(f)
    assert kats['version'] == 'v2' and kats['f3_t'] == 36
    assert position_to_bytes(v1.iv_cook12()).hex() == kats['iv_cook12_digest_hex']
    assert hex(GROUP_ORDER) == kats['group_order_hex']
    vecs = kats['vectors']
    n = sum(Hash(bytes.fromhex(v['msg_hex'])).hex() == v['digest_hex'] for v in vecs)
    assert n == len(vecs) == 8, f'fast engine: {n}/{len(vecs)} v2 KATs'
    hd = kats['hash_deck']
    assert bytes(28).hex() == hd['phi_inv_hex'] and phi_rank(hd['deal_ids']) == 0
    assert HashDeck(hd['deal_ids']).hex() == hd['digest_hex'] == Hash(bytes(28)).hex()
    out.append(f'fast engine C36 vs v2 KATs: {n}/{len(vecs)} Hash digests, HashDeck vector, '
               'IV-COOK12 digest and |G|: OK')
    # 3. KATs (slow reference)
    ns = sum(ref.hash_(bytes.fromhex(v['msg_hex'])).hex() == v['digest_hex'] for v in vecs)
    assert ns == 8, f'slow reference: {ns}/8'
    out.append(f'slow reference (m9_search, Em.lean transliteration) vs v2 KATs: {ns}/8 Hash digests: OK')
    # 4. fast == slow on random states, every rule, grips included
    assert ref_hash(b'abc') == ref.hash_(b'abc') == Hash(b'abc')
    rng = random.Random(20260930)
    for rule in RULES:
        E = engine(rule); same = 0
        for _ in range(n_random):
            h = uniform_pos(rng); d = rand_deal(rng); hp = as_tuple_pos(h)
            gf, gs = [], []
            a = from_st(E.em(to_st(h), d, grips=gf))
            b = ref.em_block(hp, d, grips=gs, **ref_noon_t(rule))
            same += as_tuple_pos(a) == b and gf == [GRIPS.index(tuple(o)) for o in gs]
        assert same == n_random, f'{rule}: fast != slow on {n_random - same} blocks'
        out.append(f'fast engine {rule} vs slow reference: {same}/{n_random} random (uniform h, '
                   'random deal) blocks with identical E_m and grip sequence')
    # 5. the review engine's recorded candidate digests (prefixes of 12 bytes)
    for rule, e0, eabc in REVIEW_PREFIXES:
        assert Hash(b'', rule).hex()[:24] == e0 and Hash(b'abc', rule).hex()[:24] == eabc, rule
    out.append("Hash('') and Hash('abc') prefixes of rules " + ', '.join(r for r, _, _ in REVIEW_PREFIXES)
               + ' == the review engine md3.py (its out/md3_selfcheck.txt): yes')
    return out


# Recorded from the grip-rule review's out/md3_selfcheck.txt ("candidate digest" lines).
REVIEW_PREFIXES = (('A_vn', '01dd01060796b9d9f6bb4252', '03a8cf306436f6af61192691'),
                   ('C36', '00177fb4f00c600607ae0bae', '02127ee2a640fdd7f250205c'),
                   ('A', '01005615833cb886ad15c954', '01768cfec9456d948eadc719'))


if __name__ == '__main__':
    print('\n'.join(selfcheck()))
