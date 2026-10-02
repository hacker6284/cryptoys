"""Colour-named v3 card-phase candidates for MegaDreifach (stage 3, scratch only).

Every rule keeps the v2 Davies-Meyer shape exactly: all turns are face turns of puzzle A,
so E(h) = X = W*h with W the (read-dependent) turn word, and y = compose(h, X) = h*W*h
(unchanged 3-solve).  No grip, no re-grip, no grip-relative face names: a face is named by
its centre colour (centre ids 0..11 of SPEC section 4), cards map to faces by a FIXED table
rank r -> colour r (A=0, 2=1, ..., Q=11); King = face 0 turned the other way.

Naming of the card's pieces (rules NP, NPL): for face r let n_1 be r's LOWEST-numbered
neighbouring centre and n_1..n_5 the neighbours going clockwise round face r (seen from
outside).  A card of suit amount k (Clubs 1, Hearts 2, Spades 3, Diamonds 4) names the
EDGE {r, n_k} and the CORNER {r, n_k, n_k+1} (the corner at the clockwise end of that edge).
King of suit k names the same pair as the Ace of suit k.

Rules (t = number of blank rounds BR after the 52 cards):
  CF t   card: turn face r +k (King: face 0 +5-k); read the piece in the SLOT between face r
         and n_1 (odd position: the corner {r,n_1,n_2}; even: the edge {r,n_1});
         c1 = its colour on face r, c2 = its colour on face n_1; turn face c1 +1, face c2 +1.
  NP t   card: turn face r +k; find the named edge; turn the face carrying its r-coloured
         sticker +1, then the face now carrying its other sticker +1; then the same for the
         named corner (r-sticker face +1, then the face now carrying its n_k sticker +1).
  NPL t  as NP but only the r-sticker face is turned for each named piece.
  BR round j (j = 1..t): turn face 0 +1; read the slot {0,1} edge (even j) or the {0,1,2}
         corner (odd j); c1 = colour on face 0, c2 = colour on face 1; turn face c1 +1,
         face c2 +1.
  NPr m  NP card phase, then the first m cards of the deal are dealt again (NP steps).
  NRr m  NP with a REGISTER: R = the face turned last (R = 0 at the start of the block).  The
         card's own turn is on face (r + R) mod 12 (King: face R, turned -k); the named pieces
         and their four turns are exactly as in NP (so R after a card = the face carrying the
         card's corner's n_k sticker).  Then the first m cards are dealt again, R continuing.
  NRk m  NRr m with the King changed: a King turns the face OPPOSITE R by +k (NRr's King turns
         face R by -k, which aliases the Ace of the complementary suit: K-clubs and A-diamonds both
         turn face R by 4 clicks).  Kings still name the Ace's pair of their suit.
"""
import os
import random
import sys

import mdfix_lib as L

eng, ref = L.eng, L.ref
apply, compose_st, inv_st = L.apply, L.compose_st, L.inv_st
ID_ST, IV_ST, uniform_st = L.ID_ST, L.IV_ST, L.uniform_st
NB = [list(r) for r in ref.NBRS]
CF3 = [tuple(c) for c in ref.CORNER_FACES]
EFL = [(ref.EDGE_FLAT[2 * s], ref.EDGE_FLAT[2 * s + 1]) for s in range(30)]
FOP = [[None] + [eng.make_op(eng.face_pos(f, a)) for a in range(1, 5)] for f in range(12)]
F1 = [FOP[f][1] for f in range(12)]

# ---- naming tables
LOWN = [NB[r].index(min(NB[r])) for r in range(12)]


def named(r, k):
    """(edge label, corner label, n_k, n_k+1) named by face r and suit amount k (1..4)."""
    i = LOWN[r]
    n = NB[r][(i + k - 1) % 5]
    n2 = NB[r][(i + k) % 5]
    return ref.edge_slot(r, n), ref.corner_slot(r, n, n2), n, n2


def card_face_amt(card):
    rank, k = card // 4, card % 4 + 1
    if rank < 12:
        return rank, k, k
    return 0, (5 - k) % 5, k          # King: face 0, turned -k; names like the Ace of suit k


# ---- "which face carries colour c of this piece" tables, from m9_search primitives
def _tables():
    ef = [[None] * 60 for _ in range(30)]
    for s in range(30):
        f0, f1 = EFL[s]
        for v in range(60):
            pc, o = v // 2, v % 2
            a, b = ref.read_colours_piece('e', s, pc, o, f0, f1)     # colours on f0, f1
            cols = EFL[pc]
            ef[s][v] = tuple(f0 if a == c else f1 for c in cols)
    cf = [[None] * 60 for _ in range(20)]
    for s in range(20):
        fs = CF3[s]
        for v in range(60):
            pc, o = v // 3, v % 3
            on = {f: ref.colour_on(f, fs[1], fs[2], CF3[pc], o) for f in fs}
            cf[s][v] = tuple(next(f for f in fs if on[f] == c) for c in CF3[pc])
    return ef, cf


EFACE, CFACE = _tables()


def find_e(st, e):
    v = 2 * e
    try:
        s = st.index(v, 20)
    except ValueError:
        v += 1
        s = st.index(v, 20)
    return s - 20, v


def find_c(st, c):
    v = 3 * c
    for d in range(3):
        try:
            return st.index(v + d, 0, 20), v + d
        except ValueError:
            pass
    raise AssertionError


CARD = []
for card in range(52):
    f, a, k = card_face_amt(card)
    e, c, n, n2 = named(f, k)
    CARD.append((FOP[f][a] if a else None, e, EFL[e].index(f), EFL[e].index(n),
                 c, CF3[c].index(f), CF3[c].index(n), f, LOWN[f]))


def np_step(st, card, full=True, rec=None):
    op, e, ir, inn, c, jr, jn, _, _ = CARD[card]
    if op:
        apply(st, op)
    s, v = find_e(st, e)
    if rec is not None:
        rec.append(('e', e))
    apply(st, F1[EFACE[s][v][ir]])
    if full:
        s, v = find_e(st, e)
        apply(st, F1[EFACE[s][v][inn]])
    s, v = find_c(st, c)
    if rec is not None:
        rec.append(('c', c))
    apply(st, F1[CFACE[s][v][jr]])
    if full:
        s, v = find_c(st, c)
        apply(st, F1[CFACE[s][v][jn]])


# CF slot reads: slot between face r and its lowest neighbour
CFSLOT = []
for r in range(12):
    n1 = min(NB[r])
    n2 = NB[r][(LOWN[r] + 1) % 5]
    CFSLOT.append((ref.edge_slot(r, n1), ref.corner_slot(r, n1, n2), r, n1))


def slot_colours(st, kind, slot, fa, fb):
    """Colours (on face fa, on face fb) of the piece in a slot."""
    if kind == 'e':
        v = st[20 + slot]
        return ref.read_colours_piece('e', slot, v // 2, v % 2, fa, fb)
    v = st[slot]
    return ref.read_colours_piece('c', slot, v // 3, v % 3, fa, fb)


def _slot_tab(kind, slot, fa, fb):
    return [slot_colours([v] * 50, kind, slot, fa, fb) for v in range(60)]


CFTAB = [(_slot_tab('e', CFSLOT[r][0], r, CFSLOT[r][3]), _slot_tab('c', CFSLOT[r][1], r, CFSLOT[r][3]))
         for r in range(12)]
BRE = (ref.edge_slot(0, 1), _slot_tab('e', ref.edge_slot(0, 1), 0, 1))
BRC = (ref.corner_slot(0, 1, 2), _slot_tab('c', ref.corner_slot(0, 1, 2), 0, 1))


def cf_step(st, card, pos, rec=None):
    """pos is 1-based; odd -> corner."""
    op, *_, f, _ = CARD[card]
    if op:
        apply(st, op)
    es, cs, _, _ = CFSLOT[f]
    if pos & 1:
        if rec is not None:
            rec.append(('c', st[cs] // 3))
        c1, c2 = CFTAB[f][1][st[cs]]
    else:
        if rec is not None:
            rec.append(('e', st[20 + es] // 2))
        c1, c2 = CFTAB[f][0][st[20 + es]]
    apply(st, F1[c1])
    apply(st, F1[c2])


def br(st, t, rec=None):
    fo = F1[0]
    es, etab = BRE
    cs, ctab = BRC
    for j in range(1, t + 1):
        apply(st, fo)
        if j & 1:
            if rec is not None:
                rec.append(('c', st[cs] // 3))
            c1, c2 = ctab[st[cs]]
        else:
            if rec is not None:
                rec.append(('e', st[20 + es] // 2))
            c1, c2 = etab[st[20 + es]]
        apply(st, F1[c1])
        apply(st, F1[c2])


def em(kind, t, h, deal, rec=None, stop=52, rounds=True):
    st = list(h)
    if kind == 'CF':
        for i in range(stop):
            cf_step(st, deal[i], i + 1, rec)
    elif kind in ('NP', 'NPL', 'NPr'):
        full = kind != 'NPL'
        for i in range(stop):
            np_step(st, deal[i], full, rec)
        if kind == 'NPr':
            if rounds:
                for i in range(t):
                    np_step(st, deal[i], True, rec)
            return st
    else:
        raise ValueError(kind)
    if rounds:
        br(st, t, rec)
    return st


OPP = list(ref.OPP)


def nr_step(st, card, R, rec=None, kopp=False):
    """One NRr (kopp=False) / NRk (kopp=True) card step from register R; returns the new register."""
    _, e, ir, inn, c, jr, jn, f, _ = CARD[card]
    rank, k = card // 4, card % 4 + 1
    if rank < 12:
        face, a = (rank + R) % 12, k
    elif kopp:
        face, a = OPP[R], k
    else:
        face, a = R, 5 - k
    apply(st, FOP[face][a])
    s, v = find_e(st, e)
    if rec is not None:
        rec.append(('e', e))
    apply(st, F1[EFACE[s][v][ir]])
    s, v = find_e(st, e)
    apply(st, F1[EFACE[s][v][inn]])
    s, v = find_c(st, c)
    if rec is not None:
        rec.append(('c', c))
    apply(st, F1[CFACE[s][v][jr]])
    s, v = find_c(st, c)
    x = CFACE[s][v][jn]
    apply(st, F1[x])
    return x


def em_nr(t, h, deal, rec=None, stop=52, rounds=True, regout=None, kopp=False):
    st = list(h)
    R = 0
    for i in range(stop):
        R = nr_step(st, deal[i], R, rec, kopp)
    if rounds:
        for i in range(t):
            R = nr_step(st, deal[i], R, rec, kopp)
    if regout is not None:
        regout.append(R)
    return st


_em0 = em


def em(kind, t, h, deal, rec=None, stop=52, rounds=True):  # noqa: F811
    if kind == 'NRr':
        return em_nr(t, h, deal, rec, stop, rounds)
    if kind == 'NRk':
        return em_nr(t, h, deal, rec, stop, rounds, kopp=True)
    return _em0(kind, t, h, deal, rec, stop, rounds)


def make_dm(kind, t):
    return lambda h, d: compose_st(h, em(kind, t, h, d))


def cost(kind, t):
    """Per block (every deal holds each card once: sum of suit amounts = 130 = sum of King amounts' complement)."""
    if kind == 'CF':
        return dict(turns=156 + 3 * t, clicks=130 + 104 + 3 * t, reads=52 + t, finds=0, regrips=0, solves=3)
    if kind == 'NP':
        return dict(turns=260 + 3 * t, clicks=130 + 208 + 3 * t, reads=104 + t, finds=104, regrips=0, solves=3)
    if kind == 'NPL':
        return dict(turns=156 + 3 * t, clicks=130 + 104 + 3 * t, reads=104 + t, finds=104, regrips=0, solves=3)
    if kind in ('NPr', 'NRr', 'NRk'):
        return dict(turns=260 + 5 * t, clicks=f'{338} + about 6.5 per replayed card (exactly 676 for m = 52)',
                    reads=104 + 2 * t, finds=104 + 2 * t, regrips=0, solves=3)


# ---------------------------------------------------------------- slow reference (tuple positions)
def _slow_find(g, kind, piece):
    if kind == 'e':
        s = list(g[2]).index(piece)
        return s, g[3][s]
    s = list(g[0]).index(piece)
    return s, g[1][s]


def _slow_face_carrying(g, kind, piece, colour):
    s, o = _slow_find(g, kind, piece)
    if kind == 'e':
        f0, f1 = EFL[s]
        a, b = ref.read_colours_piece('e', s, piece, o, f0, f1)
        return f0 if a == colour else f1
    fs = CF3[s]
    for f in fs:
        if ref.colour_on(f, fs[1], fs[2], CF3[piece], o) == colour:
            return f
    raise AssertionError


def slow_em(kind, t, hpos, deal):
    """Literal transliteration of the hand rules on m9_search tuple positions."""
    g = hpos

    def turn(g, f, a=1):
        return ref.face_turn(g, f, a)

    def slow_np(g, card, full):
        rank, k = card // 4, card % 4 + 1
        f, a = (rank, k) if rank < 12 else (0, 5 - k)
        g = turn(g, f, a)
        nb = NB[f]
        i = nb.index(min(nb))
        n, n2 = nb[(i + k - 1) % 5], nb[(i + k) % 5]
        e, c = ref.edge_slot(f, n), ref.corner_slot(f, n, n2)
        g = turn(g, _slow_face_carrying(g, 'e', e, f))
        if full:
            g = turn(g, _slow_face_carrying(g, 'e', e, n))
        g = turn(g, _slow_face_carrying(g, 'c', c, f))
        if full:
            g = turn(g, _slow_face_carrying(g, 'c', c, n))
        return g

    def slow_slotread(g, kind, fa, fb, fc=None):
        if kind == 'e':
            s = ref.edge_slot(fa, fb)
            return ref.read_colours_piece('e', s, g[2][s], g[3][s], fa, fb)
        s = ref.corner_slot(fa, fb, fc)
        return ref.read_colours_piece('c', s, g[0][s], g[1][s], fa, fb)

    if kind in ('NRr', 'NRk'):
        R = 0
        for card in list(deal[:52]) + list(deal[:t]):
            rank, k = card // 4, card % 4 + 1
            f0 = rank if rank < 12 else 0
            if rank < 12:
                face, a = (rank + R) % 12, k
            elif kind == 'NRk':
                face, a = ref.OPP[R], k
            else:
                face, a = R, 5 - k
            g = turn(g, face, a)
            nb = NB[f0]
            i = nb.index(min(nb))
            n, n2 = nb[(i + k - 1) % 5], nb[(i + k) % 5]
            e, c = ref.edge_slot(f0, n), ref.corner_slot(f0, n, n2)
            g = turn(g, _slow_face_carrying(g, 'e', e, f0))
            g = turn(g, _slow_face_carrying(g, 'e', e, n))
            g = turn(g, _slow_face_carrying(g, 'c', c, f0))
            R = _slow_face_carrying(g, 'c', c, n)
            g = turn(g, R)
        return g
    if kind == 'CF':
        for i, card in enumerate(deal[:52]):
            rank, k = card // 4, card % 4 + 1
            f, a = (rank, k) if rank < 12 else (0, 5 - k)
            g = turn(g, f, a)
            n1 = min(NB[f])
            n2 = NB[f][(NB[f].index(n1) + 1) % 5]
            c1, c2 = slow_slotread(g, 'c' if (i + 1) % 2 else 'e', f, n1, n2)
            g = turn(turn(g, c1), c2)
    else:
        for card in deal[:52]:
            g = slow_np(g, card, kind != 'NPL')
        if kind == 'NPr':
            for card in deal[:t]:
                g = slow_np(g, card, True)
            return g
    for j in range(1, t + 1):
        g = turn(g, 0)
        c1, c2 = slow_slotread(g, 'c' if j % 2 else 'e', 0, 1, 2)
        g = turn(turn(g, c1), c2)
    return g


def selftest(kinds=(('CF', 24), ('NP', 24), ('NPL', 24), ('NPr', 13), ('NRr', 0), ('NRr', 52), ('NRk', 52))):
    out = L.selftest()
    rng = random.Random(20261001)
    for kind, t in kinds:
        ok = 0
        for _ in range(12):
            h = uniform_st(rng)
            d = list(range(52))
            rng.shuffle(d)
            a = eng.as_tuple_pos(eng.from_st(em(kind, t, h, d)))
            b = slow_em(kind, t, eng.as_tuple_pos(eng.from_st(h)), d)
            ok += a == b
        assert ok == 12, (kind, t, ok)
        # DM shape: X is a pure face-turn word applied to h -> X h^-1 is the same element as the
        # word replayed on the identity
        out.append(f'mdw_lib {kind}{t}: fast == slow literal transliteration on 12/12 random blocks')
    # coverage of the naming (all 50 pieces named by the 48 non-King cards)
    E_, C_ = set(), set()
    for card in range(48):
        _, e, _, _, c, _, _, _, _ = CARD[card]
        E_.add(e)
        C_.add(c)
    out.append(f'naming: the 48 non-King cards name {len(E_)}/30 edges and {len(C_)}/20 corners; '
               f'52 cards name {len({CARD[c][1] for c in range(52)})} edges, {len({CARD[c][4] for c in range(52)})} corners')
    assert len(E_) == 30 and len(C_) == 20
    # read -> turn encodings: for each named piece and reference colour, distinct piece states give
    # distinct turn words (NP: 60 states -> 60 distinct group elements; NPL: 12 faces)
    for kind, n, q in (('e', 30, 2), ('c', 20, 3)):
        for p in range(n):
            cols = EFL[p] if kind == 'e' else CF3[p]
            for i1 in range(len(cols)):
                for i2 in range(len(cols)):
                    if i1 == i2:
                        continue
                    words, faces = set(), set()
                    for s in range(n):
                        for o in range(q):
                            st = list(ID_ST)
                            if kind == 'e':
                                st[20 + p], st[20 + s] = st[20 + s], 2 * p + o
                                a = EFACE[s][2 * p + o][i1]
                            else:
                                st[p], st[s] = st[s], 3 * p + o
                                a = CFACE[s][3 * p + o][i1]
                            w = list(ID_ST)
                            apply(st, F1[a])
                            apply(w, F1[a])
                            s2, v2 = find_e(st, p) if kind == 'e' else find_c(st, p)
                            b = (EFACE if kind == 'e' else CFACE)[s2][v2][i2]
                            apply(w, F1[b])
                            words.add(tuple(w))
                            faces.add(a)
                    assert len(words) == 60 and len(faces) == 12, (kind, p, i1, i2, len(words))
    out.append('read->turn encodings: for every piece and ordered pair of its colours, the 60 piece states give '
               '60 distinct two-turn words (NP) and the first turn alone takes all 12 faces, 5 states each (NPL): OK')
    return out


if __name__ == '__main__':
    print('\n'.join(selftest()))
