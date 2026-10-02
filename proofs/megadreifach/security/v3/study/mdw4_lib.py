"""Per-card state-driven scrambles, memory-free registers (stage 3, scratch only; 2026-10-01 18:36 ask).

Exactly h' = h*W*h (face turns of A only; unchanged 3-solve); colour names only; no grip.
Kind string 'Z' + REG + THIRD + SLOT + s + TAIL  (t = m = tail length):
  REG   B  board register: before every card, read the edge in the slot between the Ace face and its
           lowest-ranked neighbour (the 2-face, fixed colours); B = the colour of its sticker ON THE ACE FACE.
           Nothing is carried between steps: every quantity is read when it is used (memory-free).
        H  hybrid: the last-face register L in the 52 card steps, the board register B in the echoes.
        E  piece register: the last-face register L in the 52 card steps; in the echoes the register is the face
           now carrying the n-sticker of the HELD card's own edge (re-derivable at any time from board + held card).
        P  pair register (ZP3F0E = with the SB third turn; ZP0F0E = without it, i.e. the NRk 5-turn step in the
           card pass and the echoes, card-pass last face = face of the corner's n-sticker): as E, but the echo register is (face of the held edge's n-sticker + face of the held
           corner's n-sticker) mod 12.
        L  last-face register as in NRk / SB (R = face turned last in the card part; NOT re-derivable once
           scrambles have moved the pieces) -- comparison only.
  Card step (NRk naming): turn face (rank + B) +k (King: face opposite B, +k); edge pair; corner pair
        (as NRk);  THIRD = 3: then turn the face now carrying the edge's n-sticker +1 (SB);  0: no third turn.
  Scramble: s rounds after every card.  Round j reads the piece in a slot and turns, in order, the faces
        of the COLOURS it shows on the slot's faces (each +1):
          odd j: the corner slot at (Ace, 2, 3)-faces ... see SLOT; 3 turns;   even j: the edge slot; 2 turns.
  SLOT  F  fixed slots: edge (Ace, n1), corner (Ace, n1, n2) with n1, n2 = Ace's lowest neighbour and the next
           clockwise (the 2- and 3-faces).
        R  relative slots: the same construction on face B' instead of the Ace face, B' = the board register
           re-read at the start of the round (memory-free).
  TAIL  N  none (single pass, then the 3-solve).
        E  m echoes of the last card: the card step of the held card with naming colour = B (read from the
           board at that echo) and its s scramble rounds.  Memory-free (counter pile only).
        S  m extra scramble rounds after the last card's own s rounds (memory-free).
"""
import random

import mdfix_lib as L
import mdw_lib as W
import mdw3_lib as T

ref, eng = L.ref, L.eng
apply, compose_st = L.apply, L.compose_st
FOP, F1, EFACE, CFACE, OPP, NB = W.FOP, W.F1, W.EFACE, W.CFACE, W.OPP, W.NB
find_e, find_c, EFL, CF3, NAME = W.find_e, W.find_c, W.EFL, W.CF3, T.NAME


def n12(f):
    i = W.LOWN[f]
    return NB[f][i], NB[f][(i + 1) % 5]


# slot tables, for every base face f: edge slot (f, n1), corner slot (f, n1, n2)
ESL, CSL, ETAB, CTAB, BTAB = [], [], [], [], []
for f in range(12):
    a, b = n12(f)
    es, cs = ref.edge_slot(f, a), ref.corner_slot(f, a, b)
    ESL.append(es)
    CSL.append(cs)
    et = []
    for v in range(60):
        ca, cb = ref.read_colours_piece('e', es, v // 2, v % 2, f, a)
        et.append((ca, cb))
    ETAB.append(et)
    fs = CF3[cs]
    ct = []
    for v in range(60):
        ct.append(tuple(ref.colour_on(x, fs[1], fs[2], CF3[v // 3], v % 3) for x in (f, a, b)))
    CTAB.append(ct)
    BTAB.append([c[0] for c in et])      # colour on face f of the edge in slot (f, n1)


def board_reg(st):
    return BTAB[0][st[20 + ESL[0]]]


def parse(kind):
    return dict(reg=kind[1], third=kind[2] == '3', slot=kind[3], s=int(kind[4]), tail=kind[5])


def scramble(st, s, slot):
    for j in range(1, s + 1):
        f = 0 if slot == 'F' else board_reg(st)
        if j & 1:
            for c in CTAB[f][st[CSL[f]]]:
                apply(st, F1[c])
        else:
            for c in ETAB[f][st[20 + ESL[f]]]:
                apply(st, F1[c])


def card_part(st, F, a, f0, k, third, rec=None):
    apply(st, FOP[F][a])
    e, ir, inn, c, jr, jn = NAME[f0][k]
    if rec is not None:
        rec.append(('e', e))
        rec.append(('c', c))
    s, v = find_e(st, e)
    apply(st, F1[EFACE[s][v][ir]])
    s, v = find_e(st, e)
    apply(st, F1[EFACE[s][v][inn]])
    s, v = find_c(st, c)
    apply(st, F1[CFACE[s][v][jr]])
    s, v = find_c(st, c)
    x = CFACE[s][v][jn]
    apply(st, F1[x])
    if third:
        s, v = find_e(st, e)
        x = EFACE[s][v][inn]
        apply(st, F1[x])
    return x


def em4(kind, m, h, deal, rec=None, stop=52, rounds=True, regout=None):
    P = parse(kind)
    st = list(h)
    R = 0

    def held_reg():
        c = deal[51]
        _, _, f0, k = T.card_turn(c, 0)
        e, ir, inn, cc, jr, jn = NAME[f0][k]
        s_, v = find_e(st, e)
        x = EFACE[s_][v][inn]
        if P['reg'] == 'P':
            s_, v = find_c(st, cc)
            x = (x + CFACE[s_][v][jn]) % 12
        return x

    def one(card, R, echo=False):
        if echo and P['reg'] in 'EP':
            reg = held_reg()
        else:
            reg = board_reg(st) if (P['reg'] == 'B' or (P['reg'] == 'H' and echo)) else R
        F, a, f0, k = T.card_turn(card, reg)
        if echo:
            f0 = reg
        x = card_part(st, F, a, f0, k, P['third'], rec)
        scramble(st, P['s'], P['slot'])
        return x

    for i in range(stop):
        R = one(deal[i], R)
    if rounds and m:
        if P['tail'] == 'E':
            for _ in range(m):
                R = one(deal[51], R, echo=True)
        elif P['tail'] == 'S':
            scramble(st, m, P['slot']) if P['s'] % 2 == 0 else _scr_offset(st, m, P['slot'])
    if regout is not None:
        regout.append(board_reg(st) if P['reg'] == 'B' else R)
    return st


def _scr_offset(st, m, slot):
    """tail rounds continue the alternation (after an odd s the next round is an edge round)."""
    for j in range(2, m + 2):
        f = 0 if slot == 'F' else board_reg(st)
        if j & 1:
            for c in CTAB[f][st[CSL[f]]]:
                apply(st, F1[c])
        else:
            for c in ETAB[f][st[20 + ESL[f]]]:
                apply(st, F1[c])


def make_dm(kind, m):
    return lambda h, d: compose_st(h, em4(kind, m, h, d))


def scr_turns(s):
    return 3 * ((s + 1) // 2) + 2 * (s // 2)


def cost(kind, m):
    P = parse(kind)
    per = 5 + P['third'] + scr_turns(P['s'])
    steps = 52 + (m if P['tail'] == 'E' else 0)
    turns = per * steps + (scr_turns(m) if P['tail'] == 'S' else 0)
    if P['reg'] in 'HEP':
        breads = m if P['tail'] == 'E' else 0
    else:
        breads = steps if P['reg'] == 'B' else 0
    single = turns - 52 - (m if P['tail'] == 'E' else 0)          # every turn except card turns is +1
    return dict(turns=turns, clicks=f'{130 + single} + echo card clicks (m*k)' if P['tail'] == 'E' else 130 + single,
                piece_finds=2 * steps, slot_reads=breads + (P['s'] + (P['s'] if P['slot'] == 'R' else 0)) * steps
                + ((m + (m if P['slot'] == 'R' else 0)) if P['tail'] == 'S' else 0), regrips=0, solves=3)


# ---------------------------------------------------------------- literal slow transliteration
def slow_em4(kind, m, hpos, deal):
    P = parse(kind)
    fc = W._slow_face_carrying
    g = [hpos]

    def turn(f, a=1):
        g[0] = ref.face_turn(g[0], f, a)

    def slot_cols(kind_, f):
        a, b = n12(f)
        if kind_ == 'e':
            s = ref.edge_slot(f, a)
            ca, cb = ref.read_colours_piece('e', s, g[0][2][s], g[0][3][s], f, a)
            return ca, cb
        s = ref.corner_slot(f, a, b)
        fs = CF3[s]
        return tuple(ref.colour_on(x, fs[1], fs[2], CF3[g[0][0][s]], g[0][1][s]) for x in (f, a, b))

    def breg():
        return slot_cols('e', 0)[0]

    def scr(js):
        for j in js:
            f = 0 if P['slot'] == 'F' else breg()
            for c in slot_cols('c' if j & 1 else 'e', f):
                turn(c)

    def held():
        rank_, k_ = deal[51] // 4, deal[51] % 4 + 1
        c0 = rank_ if rank_ < 12 else 0
        nb_ = NB[c0]
        i_ = nb_.index(min(nb_))
        n_, n2_ = nb_[(i_ + k_ - 1) % 5], nb_[(i_ + k_) % 5]
        x = fc(g[0], 'e', ref.edge_slot(c0, n_), n_)
        if P['reg'] == 'P':
            x = (x + fc(g[0], 'c', ref.corner_slot(c0, n_, n2_), n_)) % 12
        return x

    def one(card, R, echo=False):
        if echo and P['reg'] in 'EP':
            reg = held()
        else:
            reg = breg() if (P['reg'] == 'B' or (P['reg'] == 'H' and echo)) else R
        rank, k = card // 4, card % 4 + 1
        face, f0 = ((rank + reg) % 12, rank) if rank < 12 else (ref.OPP[reg], 0)
        if echo:
            f0 = reg
        turn(face, k)
        nb = NB[f0]
        i = nb.index(min(nb))
        n, n2 = nb[(i + k - 1) % 5], nb[(i + k) % 5]
        e, c = ref.edge_slot(f0, n), ref.corner_slot(f0, n, n2)
        turn(fc(g[0], 'e', e, f0))
        turn(fc(g[0], 'e', e, n))
        turn(fc(g[0], 'c', c, f0))
        x = fc(g[0], 'c', c, n)
        turn(x)
        if P['third']:
            x = fc(g[0], 'e', e, n)
            turn(x)
        scr(range(1, P['s'] + 1))
        return x

    R = 0
    for card in deal[:52]:
        R = one(card, R)
    if m and P['tail'] == 'E':
        for _ in range(m):
            R = one(deal[51], R, echo=True)
    if m and P['tail'] == 'S':
        scr(range(1, m + 1) if P['s'] % 2 == 0 else range(2, m + 2))
    return g[0]


def selftest(kinds):
    out = []
    rng = random.Random(20261001 + 4)
    for kind, m in kinds:
        ok = 0
        for _ in range(8):
            h = L.uniform_st(rng)
            d = list(range(52))
            rng.shuffle(d)
            a = eng.as_tuple_pos(eng.from_st(em4(kind, m, h, d)))
            b = slow_em4(kind, m, eng.as_tuple_pos(eng.from_st(h)), d)
            ok += a == b
        assert ok == 8, (kind, m, ok)
        out.append(f'mdw4_lib {kind}{m}: fast == slow literal transliteration on 8/8 random blocks')
    # coverage: the card naming is NRk's (48 non-Kings name 30 edges + 20 corners) -> every block reads all 50
    E_ = {NAME[c // 4][c % 4 + 1][0] for c in range(48)}
    C_ = {NAME[c // 4][c % 4 + 1][3] for c in range(48)}
    assert len(E_) == 30 and len(C_) == 20
    out.append('mdw4_lib naming: the 48 non-King card steps name 30/30 edges and 20/20 corners (every block reads all 50)')
    # board register is uniform over the 12 colours on the 60 states of its slot
    from collections import Counter
    cnt = Counter(BTAB[0])
    assert sorted(cnt.values()) == [5] * 12
    out.append('mdw4_lib board register: the 60 states of the (Ace, n1) edge slot give each of the 12 colours 5 times')
    return out
