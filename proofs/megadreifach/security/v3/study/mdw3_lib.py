"""Single-pass colour-named card phases for MegaDreifach (stage 3, scratch only; 2026-10-01 14:11 ask).

All rules keep h' = h*W*h exactly (face turns of A only; unchanged 3-solve), colour names only, no grip.
Names (as NRk, mdw_lib): colour f, suit k (C1 H2 S3 D4) names the edge {f, n_k} and the corner
{f, n_k, n_k+1}; n_1 = f's lowest-ranked neighbour, n_2.. clockwise.  Card rank r < 12 -> colour r;
King -> colour 0 (Ace colour).  Register R ("last face"), R = 0 (Ace face) at the start.

Card turn (every rule):  non-King: face (r + R) mod 12 by +k;  King: face opposite R by +k.

Step variants (VAR):
  A  NRk step: edge: turn face carrying its f-sticker +1, then face now carrying its n-sticker +1;
     corner: same (f-sticker face +1, then n-sticker face +1);  R := that last face.        5 turns
  B  A, then a third turn: the face now carrying the EDGE's n-sticker +1;  R := that face.  6 turns
  C  A, but R := (face now carrying the edge's n-sticker + face now carrying the corner's
     n-sticker) mod 12 (no extra turn; read both after the corner turns).                  5 turns
  D  3 turns per card: edge: face carrying its n-sticker +1; corner: face carrying its n-sticker +1;
     R := (face now carrying edge's n-sticker + face now carrying corner's n-sticker) mod 12. 3 turns
Tail (no cards are dealt again): after the 52nd card, keep that last card L in hand and play m ECHO
steps.  An echo step is a card step of L, except for the naming colour:
  TAIL F  echo names L's own pieces (colour of L, suit of L): the same edge and corner every echo.
  TAIL R  echo names the pieces of colour R (current last face) with L's suit.
Kind string: 'S' + VAR + TAIL, e.g. 'SAF' with t = m.  m = 0 is the bare single pass.
"""
import random

import mdfix_lib as L
import mdw_lib as W

ref, eng = L.ref, L.eng
apply, compose_st = L.apply, L.compose_st
FOP, F1, EFACE, CFACE, OPP, NB = W.FOP, W.F1, W.EFACE, W.CFACE, W.OPP, W.NB
find_e, find_c, EFL, CF3 = W.find_e, W.find_c, W.EFL, W.CF3

NAME = [[None] * 5 for _ in range(12)]
for f in range(12):
    for k in range(1, 5):
        e, c, n, n2 = W.named(f, k)
        NAME[f][k] = (e, EFL[e].index(f), EFL[e].index(n), c, CF3[c].index(f), CF3[c].index(n))


def card_turn(card, R):
    rank, k = card // 4, card % 4 + 1
    if rank < 12:
        return (rank + R) % 12, k, rank, k
    return OPP[R], k, 0, k


def step(st, F, a, f0, k, var, rec=None):
    apply(st, FOP[F][a])
    e, ir, inn, c, jr, jn = NAME[f0][k]
    if rec is not None:
        rec.append(('e', e))
        rec.append(('c', c))
    if var == 'D':
        s, v = find_e(st, e)
        apply(st, F1[EFACE[s][v][inn]])
        s, v = find_c(st, c)
        x = CFACE[s][v][jn]
        apply(st, F1[x])
        s, v = find_e(st, e)
        return (EFACE[s][v][inn] + x) % 12
    s, v = find_e(st, e)
    apply(st, F1[EFACE[s][v][ir]])
    s, v = find_e(st, e)
    apply(st, F1[EFACE[s][v][inn]])
    s, v = find_c(st, c)
    apply(st, F1[CFACE[s][v][jr]])
    s, v = find_c(st, c)
    x = CFACE[s][v][jn]
    apply(st, F1[x])
    if var == 'A':
        return x
    s, v = find_e(st, e)
    y = EFACE[s][v][inn]
    if var == 'B':
        apply(st, F1[y])
        return y
    if var == 'C':
        return (x + y) % 12
    raise ValueError(var)


def em3(kind, m, h, deal, rec=None, stop=52, rounds=True, regout=None):
    var, tail = kind[1], kind[2]
    st = list(h)
    R = 0
    for i in range(stop):
        F, a, f0, k = card_turn(deal[i], R)
        R = step(st, F, a, f0, k, var, rec)
    if rounds and m:
        last = deal[51]
        for _ in range(m):
            F, a, f0, k = card_turn(last, R)
            if tail == 'R':
                f0 = R                                   # echo colour = current last face
            R = step(st, F, a, f0, k, var, rec)
    if regout is not None:
        regout.append(R)
    return st


def make_dm(kind, m):
    return lambda h, d: compose_st(h, em3(kind, m, h, d))


TURNS = {'A': 5, 'B': 6, 'C': 5, 'D': 3}
READS = {'A': 4, 'B': 5, 'C': 5, 'D': 3}     # face look-ups per step (A: 2 per piece; B/C: + edge again; D: 1+1+edge again)


def cost(kind, m):
    var = kind[1]
    steps = 52 + m
    t = TURNS[var] * steps
    rd = TURNS[var] - 1 if var != 'C' else 5
    return dict(steps=steps, turns=t, piece_turn_clicks=(TURNS[var] - 1) * steps,
                card_clicks='130 + sum of echo amounts (echo amount = suit of the held card, so 130 + m*k)',
                face_lookups=READS[var] * steps, pieces_found_per_step=2, regrips=0, solves=3)


# ---------------------------------------------------------------- literal slow transliteration
def slow_em3(kind, m, hpos, deal):
    var, tail = kind[1], kind[2]
    g = hpos
    fc = W._slow_face_carrying

    def turn(g, f, a=1):
        return ref.face_turn(g, f, a)

    def one(g, card, R, colour=None):
        rank, k = card // 4, card % 4 + 1
        if rank < 12:
            face, f0 = (rank + R) % 12, rank
        else:
            face, f0 = ref.OPP[R], 0
        if colour is not None:
            f0 = colour
        g = turn(g, face, k)
        nb = NB[f0]
        i = nb.index(min(nb))
        n, n2 = nb[(i + k - 1) % 5], nb[(i + k) % 5]
        e, c = ref.edge_slot(f0, n), ref.corner_slot(f0, n, n2)
        if var == 'D':
            g = turn(g, fc(g, 'e', e, n))
            x = fc(g, 'c', c, n)
            g = turn(g, x)
            return g, (fc(g, 'e', e, n) + x) % 12
        g = turn(g, fc(g, 'e', e, f0))
        g = turn(g, fc(g, 'e', e, n))
        g = turn(g, fc(g, 'c', c, f0))
        x = fc(g, 'c', c, n)
        g = turn(g, x)
        if var == 'A':
            return g, x
        y = fc(g, 'e', e, n)
        if var == 'B':
            return turn(g, y), y
        return g, (x + y) % 12

    R = 0
    for card in deal[:52]:
        g, R = one(g, card, R)
    for _ in range(m):
        g, R = one(g, deal[51], R, R if tail == 'R' else None)
    return g


def selftest(kinds):
    out = []
    rng = random.Random(20261001 + 3)
    for kind, m in kinds:
        ok = 0
        for _ in range(12):
            h = L.uniform_st(rng)
            d = list(range(52))
            rng.shuffle(d)
            a = eng.as_tuple_pos(eng.from_st(em3(kind, m, h, d)))
            b = slow_em3(kind, m, eng.as_tuple_pos(eng.from_st(h)), d)
            ok += a == b
        assert ok == 12, (kind, m, ok)
        out.append(f'mdw3_lib {kind}{m}: fast == slow literal transliteration on 12/12 random blocks')
    # coverage: the 52 card steps name all 30 edges and 20 corners in every pass (naming is the NRk naming)
    E_ = {NAME[c // 4 if c < 48 else 0][c % 4 + 1][0] for c in range(48)}
    C_ = {NAME[c // 4 if c < 48 else 0][c % 4 + 1][3] for c in range(48)}
    assert len(E_) == 30 and len(C_) == 20
    out.append('mdw3_lib naming: the 48 non-King card steps name 30/30 edges and 20/20 corners (every pass)')
    return out
