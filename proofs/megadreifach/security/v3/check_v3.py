"""MegaDreifach v3: the hand recipe (SPEC v3 §5) agrees with the runnable spec.

Stdlib only.  Evidence, not proof: nothing here is a security claim.

1. `hand_em`, a literal transliteration of SPEC v3 §5.3-§5.4 written from the prose (colours,
   "the face carrying the x-coloured sticker", "count up from the last face by the rank"), on
   m9_search's tuple positions (face-turn and piece tables read out of Em.lean, the v1/v2 tables,
   unchanged in v3), reproduces every vector of primitives/hash/megadreifach/kats/
   megaminx_hash_kats_v3.json.  That file is written by kats/regen_v3.mjs from the sudoc JS build
   of v3/megadreifach.sudo, so this checks prose == sudo on 8 Hash digests, the HashDeck vector
   and 8 HashDeckBody vectors (4 of them with a King held for the echoes).
2. Cost (SPEC v3 §5.6): on the 8 HashDeckBody deals, W makes exactly 468 face turns and
   520 + 26k clicks (k = the held card's suit amount), counted on `hand_em`.
3. The fast engine that the v3 statistics were computed with (study/mdw4_lib.py, kind ZP3F0E,
   m = 26) equals `hand_em` on random blocks (uniform h, random deal; --blocks, default 60).
   Shared primitives: both use m9_search's tables and piece-colour reads, so (3) checks the fast
   engine's compiled tables and stepping, not those primitives (as in ../v2/README.md).

Run from anywhere:  python3 check_v3.py [--blocks N]   (exit 1 on any mismatch)
"""
import argparse
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'm9'))
import m9_search as ref  # noqa: E402

KATS = os.path.join(HERE, '..', '..', '..', '..', 'primitives', 'hash', 'megadreifach', 'kats',
                    'megaminx_hash_kats_v3.json')
ECHOES = 26
CF = [tuple(x) for x in ref.CORNER_FACES]


def face_carrying(g, colours, x):
    """The face now carrying the x-coloured sticker of the piece coloured `colours`."""
    cp, co, ep, eo = g
    if len(colours) == 2:
        piece = ref.edge_slot(*colours)
        slot = ep.index(piece)
        f0, f1 = ref.EDGE_FLAT[2 * slot], ref.EDGE_FLAT[2 * slot + 1]
        a, b = ref.read_colours_piece('e', slot, piece, eo[slot], f0, f1)
        assert x in (a, b)
        return f0 if a == x else f1
    piece = ref.corner_slot(*colours)
    slot = cp.index(piece)
    fs = CF[slot]
    hits = [f for f in fs if ref.colour_on(f, fs[1], fs[2], CF[piece], co[slot]) == x]
    assert len(hits) == 1
    return hits[0]


def named(colour, k):
    """§5.2: around `colour`, start at its lowest-ranked neighbour (Clubs) and go clockwise;
    the suit amount k picks n; the edge is (colour, n), the corner (colour, n, next clockwise)."""
    nb = list(ref.NBRS[colour])
    i = nb.index(min(nb))
    return nb[(i + k - 1) % 5], nb[(i + k) % 5]


def step(g, last, rank, k, colour):
    """§5.3 steps 1-5. Returns (position, new last face)."""
    face = ref.OPP[last] if rank == 12 else (last + rank) % 12      # 1. count up (King: opposite)
    g = ref.face_turn(g, face, k)
    n, n2 = named(colour, k)                                          # 2. name
    g = ref.face_turn(g, face_carrying(g, (colour, n), colour), 1)    # 3. edge
    g = ref.face_turn(g, face_carrying(g, (colour, n), n), 1)
    g = ref.face_turn(g, face_carrying(g, (colour, n, n2), colour), 1)  # 4. corner
    g = ref.face_turn(g, face_carrying(g, (colour, n, n2), n), 1)
    last = face_carrying(g, (colour, n), n)                           # 5. edge again
    return ref.face_turn(g, last, 1), last


def hand_em(h, deal):
    """W·h: 52 card steps from the Ace face, then 26 echoes of the held card 52 (§5.4)."""
    g, last = h, 0
    for card in deal:
        rank, k = card // 4, card % 4 + 1
        g, last = step(g, last, rank, k, rank if rank < 12 else 0)
    rank, k = deal[51] // 4, deal[51] % 4 + 1
    c = rank if rank < 12 else 0
    n, n2 = named(c, k)
    for _ in range(ECHOES):
        x = face_carrying(g, (c, n), n)            # held edge's n-sticker
        y = face_carrying(g, (c, n, n2), n)        # held corner's n-sticker
        p = (x + y) % 12                           # X counted up by Y's rank
        g, last = step(g, p, rank, k, p)
    return g


def iv():
    h = ref.ID
    for f in range(12):
        h = ref.face_turn(h, f, 1)
    return h


def hash_v3(msg):
    h = iv()
    m = ref.pad(msg)
    for b in range(0, len(m), 28):
        deal = ref.phi_unrank(int.from_bytes(bytes(m[b:b + 28]), 'big'))
        h = ref.compose(h, hand_em(h, deal))
    return ref.to_bytes(h)


def body_v3(deal):
    h = iv()
    return ref.to_bytes(ref.compose(h, hand_em(h, deal)))


def check_kats():
    k = json.load(open(KATS))
    assert k['version'] == 'v3' and k['echoes'] == ECHOES
    n = 0
    for v in k['vectors']:
        assert hash_v3(bytes.fromhex(v['msg_hex'])).hex() == v['digest_hex'], v['name']
        n += 1
    assert hash_v3(bytes(28)).hex() == k['hash_deck']['digest_hex']
    assert ref.to_bytes(iv()).hex() == k['iv_cook12_digest_hex']
    kings = 0
    for v in k['body_vectors']:
        assert body_v3(v['deal_ids']).hex() == v['digest_hex'], v['deal_ids'][:4]
        kings += v['deal_ids'][51] >= 48
    nb = len(k['body_vectors'])
    print(f'check_v3: SPEC v3 §5 hand transliteration reproduces the {n} Hash digests, the HashDeck vector, '
          f'the IV-COOK12 digest and the {nb} HashDeckBody vectors ({kings} with a King held) of '
          f'megaminx_hash_kats_v3.json (written from the sudo)')


def check_cost():
    k = json.load(open(KATS))
    real = ref.face_turn
    tally = [0, 0]

    def counted(g, f, n):
        tally[0] += 1
        tally[1] += n
        return real(g, f, n)
    h0 = iv()
    ref.face_turn = counted
    try:
        for v in k['body_vectors']:
            tally[:] = [0, 0]
            d = v['deal_ids']
            hand_em(h0, d)
            assert tally == [468, 520 + 26 * (d[51] % 4 + 1)], (tally, d[51])
    finally:
        ref.face_turn = real
    print(f"check_v3: cost on the {len(k['body_vectors'])} HashDeckBody deals: 468 face turns and 520 + 26k clicks "
          '(k = held suit amount) per block')


def check_fast(blocks):
    sys.path.insert(0, os.path.join(HERE, 'study'))
    import mdfix_lib as L  # noqa: E402
    import mdw4_lib as Z  # noqa: E402
    eng = L.eng
    rng = random.Random(20261002)
    ok = 0
    for _ in range(blocks):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        fast = eng.as_tuple_pos(eng.from_st(Z.em4('ZP3F0E', ECHOES, h, d)))
        slow = hand_em(eng.as_tuple_pos(eng.from_st(h)), d)
        ok += fast == eng.as_tuple_pos(slow)
    assert ok == blocks, (ok, blocks)
    print(f'check_v3: study fast engine (mdw4_lib ZP3F0E, m = 26) == hand transliteration on {ok}/{blocks} '
          'random blocks (seed 20261002)')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--blocks', type=int, default=60)
    a = ap.parse_args()
    check_kats()
    check_cost()
    check_fast(a.blocks)
