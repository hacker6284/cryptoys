"""Scramble digest encoding: is position -> digest injective on the cube group G?

SPEC 'Digest': edge orientation bit = 0 iff the first-axis sticker is W, Y, R or O.
For the four edge pieces RW, OW, RY, OY BOTH stickers are in {W,Y,R,O}, so their flip is
invisible. This script (computed):
  1. builds solved and solved-with-RW-and-OW-flipped (a legal 2-flip), shows equal digests;
  2. reaches the flipped state by a real v2 message: preimage machinery of scramble_attack
     is not needed -- we exhibit two MESSAGES with equal digest whose seated final cubes
     differ (so the collision is in the encoding, not in the walk);
  3. counts preimages per digest exactly: k = 16 if slot 11 holds a non-ambiguous piece,
     8 if it holds an ambiguous one; image size |G|/12.
Stage-3 review script (PYTHONDONTWRITEBYTECODE=1).
"""
import math, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scramble_ref as S
import scramble_attack as A

def flip(state, pos):
    s = list(state)
    a, b = [S.SIDX[x] for x in S.SLOTS if x[0] == pos]
    s[a], s[b] = s[b], s[a]
    return tuple(s)

def main():
    print('[1] encoding check on hand-built states')
    s0 = S.SOLVED
    s1 = flip(flip(s0, (1, 1, 0)), (-1, 1, 0))     # flip RW (slot UR) and OW (slot UL)
    s2 = flip(flip(s0, (1, 1, 0)), (0, 1, 1))      # flip RW and GW (control)
    d0, d1, d2 = (S.digest_of_seated(x) for x in (s0, s1, s2))
    print(f'  solved            digest {d0:017X}  facelets {S.facelets(s0)}')
    print(f'  RW+OW flipped     digest {d1:017X}  facelets {S.facelets(s1)}')
    print(f'  RW+GW flipped     digest {d2:017X}  (control: GW flip is visible)')
    print(f'  distinct states with equal digest: {s0 != s1 and d0 == d1}')
    print('[2] a real message pair: M1 = preimage of the solved-seated... skipped; instead')
    print('    take M = b"hello" and the state that differs from its seated pose by the RW+OW flip;')
    s, _ = S.hash_v2_state(b'hello'); seated = S.close_and_seat(s)
    # locate RW and OW pieces in the seated pose and flip them
    locs = []
    for pos, axes in S.ESLOT:
        cols = {seated[S.SIDX[(pos, a)]] for a in axes}
        if cols in ({S.R, S.W}, {S.O, S.W}):
            locs.append(pos)
    seated2 = seated
    for pos in locs:
        seated2 = flip(seated2, pos)
    print(f'    seated(hello) digest {S.digest_of_seated(seated):017X}; flipped pose digest {S.digest_of_seated(seated2):017X}; poses differ: {seated != seated2}')
    tgt = A.prepad_states_from_seated(seated2)[0]
    rng = random.Random(7)
    m = A.attack_preimage(tgt, 42, rng, lambda x: print('   ', x))
    if m is not None:
        s3, _ = S.hash_v2_state(m); seat3 = S.close_and_seat(s3)
        print(f'    M = {m.hex()}')
        print(f'    digest(M) = {S.evaluate(m)[0]}, digest(hello) = {S.evaluate(b"hello")[0]}; '
              f'seated poses differ: {seat3 != seated}; seat(M) == flipped pose: {seat3 == seated2}')
    print('[3] preimages per digest value (exact count)')
    amb = [{S.R, S.W}, {S.O, S.W}, {S.R, S.Y}, {S.O, S.Y}]
    amb_ids = [S.EPIECE.index(x) for x in amb]
    # k = 2^(#ambiguous pieces in slots 0..10); slot 11 flip fixed by parity
    p11 = len(amb_ids) / 12
    k_avg_inv = p11 / 8 + (1 - p11) / 16
    print(f'    ambiguous edge pieces: {sorted(amb_ids)}; P(slot 11 holds one) = {p11:.4f}')
    print(f'    image size = |G| * {k_avg_inv:.6f} = |G|/{1 / k_avg_inv:.1f} = 2^{math.log2(S.GROUP * k_avg_inv):.3f} (|G| = 2^{math.log2(S.GROUP):.3f})')
    print(f'    generic birthday on the image: ~2^{math.log2(S.GROUP * k_avg_inv) / 2:.2f}')
    # empirical check of the per-state preimage count on random states reached by random messages
    rng = random.Random(11); cnt = {}
    for _ in range(300):
        m = bytes(rng.randrange(256) for _ in range(8))
        st, _ = S.hash_v2_state(m); se = S.close_and_seat(st)
        # enumerate all flips of the 4 ambiguous pieces with even total parity
        base = S.digest_of_seated(se); pos_amb = []
        for pos, axes in S.ESLOT:
            cols = {se[S.SIDX[(pos, a)]] for a in axes}
            if cols in amb: pos_amb.append(pos)
        others = [pos for pos, _ in S.ESLOT if pos not in pos_amb]
        same = 0
        # candidates: flip any subset of ambiguous pieces, plus the slot-11 piece if needed for parity
        import itertools
        s11 = S.ESLOT[11][0]
        for r in range(5):
            for sub in itertools.combinations(pos_amb, r):
                x = se
                for p in sub: x = flip(x, p)
                if len(sub) % 2 == 1:
                    if s11 in pos_amb: continue      # parity would need another ambiguous flip: covered by other subsets
                    x = flip(x, s11)
                if S.digest_of_seated(x) == base: same += 1
        cnt[same] = cnt.get(same, 0) + 1
    print(f'    300 random 8-byte messages: legal states sharing the digest (incl. itself) -> {cnt}')

if __name__ == '__main__':
    main()
