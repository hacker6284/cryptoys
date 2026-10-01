"""Scramble v2: digest -> seated pose decoder, and a preimage from the digest HEX alone.

Removes the caveat of `scramble_attack.py preimage`, which obtained the target's seated pose by
hashing b'hello'. Here the target is only a 17-hex-digit digest string (default: the SPEC v2
KAT digest of b'cube', 132FDCE0BF26E5898); no message is hashed to get the pose.
COMPUTED checks:
  1. corner-twist sum = 0 mod 3 and standard edge-flip sum = 0 mod 2 on 2000 random reachable
     states (validates the invariants the decoder uses);
  2. decode(digest(s)) round-trips (equal digest, legal) for 2000 random reachable states;
  3. preimage of the given digest: decode -> 24 pre-padding states -> attack_preimage ->
     verify with the engine's full evaluate().
Stage-3 review script (PYTHONDONTWRITEBYTECODE=1). Seeded.
"""
import itertools, math, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scramble_ref as S
import scramble_attack as A
W, Y, R, O, B, G = S.W, S.Y, S.R, S.O, S.B, S.G

# canonical cyclic colour tuple of each corner piece, read in its home slot's axis order
HOME_C = []
for k, piece in enumerate(S.CPIECE):
    pos, axes = next((p, a) for p, a in S.CSLOT if {S.SOLVED[S.SIDX[(p, x)]] for x in a} == piece)
    HOME_C.append(tuple(S.SOLVED[S.SIDX[(pos, x)]] for x in axes))

def unrank(r, n):
    items = list(range(n)); out = []
    for i in range(n - 1, -1, -1):
        f = math.factorial(i); q, r = divmod(r, f); out.append(items.pop(q))
    return out

def parity(p):
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j]) % 2

def true_flip(cols):
    """standard edge orientation: reference sticker W/Y if present else G/B; reference axis = first
    listed slot axis (+-Y for U/D-layer slots, +-Z for middle-layer slots). 0 iff ref on ref axis."""
    ref = [c for c in cols if c in (W, Y)] or [c for c in cols if c in (G, B)]
    return 0 if cols[0] == ref[0] else 1

def invariants(s):
    tw = sum(next(k for k, c in enumerate([s[S.SIDX[(p, a)]] for a in ax]) if c in (W, Y)) for p, ax in S.CSLOT) % 3
    fl = sum(true_flip([s[S.SIDX[(p, a)]] for a in ax]) for p, ax in S.ESLOT) % 2
    cp = [S.CPIECE.index({s[S.SIDX[(p, a)]] for a in ax}) for p, ax in S.CSLOT]
    ep = [S.EPIECE.index({s[S.SIDX[(p, a)]] for a in ax}) for p, ax in S.ESLOT]
    return tw, fl, parity(cp), parity(ep)

def build(cp, co, ep, eflip_first):
    s = list(S.SOLVED)
    for (pos, axes), piece, t in zip(S.CSLOT, cp, co):
        tup = HOME_C[piece]; k = next(i for i, c in enumerate(tup) if c in (W, Y))
        rot = tup[k:] + tup[:k]                      # W/Y first, cyclic order kept
        rot = rot[-t:] + rot[:-t] if t else rot       # W/Y moved to index t
        for a, c in zip(axes, rot): s[S.SIDX[(pos, a)]] = c
    for (pos, axes), piece, first in zip(S.ESLOT, ep, eflip_first):
        cols = sorted(S.EPIECE[piece]); cols = cols if cols[0] == first else cols[::-1]
        for a, c in zip(axes, cols): s[S.SIDX[(pos, a)]] = c
    return tuple(s)

def decode(dg):
    """one legal seated state with digest dg (None if dg is not in the image)"""
    v = dg
    eo = [(v >> i) & 1 for i in range(11)]; v >>= 11
    v, epr2 = divmod(v, 239500800)
    cpr, cor = divmod(v, 2187)
    cp = unrank(cpr, 8)
    co7 = [(cor // 3 ** i) % 3 for i in range(7)]
    for c8, epr in itertools.product(range(3), (2 * epr2, 2 * epr2 + 1)):
        ep = unrank(epr, 12)
        if parity(ep) != parity(cp): continue
        co = co7 + [c8]
        if sum(co) % 3: continue
        opts = []
        for i, piece in enumerate(ep):
            cols = sorted(S.EPIECE[piece])
            bit = eo[i] if i < 11 else None
            cand = []
            for first in cols:
                b = 0 if first in (W, Y, R, O) else 1
                if bit is None or b == bit: cand.append(first)
            opts.append(cand)
        for firsts in itertools.product(*opts):
            s = build(cp, co, ep, firsts)
            if S.digest_of_seated(s) == dg and invariants(s) == (0, 0, parity(cp), parity(cp)):
                return s
    return None

def random_state(rng, n=40):
    s = S.SOLVED
    for _ in range(n): s = S.turns(s, rng.choice('UDLRFB'), rng.choice((1, 2, 3)))
    return s

def main():
    hexdg = sys.argv[1] if len(sys.argv) > 1 else '132FDCE0BF26E5898'
    rng = random.Random(20260930)
    log = lambda x: print(x, flush=True)
    assert S.selfcheck(verbose=False)
    bad = 0
    for _ in range(2000):
        tw, fl, pc, pe = invariants(random_state(rng))
        bad += (tw != 0) or (fl != 0) or (pc != pe)
    log(f"[1] invariants on 2000 random face-turn states: violations {bad}")
    ok = 0
    for _ in range(2000):
        s = random_state(rng); d = S.digest_of_seated(s); z = decode(d)
        ok += z is not None and S.digest_of_seated(z) == d
    log(f"[2] decode round-trip on 2000 random states: {ok}/2000")
    dg = int(hexdg, 16)
    t0 = time.time(); A.STEPS[0] = 0
    seated = decode(dg)
    assert seated is not None
    log(f"[3] target digest {hexdg} (hex only; no message hashed). decoded pose facelets {S.facelets(seated)}")
    cands = A.prepad_states_from_seated(seated)
    m = A.attack_preimage(cands[0], 42, rng, log)
    d = S.evaluate(m)[0]
    log(f"    found M = {m.hex()} ({len(m)} bytes)")
    log(f"    digest(M) = {d}; PREIMAGE OF {hexdg} VERIFIED: {d == hexdg.upper()}")
    import resource
    st = A.STEPS[0]
    log(f"    work {st} nybble steps = 2^{math.log2(st):.2f}; wall {time.time() - t0:.0f} s; "
        f"peak RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024:.0f} MB")

if __name__ == '__main__':
    main()
