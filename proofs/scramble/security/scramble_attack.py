"""Structural attacks on Scramble v2: the corner+frame sub-state is autonomous.

OBSERVATION (proved on paper in REPORT.md §2): face turns never mix corners with edges;
Rule B reads only the corner cubie in slot (1,1,1) and the centre positions (the frame).
So (corner stickers, centre stickers) evolve on their own, a set of at most
24 * (8!/2) * 3^7 ~ 2^29.98 states (corner permutations are even; REPORT.md P4), and the
edge stickers are only permuted by a map that depends on (nybble, corner state), never on
the edges.

ATTACKS (all end-to-end, every result re-verified with the engine's full evaluate(); the
sudoc-generated JS re-check is scramble_sudo_check.mjs):
  collision  : Joux multicollision on the 2^29.98 corner chain (t stages of 8-nybble blocks),
               then a birthday search over the 2^t edge outcomes (edge space ~2^38.8).
  second     : second preimage of a random 64-byte message.
  preimage   : preimage of a given digest (default: the SPEC KAT digest of b'hello').
               t stages, a corner meet-in-the-middle bridge to the target corner state,
               then a meet-in-the-middle on the edge outcomes (2^(t/2) per side).
Work is counted in "nybble steps" (one symbol = two quarter turns + Rule B); corner-only
steps are counted as full steps (an over-count). Reference costs: one v2 hash of a
>= 11-nybble message is >= 12 nybble steps.
Stage-3 review script (PYTHONDONTWRITEBYTECODE=1). Seeded; deterministic. Write-up: REPORT.md.
"""
import argparse, math, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scramble_ref as S

CS = S.CENTER_SLOTS + S.CORNER_SLOTS          # corner sub-state slots (30)
ES = S.EDGE_SLOTS                             # edge slots (24)
CPOS = {s: k for k, s in enumerate(CS)}
EPOS = {s: k for k, s in enumerate(ES)}

def gather(perm, sub, pos):
    """perm: slot i -> slot perm[i]. Return g with new[k] = old[g[k]] on the sub-slots."""
    inv = [0] * 54
    for i, j in enumerate(perm):
        inv[j] = i
    return tuple(pos[inv[s]] for s in sub)

def compose_perm(p, q):  # first p then q
    return tuple(q[p[i]] for i in range(54))

TURN = []
for n in range(16):
    a, b = S.V2[n]
    TURN.append(compose_perm(S.QT[a], S.QT[b]))
TURN_C = [gather(p, CS, CPOS) for p in TURN]
TURN_E = [gather(p, ES, EPOS) for p in TURN]
ROTS = list(S.ROT.items())
ROT_C = [gather(p, CS, CPOS) for _, p in ROTS]
ROT_E = [gather(p, ES, EPOS) for _, p in ROTS]
RIDX = {k: i for i, (k, _) in enumerate(ROTS)}
def inv_g(g):
    out = [0] * len(g)
    for k, j in enumerate(g):
        out[j] = k
    return tuple(out)
TURN_C_INV = [inv_g(g) for g in TURN_C]
ROT_C_INV = [inv_g(g) for g in ROT_C]
UP_K, FR_K = CPOS[S.UFR_UP], CPOS[S.UFR_FR]
CENTER_AXIS = [S.SLOTS[s][0] for s in S.CENTER_SLOTS]   # CS[0..5] are the centres

def rot_index(c):
    up, fr = c[UP_K], c[FR_K]
    e = t = None
    for k in range(6):
        if c[k] == up: e = CENTER_AXIS[k]
        if c[k] == fr: t = CENTER_AXIS[k]
    return RIDX[(e, t)]

STEPS = [0]
def cstep(c, n):
    g = TURN_C[n]; c = tuple([c[j] for j in g])
    r = ROT_C[rot_index(c)]; STEPS[0] += 1
    return tuple([c[j] for j in r])

def cstep_inv(y, n):
    for ri in range(24):
        g = ROT_C_INV[ri]; z = tuple([y[j] for j in g])
        if rot_index(z) == ri:
            gi = TURN_C_INV[n]; STEPS[0] += 1
            return tuple([z[j] for j in gi])
    raise AssertionError('Rule B not invertible?')

def run_block(c, block):
    """corner state after the block, and the composed edge gather of the block"""
    ge = tuple(range(24))
    for n in block:
        g = TURN_C[n]; c = tuple([c[j] for j in g])
        ri = rot_index(c); r = ROT_C[ri]; c = tuple([c[j] for j in r])
        te = TURN_E[n]; ge = tuple([ge[j] for j in te])
        re = ROT_E[ri]; ge = tuple([ge[j] for j in re])
        STEPS[0] += 1
    return c, ge

def cfinal(c, block):
    for n in block:
        c = cstep(c, n)
    return c

def split(state):
    return tuple(state[s] for s in CS), tuple(state[s] for s in ES)

def stage(c, rng, L=8):
    seen = {}
    tries = 0
    while True:
        blk = tuple(rng.randrange(16) for _ in range(L)); tries += 1
        end = cfinal(c, blk)
        o = seen.get(end)
        if o is not None and o != blk:
            c1, g1 = run_block(c, o); c2, g2 = run_block(c, blk)
            assert c1 == c2 == end
            return o, blk, g1, g2, end, tries
        seen[end] = blk

def joux(c0, t, rng, log):
    stages = []; c = c0; tries = []
    for i in range(t):
        b1, b2, g1, g2, c, n = stage(c, rng)
        stages.append((b1, b2, g1, g2)); tries.append(n)
    log(f"  {t} corner-collision stages: blocks tried per stage mean {sum(tries) / t:.0f} "
        f"(2^{math.log2(sum(tries) / t):.2f}), min {min(tries)}, max {max(tries)}; "
        f"sqrt(pi/2 * 24*(8!/2)*3^7) = {math.sqrt(math.pi / 2 * 24 * 20160 * 2187):.0f} "
        f"(2^{math.log2(math.pi / 2 * 24 * 20160 * 2187) / 2:.2f})")
    return stages, c

EG = [0]
def apply_g(e, g):
    EG[0] += 1
    return tuple([e[j] for j in g])
def apply_g_inv(e, g):
    EG[0] += 1
    out = [0] * len(g)
    for k, j in enumerate(g):
        out[j] = e[k]
    return tuple(out)

def enumerate_forward(e0, stages):
    """dict edge-state -> choice bits, over all 2^len(stages) choices (DFS)"""
    table = {}
    def rec(e, i, bits):
        if i == len(stages):
            table.setdefault(bytes(e), bits); return
        rec(apply_g(e, stages[i][2]), i + 1, bits)
        rec(apply_g(e, stages[i][3]), i + 1, bits | (1 << i))
    rec(e0, 0, 0)
    return table

def message_from(stages, bits, extra=()):
    ny = []
    for i, st in enumerate(stages):
        ny += st[1] if (bits >> i) & 1 else st[0]
    ny += list(extra)
    assert len(ny) % 2 == 0
    return bytes((ny[k] << 4) | ny[k + 1] for k in range(0, len(ny), 2))

def attack_collision(t, rng, log):
    c0, e0 = split(S.SOLVED)
    stages, _ = joux(c0, t, rng, log)
    table = {}; found = None
    def rec(e, i, bits):
        nonlocal found
        if found: return
        if i == t:
            k = bytes(e); o = table.get(k)
            if o is not None and o != bits: found = (o, bits)
            table.setdefault(k, bits); return
        rec(apply_g(e, stages[i][2]), i + 1, bits)
        rec(apply_g(e, stages[i][3]), i + 1, bits | (1 << i))
    rec(e0, 0, 0)
    log(f"  edge birthday: {len(table)} edge outcomes stored before the first match")
    if not found: return None
    return message_from(stages, found[0]), message_from(stages, found[1])

def bridge(c_from, c_to, rng, log, a=4, b=4):
    """corner MITM: forward all 16^a blocks from c_from, backward all 16^b from c_to"""
    import itertools
    fw = {}
    for blk in itertools.product(range(16), repeat=a):
        fw.setdefault(cfinal(c_from, blk), blk)
    hits = []
    for blk in itertools.product(range(16), repeat=b):
        y = c_to
        for n in reversed(blk):
            y = cstep_inv(y, n)
        if y in fw:
            hits.append(fw[y] + blk)
    log(f"  corner bridge {a}+{b} nybbles: {len(fw)} distinct forward ends, {len(hits)} meets")
    return hits

def attack_preimage(target_state, t, rng, log):
    """message M (>= 11 nybbles, even) whose pre-padding state equals target_state"""
    c0, e0 = split(S.SOLVED)
    cT, eT = split(target_state)
    stages, ct = joux(c0, t, rng, log)
    hits = []
    a = 4
    while not hits:
        hits = bridge(ct, cT, rng, log, a, a)
        a += 1
    br = hits[0]
    cchk, gb = run_block(ct, br)
    assert cchk == cT
    estar = apply_g_inv(eT, gb)            # edge state needed right after the t stages
    h = t // 2
    lo = enumerate_forward(e0, stages[:h])
    log(f"  edge MITM: {len(lo)} forward edge outcomes (2^{math.log2(len(lo)):.2f})")
    hi_stages = stages[h:]
    res = None
    def rec(e, i, bits):
        nonlocal res
        if res: return
        if i < 0:
            o = lo.get(bytes(e))
            if o is not None: res = o | (bits << h)
            return
        rec(apply_g_inv(e, hi_stages[i][2]), i - 1, bits)
        rec(apply_g_inv(e, hi_stages[i][3]), i - 1, bits | (1 << i))
    rec(estar, len(hi_stages) - 1, 0)
    if res is None:
        return None
    return message_from(stages, res, br)

def state_from_digest(dg, frame=0):
    """one of the 24 pre-padding states whose closer+seat gives digest dg"""
    # build the seated cube from the digest by searching is not needed: we invert from a
    # known seated pose. Here the digest must come with its seated pose (see main()).
    raise NotImplementedError

def prepad_states_from_seated(seated):
    """all 24 pre-padding states (long-message padding = one marker nybble 8)"""
    out = []
    for (_, p) in S.ROT.items():
        inv = [0] * 54
        for i, j in enumerate(p): inv[j] = i
        s = S.apply(seated, tuple(inv))              # undo a whole-cube rotation
        s = S.turns(s, 'B', 2); s = S.turns(s, 'F', 2)   # undo B2 then F2
        # undo symbol 8 = F then U then Rule B
        for (_, r) in S.ROT.items():
            rinv = [0] * 54
            for i, j in enumerate(r): rinv[j] = i
            z = S.apply(s, tuple(rinv))
            if S.rot_for(z, z[S.UFR_UP], z[S.UFR_FR]) == r:
                break
        else:
            raise AssertionError
        z = S.turns(z, 'U', 3); z = S.turns(z, 'F', 3)
        assert S.close_and_seat(S.v2_symbol(z, 8)) == seated
        out.append(z)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['collision', 'second', 'preimage'])
    ap.add_argument('--t', type=int, default=None)
    ap.add_argument('--seed', type=int, default=20260930)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    log = lambda s: print(s, flush=True)
    assert S.selfcheck(verbose=False), 'reference KATs failed'
    log(f"[{args.mode}] seed {args.seed}; reference self-check: 10/10 SPEC KATs ok")
    t0 = time.time(); STEPS[0] = 0
    if args.mode == 'collision':
        t = args.t or 22
        r = attack_collision(t, rng, log)
        if r is None:
            log('  no edge match; rerun with larger --t'); return 1
        m1, m2 = r
        d1, d2 = S.evaluate(m1), S.evaluate(m2)
        log(f"  m1 = {m1.hex()}\n  m2 = {m2.hex()}")
        log(f"  distinct: {m1 != m2}; len {len(m1)} bytes; digests {d1[0]} {d2[0]}; COLLISION VERIFIED: {m1 != m2 and d1[0] == d2[0]}")
    else:
        t = args.t or 42
        if args.mode == 'second':
            target = bytes(rng.randrange(256) for _ in range(64))
            st, _ = S.hash_v2_state(target)
            # pre-padding state of a >= 11-nybble message = state after its own nybbles
            s = S.SOLVED
            for n in S.nybbles(target): s = S.v2_symbol(s, n)
            tgt_state, tgt_digest, what = s, S.evaluate(target)[0], f"target message {target.hex()}"
        else:
            s, _ = S.hash_v2_state(b'hello')
            seated = S.close_and_seat(s)
            tgt_digest = S.evaluate(b'hello')[0]
            cands = prepad_states_from_seated(seated)
            tgt_state, what = cands[0], f"digest {tgt_digest} (SPEC KAT of b'hello'; only the seated pose/digest is used)"
            target = b'hello'
        log(f"  target: {what}")
        m = attack_preimage(tgt_state, t, rng, log)
        if m is None:
            log('  no edge match; rerun with larger --t'); return 1
        d = S.evaluate(m)[0]
        log(f"  found M = {m.hex()} ({len(m)} bytes)")
        log(f"  digest(M) = {d}; target digest = {tgt_digest}; M != target: {m != target}; "
            f"{'SECOND PREIMAGE' if args.mode == 'second' else 'PREIMAGE'} VERIFIED: {d == tgt_digest and m != target}")
    el = time.time() - t0
    import resource
    log(f"  peak RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024:.0f} MB")
    log(f"  work: {STEPS[0]} nybble steps = 2^{math.log2(STEPS[0]):.2f} (corner-only steps counted as full); "
        f"~2^{math.log2(STEPS[0] / 12):.2f} twelve-step hash equivalents; plus {EG[0]} = 2^{math.log2(max(EG[0], 1)):.2f} edge-only "
        f"permutation applications (24 entries each; each cheaper than one nybble step); wall {el:.0f} s (single Python process)")
    return 0

if __name__ == '__main__':
    sys.exit(main())
