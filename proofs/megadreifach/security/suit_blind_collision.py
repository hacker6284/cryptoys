"""Practical IV-anchored collisions of MegaDreifach (current Recipe A grip rule, "v1")
via suit-blind re-grips.  MEASUREMENT on the real hash (repo `md.py`, KAT-checked).

Mechanism (`megadreifach.sudo` `g2_step`): a non-King card turns its held face F by +k
(k = suit + 1), then the noon face by +1, then Front by +1, and only THEN reads the
Recipe A corner (between F, noon and the next neighbour of F).  The noon turn brings
into the read slot a corner from the noon face that was (usually) not on F, so k cannot
influence the read: for about 71.5% of cards all four suits give the same new grip.

Attack: swap two cards of the same rank and different suits.  At distance 2 (cards i and
i+2) this is a 3-card local collision when the grips agree in both orders and the middle
card's turns commute with F: the states rejoin after card i+2, the rest of the block is
identical, and so dm(h, m) = dm(h, m').  Equal-length messages have the same padding,
so a colliding block gives a full Hash collision; a colliding block inside a longer
message gives a second preimage of that message.

Usage (Python 3 standard library only; runs from any directory):
  python3 suit_blind_collision.py              # KATs, verify the recorded pair, suit-blind
                                               # fraction, a 2000-block swap search
  python3 suit_blind_collision.py --search N [--gaps 1-6] [--chained] [--seed S]
        swap search on N random 28-byte blocks; per-distance rates.  --chained swaps
        in the second block of random 2-block messages (a reachable non-IV h).
  python3 suit_blind_collision.py --second-preimage L --targets T [--gaps 2-3]
        for T random targets of L full blocks, look for a colliding swap in any block
  python3 suit_blind_collision.py --variant pre-noon
        the control experiment for the cause: the SAME rule except that the Recipe A
        read moves to right after the held-face turn (remember the colours, then do the
        noon and Front turns, then re-grip).  Runs the suit-blind fraction under both
        rules and a paired swap search at distances 1-4 (same blocks, same swaps) from the IV.
        --variant also applies to --search / --second-preimage.
  python3 suit_blind_collision.py --log  [--full | --variant pre-noon]   # write the log
  python3 suit_blind_collision.py --check [--full | --variant pre-noon]  # fail if stale
  --workers W parallelises; results do not depend on W (per-block seeds).
Exit status is non-zero if a KAT fails, if the recorded pair does not collide or the two
messages are equal, if a reported collision does not re-verify as a Hash collision, or
(--check) if the committed log differs from a fresh run.
Derived from the scripts of an out-of-tree review of candidate grip rules
(exp_suit_blind.py / exp_swap_collisions.py / exp_swap_anatomy.py), keeping only v1.
"""
import argparse, contextlib, io, json, math, os, random, sys, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools'))
from md import (Hash, KATS_JSON, GROUP_ORDER, ROTS, F3_T, compose, face_turn,  # noqa: E402
                f3_step, g2_step, iv_cook12, noon_phys, pad_message, phi_chunk, phi_rank,
                position_to_bytes, recipe_a, spin_about_up)

# The recorded collision (first hit of the original seed-99 search of the review).
M1 = 'e132ebb03ed19b3949820c68d22d8b5004867c3c0ea79f44269e19fb'
M2 = 'e132ebd9724a3c582fca2e7f51a1a34dd82b8afcfcf71344269e19fb'
DIGEST = '0084d6d1e0a4ddb231deb23ac0f4ead7b497eed17f997bfcefa7c34e82'
RANKS, SUITS = 'A23456789TJQK', 'cdhs'
LOG = os.path.join(HERE, 'logs', 'suit_blind_collision.log')
LOG_FULL = os.path.join(HERE, 'logs', 'suit_blind_collision_full.log')
LOG_PRE_NOON = os.path.join(HERE, 'logs', 'suit_blind_collision_pre_noon.log')
IV = iv_cook12()


# ---------------------------------------------------------------- grip-rule variants
#
# 'recipe-a' is the published rule (md.g2_step: held-face turn, noon turn, Front turn,
# THEN the Recipe A read).  'pre-noon' is a control that changes ONLY when the read
# happens: the Recipe A corner (between the held face, its noon and the next
# neighbour, for the grip in force) is read right after the held-face turn (and the
# King spin); the noon and Front turns follow with the old grip, and only then is the
# grip replaced by the remembered reading.  F3 steps and everything else are unchanged.
# It is NOT a proposed rule; it isolates the effect of the read position.

def g2_step_pre_noon(g, o, card):
    rank, suit = card // 4, card % 4
    amt = suit + 1
    held = rank
    if rank < 12:
        g = face_turn(g, o[held], amt)
    else:
        held = 0
        g = face_turn(g, o[held], (5 - amt) % 5)
        o = spin_about_up(o, amt)
    new = recipe_a(g, o[held], o)          # read now, before the noon turn
    noon = noon_phys(o[held], o)
    if noon != o[held]:
        g = face_turn(g, noon, 1)
    g = face_turn(g, o[1], 1)
    return g, new


STEPS = {'recipe-a': g2_step, 'pre-noon': g2_step_pre_noon}


def em_block_v(h, deal, step):
    g = h; o = list(range(12))
    for c in deal[:52]:
        g, o = step(g, o, c)
    for _ in range(F3_T):
        g, o = f3_step(g, o)
    return g


def dm_step(h, deal, variant):
    return compose(h, em_block_v(h, deal, STEPS[variant]))


def hash_of(variant):
    """The full hash under a rule (md.Hash itself for the published rule)."""
    return Hash if variant == 'recipe-a' else (lambda m: hash_v(m, variant))


def hash_v(msg, variant):
    padded, h = pad_message(msg), IV
    for b in range(0, len(padded), 28):
        h = dm_step(h, phi_chunk(padded[b:b + 28]), variant)
    return position_to_bytes(h)


def card_name(c):
    return RANKS[c // 4] + SUITS[c % 4]


def check_kats():
    with open(KATS_JSON) as f:
        kats = json.load(f)
    ok = position_to_bytes(iv_cook12()).hex() == kats['iv_cook12_digest_hex']
    ok &= hex(GROUP_ORDER) == kats['group_order_hex']
    n = sum(Hash(bytes.fromhex(v['msg_hex'])).hex() == v['digest_hex'] for v in kats['vectors'])
    ok &= n == len(kats['vectors'])
    print(f"md.py vs published KATs: {n}/{len(kats['vectors'])} digests, IV digest and |G| "
          f"{'OK' if ok else 'FAIL'}")
    return ok


def grips(deal, upto):
    """Position and grips (Up, Front) after each of the first `upto` cards from IV-COOK12."""
    g, o, out = IV, list(range(12)), []
    for c in deal[:upto]:
        g, o = g2_step(g, o, c)
        out.append((o[0], o[1]))
    return g, out


def verify_pair():
    m1, m2 = bytes.fromhex(M1), bytes.fromhex(M2)
    h1, h2 = Hash(m1).hex(), Hash(m2).hex()
    print(f"recorded pair:\n  M  = {M1}\n  M' = {M2}\n  Hash(M)  = {h1}\n  Hash(M') = {h2}")
    ok = True
    if m1 == m2:
        print('  FAIL: the two messages are equal'); ok = False
    if len(m1) != 28 or len(m2) != 28:
        print('  FAIL: expected two 28-byte messages'); ok = False
    if h1 != h2:
        print('  FAIL: the digests differ'); ok = False
    elif h1 != DIGEST:
        print(f'  FAIL: common digest is not the recorded {DIGEST}'); ok = False
    d1, d2 = phi_chunk(list(m1)), phi_chunk(list(m2))
    diff = [i for i in range(52) if d1[i] != d2[i]]
    swap = (len(diff) == 2 and d1[diff[0]] == d2[diff[1]] and d1[diff[1]] == d2[diff[0]]
            and d1[diff[0]] // 4 == d1[diff[1]] // 4)
    if not swap:
        print(f'  FAIL: the deals are not a same-rank two-card swap (differ at {diff})'); ok = False
    else:
        i, j = diff
        g1, gr1 = grips(d1, j + 1)
        g2, gr2 = grips(d2, j + 1)
        same_first = dm_step(IV, d1, 'recipe-a') == dm_step(IV, d2, 'recipe-a')
        print(f"  deals differ by swapping cards {i+1} and {j+1} ({card_name(d1[i])} <-> "
              f"{card_name(d1[j])}); grips (Up, Front) after cards {i+1}..{j+1}: {gr1[i:]} vs "
              f"{gr2[i:]}; state after card {j+1} equal: {g1 == g2}; first-block dm equal: {same_first}")
        ok &= same_first and g1 == g2
    print('  pair: ' + ('COLLISION VERIFIED (distinct messages, equal Hash)' if ok else 'FAIL'))
    return ok


def perm_parity(p):
    seen, par = [False] * len(p), 0
    for s in range(len(p)):
        if not seen[s]:
            n, t = 0, s
            while not seen[t]:
                seen[t] = True; t = p[t]; n += 1
            par ^= (n - 1) & 1
    return par


def uniform_pos(rng):
    """Exactly uniform legal position."""
    cp = list(range(20)); rng.shuffle(cp)
    if perm_parity(cp): cp[0], cp[1] = cp[1], cp[0]
    ep = list(range(30)); rng.shuffle(ep)
    if perm_parity(ep): ep[0], ep[1] = ep[1], ep[0]
    co = [rng.randrange(3) for _ in range(19)]; co.append((-sum(co)) % 3)
    eo = [rng.randrange(2) for _ in range(29)]; eo.append(sum(eo) % 2)
    return (cp, co, ep, eo)


def suit_blind(trials, seed=3, variant='recipe-a'):
    """P(all four suits of a rank give the same grip) from a uniform state and grip."""
    g2_step = STEPS[variant]
    rng = random.Random(seed)
    blind, tot, nd = [0] * 13, [0] * 13, 0
    for _ in range(trials):
        g = uniform_pos(rng); o = list(ROTS[rng.randrange(60)]); r = rng.randrange(13)
        gs = {tuple(g2_step(g, o, 4 * r + s)[1]) for s in range(4)}
        tot[r] += 1; blind[r] += len(gs) == 1; nd += len(gs)
    per = ' '.join(f"{RANKS[r]}:{blind[r] / tot[r]:.2f}" for r in range(13) if tot[r])
    rule = '' if variant == 'recipe-a' else f', rule {variant}'
    print(f"suit-blind fraction{rule} ({trials} uniform random (state, grip, rank), seed {seed}): "
          f"P(all 4 suits give the same grip) = {sum(blind) / trials:.3f}, mean distinct grips "
          f"over the 4 suits {nd / trials:.2f}\n  per rank {per}")


# ---------------------------------------------------------------- statistics

def poisson_cdf(k, lam):
    term = total = math.exp(-lam)
    for i in range(1, k + 1):
        term *= lam / i; total += term
    return total


def rate_ci(x, n):
    """Exact (Poisson) 95% interval for the rate x/n, as '1/a (95% CI 1/b to 1/c)'."""
    if n == 0:
        return 'no tests'
    def solve(f, target):
        lo, hi = 0.0, max(10.0, 5.0 * x + 10)
        for _ in range(200):
            mid = (lo + hi) / 2
            if f(mid) > target: lo = mid
            else: hi = mid
        return (lo + hi) / 2
    up = solve(lambda l: poisson_cdf(x, l), 0.025)
    low = 0.0 if x == 0 else solve(lambda l: -(1 - poisson_cdf(x - 1, l)), -0.025)
    inv = lambda l: f"1/{n / l:,.0f}" if l > 0 else "0"
    point = f"1/{n / x:,.0f}" if x else "0"
    return f"{point} (95% CI {inv(up)} to {inv(low)})" if x else f"0 (95% CI 0 to {inv(up)})"


# ---------------------------------------------------------------- swap search

def swaps(d, gaps):
    """Same-rank swaps at the given distances that stay in the image of phi."""
    for gap in gaps:
        for i in range(52 - gap):
            j = i + gap
            if d[i] // 4 != d[j] // 4:
                continue
            d2 = d[:]; d2[i], d2[j] = d2[j], d2[i]
            n2 = phi_rank(d2)
            if n2 < 2 ** 224:
                yield gap, i, j, d2, n2


def search_block(task):
    """One random block: returns (per-gap [tests, hits], compressions, hits)."""
    seed, idx, gaps, chained, variant = task
    rng = random.Random(f"sbc:{seed}:{idx}")
    pre = bytes(rng.randrange(256) for _ in range(28)) if chained else b''
    h = dm_step(IV, phi_chunk(list(pre)), variant) if chained else IV
    msg = bytes(rng.randrange(256) for _ in range(28))
    d = phi_chunk(list(msg)); base = dm_step(h, d, variant)
    per, comps, hits = {g: [0, 0] for g in gaps}, 1, []
    for gap, i, j, d2, n2 in swaps(d, gaps):
        per[gap][0] += 1; comps += 1
        if dm_step(h, d2, variant) == base:
            per[gap][1] += 1
            hits.append((pre + msg, pre + n2.to_bytes(28, 'big'), gap, i, j, d[i], d[j]))
    return per, comps, hits


def pmap(fn, tasks, workers):
    if workers > 1:
        with Pool(workers) as p:
            return p.map(fn, tasks, chunksize=max(1, len(tasks) // (workers * 16)))
    return [fn(t) for t in tasks]


def search(blocks, gaps, seed, chained, workers, variant='recipe-a'):
    t0 = time.time()
    H = hash_of(variant)
    res = pmap(search_block, [(seed, k, gaps, chained, variant) for k in range(blocks)], workers)
    per = {g: [0, 0] for g in gaps}; comps = 0; hits = []; hit_blocks = 0; bad = 0
    for p, c, hs in res:
        comps += c; hit_blocks += bool(hs)
        for g in gaps:
            per[g][0] += p[g][0]; per[g][1] += p[g][1]
        for hsx in hs:
            m1, m2 = hsx[0], hsx[1]
            if m1 == m2 or H(m1) != H(m2):
                bad += 1
            hits.append(hsx)
    where = ('second block of random 2-block messages (from h = dm(IV, P))' if chained
             else 'random one-block messages (from IV-COOK12)')
    rule = '' if variant == 'recipe-a' else f'; rule {variant}'
    print(f"swap search: {blocks} {where}, seed {seed}, distances {gaps[0]}..{gaps[-1]}{rule}")
    for g in gaps:
        t, x = per[g]
        print(f"  distance {g}: {x}/{t} same-rank swaps preserve dm; rate {rate_ci(x, t)}")
    T = sum(v[0] for v in per.values()); X = len(hits)
    print(f"  total {X}/{T} (all hits re-verified as distinct-message Hash collisions: "
          f"{'yes' if not bad else f'NO, {bad} failed'}); {hit_blocks}/{blocks} blocks have a hit "
          f"(per-block rate {rate_ci(hit_blocks, blocks)})")
    if X:
        print(f"  compressions: {comps}, per collision {comps / X:,.0f} = 2^{math.log2(comps / X):.1f}")
    for m1, m2, g, i, j, a, b in hits[:3]:
        print(f"  hit: distance {g}, cards {i+1},{j+1} of the last block ({card_name(a)} <-> "
              f"{card_name(b)}): M = {m1.hex()}  M' = {m2.hex()}  Hash = {H(m1).hex()}")
    note_time(t0)
    return bad == 0


# ---------------------------------------------------------------- second preimages

def second_preimage_target(task):
    seed, t, L, gaps, variant = task
    H = hash_of(variant)
    rng = random.Random(f"sbc2:{seed}:{t}")
    msg = bytes(rng.randrange(256) for _ in range(28 * L))
    h, comps = IV, 0
    for b in range(L):
        blk = msg[28 * b:28 * b + 28]
        d = phi_chunk(list(blk)); base = dm_step(h, d, variant); comps += 1
        for gap, i, j, d2, n2 in swaps(d, gaps):
            comps += 1
            if dm_step(h, d2, variant) == base:
                m2 = msg[:28 * b] + n2.to_bytes(28, 'big') + msg[28 * b + 28:]
                ok = m2 != msg and H(m2) == H(msg)
                return (b, gap, comps, ok)
        h = base
    return (None, None, comps, True)


def second_preimages(L, targets, gaps, seed, workers, variant='recipe-a'):
    t0 = time.time()
    res = pmap(second_preimage_target, [(seed, t, L, gaps, variant) for t in range(targets)], workers)
    found = [r for r in res if r[0] is not None]
    bad = sum(not r[3] for r in res)
    comps = sum(r[2] for r in res)
    print(f"second preimages: {targets} random targets of {L} full 28-byte blocks ({28 * L} bytes), "
          f"seed {seed}; each block tested for a same-rank swap at distances {gaps[0]}..{gaps[-1]} "
          f"that preserves dm from its own chaining value"
          + ('' if variant == 'recipe-a' else f"; rule {variant}"))
    print(f"  second preimage found for {len(found)}/{targets} targets (each re-verified as a "
          f"distinct message with equal Hash: {'yes' if not bad else f'NO, {bad} failed'})")
    if found:
        idx = sorted(r[0] + 1 for r in found)
        print(f"  block index of the first vulnerable block: median {idx[len(idx) // 2]}, "
              f"max {idx[-1]}; compressions per target: mean {comps / targets:,.0f}")
    blocks_tested = sum((r[0] + 1) if r[0] is not None else L for r in res)
    print(f"  per-block rate (vulnerable blocks / blocks tested): {rate_ci(len(found), blocks_tested)}")
    note_time(t0)
    return bad == 0


# ---------------------------------------------------------------- driver

QUIET = [False]


def note_time(t0):
    if not QUIET[0]:
        print(f"  ({time.time() - t0:.1f} s)")


def parse_gaps(s):
    a, _, b = s.partition('-')
    return list(range(int(a), int(b or a) + 1))


QUICK = [('search', 2000, '1-3', 99, False)]
FULL = [('search', 40000, '1-6', 99, False),
        ('search', 20000, '1-3', 99, True),
        ('second', 1000, 100, '2-3', 99),
        ('second', 3000, 30, '2-3', 99)]


# The cause control (REPORT §3.4): the same 12,000 IV blocks (the first 12,000 of the
# full run's seed-99 search) and the same distance-1..4
# same-rank swaps under both rules.
PRE_NOON = [('pair-variant', 'pre-noon'),
            ('blind', 'pre-noon'),
            ('search-v', 12000, '1-4', 99, 'recipe-a'),
            ('search-v', 12000, '1-4', 99, 'pre-noon')]


def pair_under(variant):
    m1, m2 = bytes.fromhex(M1), bytes.fromhex(M2)
    H = hash_of(variant)
    same = H(m1) == H(m2)
    print(f"recorded pair under rule {variant}: Hash(M) {'==' if same else '!='} Hash(M')"
          f" ({H(m1).hex()} vs {H(m2).hex()})")


def run_config(config, workers):
    ok = check_kats()
    ok &= verify_pair()
    suit_blind(3000, variant='recipe-a')
    for c in config:
        if c[0] == 'pair-variant':
            pair_under(c[1])
        elif c[0] == 'blind':
            suit_blind(3000, variant=c[1])
        elif c[0] == 'search-v':
            _, n, g, s, v = c
            ok &= search(n, parse_gaps(g), s, False, workers, variant=v)
        elif c[0] == 'search':
            _, n, g, s, ch = c
            ok &= search(n, parse_gaps(g), s, ch, workers)
        else:
            _, L, T, g, s = c
            ok &= second_preimages(L, T, parse_gaps(g), s, workers)
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--search', type=int, default=0, metavar='BLOCKS')
    ap.add_argument('--second-preimage', type=int, default=0, metavar='L')
    ap.add_argument('--targets', type=int, default=50)
    ap.add_argument('--gaps', default=None, help='distances, e.g. 2 or 1-6')
    ap.add_argument('--chained', action='store_true')
    ap.add_argument('--seed', type=int, default=99)
    ap.add_argument('--trials', type=int, default=3000, help='suit-blind trials')
    ap.add_argument('--workers', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--log', action='store_true', help='write the committed log')
    ap.add_argument('--check', action='store_true', help='fail if the committed log is stale')
    ap.add_argument('--full', action='store_true', help='with --log/--check: the report-size runs')
    ap.add_argument('--variant', choices=sorted(STEPS), default='recipe-a',
                    help='grip rule (default: the published Recipe A rule)')
    a = ap.parse_args()
    pre = a.variant == 'pre-noon' and not (a.search or a.second_preimage)
    if a.full and a.variant != 'recipe-a':
        ap.error('--full is for the published rule; use --variant pre-noon alone')
    if a.log or a.check:
        from gencheck import emit
        QUIET[0] = True
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            ok = run_config(PRE_NOON if pre else FULL if a.full else QUICK, a.workers)
        path = LOG_PRE_NOON if pre else LOG_FULL if a.full else LOG
        rc = emit(path, buf.getvalue(), a.check,
                  fix='python3 proofs/megadreifach/security/suit_blind_collision.py --log'
                      + (' --variant pre-noon' if pre else ' --full' if a.full else ''))
        if not ok:
            print('FAIL: a verification in the run failed', file=sys.stderr)
        raise SystemExit(rc or (0 if ok else 1))
    if not (a.search or a.second_preimage):
        raise SystemExit(0 if run_config(PRE_NOON if pre else QUICK, a.workers) else 1)
    ok = check_kats() & verify_pair()
    if a.search:
        ok &= search(a.search, parse_gaps(a.gaps or '1-3'), a.seed, a.chained, a.workers,
                     a.variant)
    if a.second_preimage:
        ok &= second_preimages(a.second_preimage, a.targets, parse_gaps(a.gaps or '2-3'),
                               a.seed, a.workers, a.variant)
    raise SystemExit(0 if ok else 1)


if __name__ == '__main__':
    main()
