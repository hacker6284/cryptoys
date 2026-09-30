"""MegaDreifach v2 (C36) attack and structure experiments behind SPEC §8 (write-or-check logs).

Stdlib only.  Every experiment is seeded and deterministic, and its result does not depend
on --workers (the work is split into a fixed number of chunks with per-chunk seeds, as in
the grip-rule review whose scripts these are ported from; see README.md).  The engine
self-check (engine.selfcheck: 8 v2 KATs, HashDeck, fast == slow reference) runs first, and
nothing runs if it fails.  Results are empirical evidence, not proofs of security.

    python3 experiments.py --check              # quick set (CI proofs.yml; about 1 s in CI)
    python3 experiments.py --check --set heavy  # report-size runs (CI proofs-heavy.yml)
    python3 experiments.py [--set quick|heavy|all] [--only NAME ...]   # (re)write logs/
    python3 experiments.py --list

Exit status is non-zero if the self-check fails, an experiment's own verification fails
(e.g. a reported pair does not re-verify), or (--check) a committed log differs from a
fresh run.
"""
import argparse
import contextlib
import io
import itertools
import math
import os
import random
import sys
import time
from collections import Counter, defaultdict
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', '..', 'tools'))
from engine import (IV_ST, LIM, RULES, Hash, HashDeckBodyFrom, ci95,  # noqa: E402
                    compose_st, engine,
                    from_st, inverse, legal, perm_parity, phi_chunk, phi_rank, position_to_bytes,
                    rand_deal, read_hslots, ref_body_from, ref_hash, selfcheck, to_st, uniform_st,
                    as_tuple_pos)
import engine as eng  # noqa: E402

LOGS = os.path.join(HERE, 'logs')
NAMES = 'A23456789TJQK'
VERIFY_FAIL = []          # experiments append a message when their own verification fails


def fail(msg):
    VERIFY_FAIL.append(msg)
    print('  FAIL: ' + msg)


def pmap(fn, tasks, workers):
    if workers > 1:
        with Pool(workers) as p:
            return p.map(fn, tasks, chunksize=1)
    return [fn(t) for t in tasks]


def rate_text(k, n):
    """Rate k/n with ci95 (Wilson; for k = 0 the exact one-sided 95% upper bound).  The
    same_blocks log uses ../suit_blind_collision.py's rate_ci (exact Poisson) instead, so
    that it reads like the v1 log it re-runs; the two formats are kept because every
    committed log is byte-for-byte evidence."""
    lo, hi = ci95(k, n)
    if k == 0:
        return f"95% upper bound {hi:.1e} (=1/{1 / hi:,.0f})"
    return f"= 1/{n / k:,.0f}, 95% CI [{lo:.1e},{hi:.1e}]"


# ================================================================ quick experiments

def x_selfcheck(workers):
    """Engine self-check (also run before every other experiment)."""
    print('\n'.join(selfcheck()))


def _v1_counts(deal):
    """v1 (../md.py) one block from IV-COOK12: face turns, clicks, pieces read (calls of
    md.colours_at) and re-grips (calls of md.recipe_a), counted by wrapping the two."""
    import md as v1
    calls = Counter()
    orig = v1.colours_at, v1.recipe_a

    def colours_at(*a):
        calls['read'] += 1
        return orig[0](*a)

    def recipe_a(*a):
        calls['regrip'] += 1
        return orig[1](*a)

    v1.colours_at, v1.recipe_a = colours_at, recipe_a
    try:
        tr = []
        v1.em_block(v1.iv_cook12(), deal, trace=tr)
    finally:
        v1.colours_at, v1.recipe_a = orig
    return len(tr), sum(a % 5 for f, a in tr), calls['read'], calls['regrip']


def x_cost(workers):
    """SPEC §5.7 / §8 cost per block: face turns, clicks, pieces read, re-grips (review T8)."""
    rng = random.Random(8)
    deals = [rand_deal(rng) for _ in range(100)]
    rows = [('v1', 12, {_v1_counts(d) for d in deals})]
    for rule in ('A_vn', 'C36', 'C76'):
        E = engine(rule)
        counts = set()
        for d in deals:
            tr, rec, grips = [], [], []
            E.em(IV_ST, d, trace=tr, rec=rec, grips=grips)
            counts.add((len(tr), sum(a % 5 for f, a in tr), len(rec), len(grips)))
        rows.append((rule, E.t, counts))
    print('100 random one-block deals from IV-COOK12 (seed 8); every count is the same for all 100 '
          '(each deal holds every card once).  v1 turns from ../md.py (v1 sudo), '
          'v1 reads = 52 + 12.')
    base = None
    turns_reads = {}
    for rule, t, counts in rows:
        if len(counts) != 1:
            fail(f'{rule}: counts vary between deals')
            continue
        ((tu, cl, rd, rg),) = counts
        if rg != 52 + t:
            fail(f'{rule}: {rg} re-grips, not 52 + {t}')
        base = base or (tu, rd)
        turns_reads[rule] = (tu, rd)
        print(f"{rule:5s}: F3 rounds {t:2d}; face turns {tu} ({tu / base[0]:.2f}x v1), "
              f"clicks {cl}; pieces read {rd} ({rd / base[1]:.2f}x v1); "
              f"whole-puzzle re-grips {rg}")
    (a, ra), (b, rb) = turns_reads['C76'], turns_reads['C36']
    print(f"C76 vs C36: face turns {a}/{b} = {a / b:.2f}x, pieces read {ra}/{rb} = {ra / rb:.2f}x")


def x_grip_merge(workers):
    """Review t4c (exact): ordered pairs of different grips whose card step makes the same
    face turns and reads the same slot, per rank, for the table noon (A) and visual noon."""
    print('exact count over all 60 x 59 ordered grip pairs, 52 cards and both read parities '
          '(the pair shares the state outside the read, so the next re-grip could re-merge):')
    for nm in ('A', 'A_vn'):
        E = engine(nm)
        per = Counter()
        tot = 0
        for par in (0, 1):
            for c in range(52):
                sig = Counter()
                for gi in range(60):
                    op1, rd, op2, turns = E.steps[par][gi][c]
                    sig[(tuple(turns), tuple(s for s, _ in rd))] += 1
                n = sum(v * (v - 1) for v in sig.values())
                per[NAMES[c // 4]] += n
                tot += n
        byrank = ', '.join(f'{r}: {per[r]}' for r in NAMES)
        print(f"{nm:5s} ({RULES[nm][0]} noon): {tot} of {60 * 59 * 52 * 2}; by rank {byrank}")
    print('(the card steps of A_vn are those of C36 and C76; only the F3 count differs)')


def x_suit_exact(workers):
    """Suit dependence, exact: for every grip, read parity and rank, the four suits bring
    pieces from four DIFFERENT slots of the pre-card state into the read slot.  Since a
    position is a permutation, that is four different pieces for every state.  Two
    m9_search step-2 facts are re-asserted here (m9_search.read_injectivity): one colour
    pair never comes from two different pieces, and abs_reorient(*pair)[:2] == pair for
    every pair read, so the new grip determines the colour pair (Lean: M9.readGrip_colours,
    M9.corner_read_piece, M9.edge_read_piece).  Hence the four new grips always differ."""
    E = engine('C36')
    bad = 0
    cases = 0
    for par in (0, 1):
        for gi in range(60):
            for r in range(13):
                src = set()
                for s in range(4):
                    op1, rd, _, _ = E.steps[par][gi][4 * r + s]
                    slot = rd[0][0]
                    srcs, dsts, _ = op1
                    src.add(srcs[dsts.index(slot)] if slot in dsts else slot)
                cases += 1
                bad += len(src) != 4
    # read -> grip injective on pieces across all read configurations, and abs_reorient
    # keeps the colour pair: m9_search step 2 (m9_search.read_injectivity asserts both)
    try:
        eng.ref.read_injectivity()
        ok = True
    except AssertionError as e:
        ok = False
        fail(f'm9_search.read_injectivity: {e!r}')
    print(f"C36 card steps (identical for A_vn and C76): (grip, parity, rank) cases where "
          f"the 4 suits read pieces from 4 different pre-card slots: {cases - bad}/{cases}")
    print(f"read colour pair -> piece injective across all read configurations: {ok}")
    print(f"=> another suit of the same card never gives the same new grip, from any state: "
          f"{bad == 0 and ok}")
    if bad or not ok:
        fail('suit exactness')


# The recorded v2e (rule A) collision of the review (REPORT §1; out/t4b_anatomy_A.txt).
V2E_M1 = '8ee6a12322bfb0a0e57737e1836a64775e82f44cab1123cc69c92692'
V2E_M2 = '8ee6a12322bfb0a0e57737e261862948fd7fa0ceef6ecb2769c92692'


def x_v2e_pair(workers):
    """The review's recorded real Hash collision of rule A (table noon), re-verified with the
    fast engine and the slow reference, and checked NOT to collide under v2 (C36)."""
    m1, m2 = bytes.fromhex(V2E_M1), bytes.fromhex(V2E_M2)
    ha, hb = Hash(m1, 'A'), Hash(m2, 'A')
    sa, sb = ref_hash(m1, 'A'), ref_hash(m2, 'A')
    d1, d2 = phi_chunk(list(m1)), phi_chunk(list(m2))
    diff = [i + 1 for i in range(52) if d1[i] != d2[i]]
    print(f"M  = {V2E_M1}\nM' = {V2E_M2}\n  distinct: {m1 != m2}, "
          f"both 28 bytes: {len(m1) == len(m2) == 28}; deals differ at positions {diff}")
    print(f"  rule A (table noon): Hash(M) = {ha.hex()}\n"
          f"                       Hash(M') = {hb.hex()}\n"
          f"  equal (fast engine): {ha == hb}; equal (slow reference): {sa == sb == ha}")
    c1, c2 = Hash(m1), Hash(m2)
    print(f"  v2 (C36): Hash(M) = {c1.hex()}\n            Hash(M') = {c2.hex()}\n"
          f"  equal: {c1 == c2}")
    if not (m1 != m2 and ha == hb and sa == sb == ha and c1 != c2):
        fail('v2e pair')


def attack(E, h, deal, which, rng):
    """Review t6 read-class recipe; returns the pair (h1, h2) or None (same RNG use as t6)."""
    rec = []
    e = E.em(h, deal, rec=rec)
    hs = set(read_hslots(h, rec))
    W = compose_st(e, to_st(inverse(from_st(h))))       # E_m(h) = W * h
    Wp = from_st(W)
    cp, co, ep, eo = [list(x) for x in from_st(h)]
    if which == 'edges':
        U = [s for s in range(30) if ('e', s) not in hs]
        perm, n, wp = ep, 30, Wp[2]
    else:
        U = [s for s in range(20) if ('c', s) not in hs]
        perm, n, wp = cp, 20, Wp[0]
    winv = [0] * n
    for p in range(n):
        winv[wp[p]] = p
    avail = {perm[s] for s in U}
    pairs = [(a, b) for a, b in itertools.combinations(U, 2)
             if winv[a] in avail and winv[b] in avail]
    rng.shuffle(pairs)
    for a, b in pairs:
        opts = ([(winv[a], winv[b]), (winv[b], winv[a])] if which == 'edges'
                else [(winv[b], winv[a])])
        for pa, pb in opts:
            P = list(perm)
            rest_slots = [s for s in U if s not in (a, b)]
            rest = [perm[s] for s in U if perm[s] not in (pa, pb)]
            rng.shuffle(rest)
            P[a], P[b] = pa, pb
            for s, p in zip(rest_slots, rest):
                P[s] = p
            if perm_parity(P):
                if len(rest_slots) < 2:
                    continue
                P[rest_slots[0]], P[rest_slots[1]] = P[rest_slots[1]], P[rest_slots[0]]
            if which == 'edges':
                h1 = (cp, co, P, eo)
                eo2 = list(eo)
                eo2[a] ^= 1
                eo2[b] ^= 1
                h2 = (cp, co, P, eo2)
            else:
                h1 = (P, co, ep, eo)
                co2 = list(co)
                co2[a] = (co2[a] + 1) % 3
                co2[b] = (co2[b] + 2) % 3
                h2 = (P, co2, ep, eo)
            if not (legal(h1) and legal(h2)):
                continue
            s1, s2 = to_st(h1), to_st(h2)
            if s1 != s2 and E.dm(s1, deal) == E.dm(s2, deal):
                return (h1, h2)
    return None


def x_pseudo_pairs(workers):
    """Free-start: the review's re-run (v2-spec pseudo_check.py) of the read-class recipe
    (same corners, 2-edge flip) on C36 until 20 pairs, each re-verified with the SLOW
    reference HashDeckBodyFrom (m9_search's Em.lean transliteration)."""
    E = engine('C36')
    rng = random.Random(7)
    found = tried = 0
    ex = None
    bad = 0
    while found < 20:
        tried += 1
        h = uniform_st(rng)
        d = rand_deal(rng)
        r = attack(E, h, d, 'edges', rng)
        if not r:
            continue
        h1, h2 = r
        a = ref_body_from(d, as_tuple_pos(h1))
        b = ref_body_from(d, as_tuple_pos(h2))
        fa, fb = HashDeckBodyFrom(d, to_st(h1)), HashDeckBodyFrom(d, to_st(h2))
        ok = h1 != h2 and legal(h1) and legal(h2) and a == b == fa == fb
        bad += not ok
        found += 1
        ex = ex or (d, a.hex())
    print(f"C36 read-class pseudo-collisions (same corners, 2-edge flip; seed 7): {found} found in "
          f"{tried} (h, m) draws")
    print(f"  re-verified with the slow reference HashDeckBodyFrom and the fast one (h != h', both "
          f"legal, equal output): {found - bad}/{found}")
    print(f"  example output {ex[1][:24]}...")
    if bad:
        fail('pseudo pair re-verification')


# ================================================================ heavy experiments

SW_CLASSES = ('sr1', 'sr2', 'sr3', 'sr4', 'srR', 'dr1', 'dr2', 'suit')


def prefix_states(E, d):
    """One block d from IV-COOK12: the (state, grip) before each of its 52 cards, and the
    final state after the F3 rounds."""
    st = list(IV_ST)
    gi = 0
    cps = []
    for i in range(52):
        cps.append((list(st), gi))
        gi = E.run(st, d, gi=gi, start=i, stop=i + 1, f3=False)
    E.run(st, d, gi=gi, start=52, stop=52)
    return cps, st


def _swaps_work(args):
    rule, n, seed = args
    E = engine(rule)
    rng = random.Random(seed)
    cnt = {c: [0, 0] for c in SW_CLASSES}
    ex = []
    for _ in range(n):
        msg = bytes(rng.randrange(256) for _ in range(28))
        d = phi_chunk(list(msg))
        cps, base = prefix_states(E, d)

        def test(cls, d2, i, check_rank=True):
            if check_rank and phi_rank(d2) >= LIM:
                return
            s0, g0 = cps[i]
            s = list(s0)
            E.run(s, d2, gi=g0, start=i)
            cnt[cls][0] += 1
            if s == base:
                cnt[cls][1] += 1
                if len(ex) < 3:
                    ex.append((cls, msg.hex(),
                               phi_rank(d2).to_bytes(28, 'big').hex() if check_rank else str(d2)))
        for gap in (1, 2, 3, 4):
            for i in range(52 - gap):
                j = i + gap
                if d[i] // 4 == d[j] // 4:
                    d2 = d[:]
                    d2[i], d2[j] = d2[j], d2[i]
                    test(f'sr{gap}', d2, i)
        far = [(i, j) for i in range(52) for j in range(i + 5, 52) if d[i] // 4 == d[j] // 4]
        if far:
            i, j = rng.choice(far)
            d2 = d[:]
            d2[i], d2[j] = d2[j], d2[i]
            test('srR', d2, i)
        for gap in (1, 2):
            opts = [i for i in range(52 - gap) if d[i] // 4 != d[i + gap] // 4]
            i = rng.choice(opts)
            d2 = d[:]
            d2[i], d2[i + gap] = d2[i + gap], d2[i]
            test(f'dr{gap}', d2, i)
        i = rng.randrange(52)
        c = d[i]
        d2 = d[:]
        d2[i] = 4 * (c // 4) + (c % 4 + rng.randrange(1, 4)) % 4
        test('suit', d2, i, check_rank=False)
    return cnt, ex


def x_swaps(workers, rule='C36', N=1200000, chunks=20, seed=99):
    """Review t4 from IV-COOK12: same-rank swaps at distance 1-4 (all), one random same-rank
    pair at distance >= 5, one different-rank swap at distance 1 and 2, one suit change
    (outside the Hash domain: the changed deal is not a permutation)."""
    per = N // chunks
    res = pmap(_swaps_work, [(rule, per, seed * 100003 + c) for c in range(chunks)], workers)
    tot = {c: [0, 0] for c in SW_CLASSES}
    exs = []
    for cnt, ex in res:
        for c in SW_CLASSES:
            tot[c][0] += cnt[c][0]
            tot[c][1] += cnt[c][1]
        exs += ex
    print(f"rule {rule}: {per * chunks} random one-block messages from IV-COOK12, seed {seed} "
          f"({chunks} chunks, chunk seed {seed}*100003+c)")
    for c in SW_CLASSES:
        n, k = tot[c]
        lo, hi = ci95(k, n)
        rate = f"1/{n / k:,.0f}" if k else "0"
        print(f"  {c:4s}: {k:5d} collisions / {n:9,d} trials  rate {rate:>10s}  "
              f"95% CI [{lo:.2e}, {hi:.2e}]"
              + ("  (upper bound = 1/" + f"{1 / hi:,.0f})" if k == 0 else ""))
    for e in exs[:6]:
        print("  example:", e)
        if e[0] != 'suit' and Hash(bytes.fromhex(e[1]), rule) != Hash(bytes.fromhex(e[2]), rule):
            fail(f'swap example does not re-verify: {e}')


def _same_blocks_work(args):
    seed, lo, hi, gaps = args
    import suit_blind_collision as sbc
    E = engine('C36')
    out = {g: [0, 0] for g in gaps}
    hits = []
    for idx in range(lo, hi):
        rng = random.Random(f"sbc:{seed}:{idx}")
        msg = bytes(rng.randrange(256) for _ in range(28))
        d = phi_chunk(list(msg))
        cps, st = prefix_states(E, d)
        for gap, i, j, d2, n2 in sbc.swaps(d, gaps):
            s0, g0 = cps[i]
            s = list(s0)
            E.run(s, d2, gi=g0, start=i)
            out[gap][0] += 1
            if s == st:
                out[gap][1] += 1
                hits.append((msg.hex(), n2.to_bytes(28, 'big').hex()))
    return out, hits


def x_same_blocks(workers, blocks=40000, seed=99, gaps=(1, 2, 3, 4, 5, 6)):
    """The v1 swap search of ../suit_blind_collision.py --full (its first run: the same 40,000
    seed-99 IV blocks and the same same-rank swaps at distance 1-6), under v2 (C36)."""
    import suit_blind_collision as sbc
    step = 1000
    res = pmap(_same_blocks_work,
               [(seed, a, min(a + step, blocks), gaps) for a in range(0, blocks, step)], workers)
    per = {g: [0, 0] for g in gaps}
    hits = []
    for o, h in res:
        for g in gaps:
            per[g][0] += o[g][0]
            per[g][1] += o[g][1]
        hits += h
    print(f"swap search: {blocks} random one-block messages (from IV-COOK12), seed {seed}, "
          f"distances {gaps[0]}..{gaps[-1]}; the blocks and swaps of "
          f"../logs/suit_blind_collision_full.log's first run; "
          f"rule C36 (v2)")
    for g in gaps:
        t, x = per[g]
        print(f"  distance {g}: {x}/{t} same-rank swaps preserve dm; rate {sbc.rate_ci(x, t)}")
    T = sum(v[0] for v in per.values())
    print(f"  total {len(hits)}/{T}")
    for m1, m2 in hits[:3]:
        ok = Hash(bytes.fromhex(m1)) == Hash(bytes.fromhex(m2))
        print(f"  hit: M = {m1}  M' = {m2}  re-verified: {ok}")
        if not ok:
            fail('same-blocks hit does not re-verify')


def _local_ab(args):
    rule, k, n_starts, structured, seed = args
    E = engine(rule)
    rng = random.Random(seed)
    orders = full = 0
    for _ in range(n_starts):
        st0 = uniform_st(rng)
        g0 = rng.randrange(60)
        p = rng.randrange(0, 49)
        if not structured:
            cards = rng.sample(range(52), k)
        else:
            r1, r2 = rng.sample(range(13), 2)
            if k == 2:
                cards = [4 * r1 + s for s in rng.sample(range(4), 2)]
            elif k == 3:
                cards = [4 * r1 + s for s in rng.sample(range(4), 2)] + [4 * r2 + rng.randrange(4)]
            else:
                cards = ([4 * r1 + s for s in rng.sample(range(4), 2)]
                         + [4 * r2 + s for s in rng.sample(range(4), 2)])
        seen = {}
        for perm in itertools.permutations(cards):
            st = list(st0)
            dl = [0] * p + list(perm)
            gi = E.run(st, dl, gi=g0, start=p, f3=False)
            key = (tuple(st), gi)
            orders += 1
            full += len(seen.get(key, ()))
            seen.setdefault(key, []).append(perm)
    return orders, full


def _local_c(args):
    rule, k, n_windows, seed = args
    E = engine(rule)
    rng = random.Random(seed)
    tests = hits = 0
    ex = None
    for _ in range(n_windows):
        d = rand_deal(rng)
        i = rng.randrange(0, 52 - k + 1)
        st = list(IV_ST)
        gi = E.run(st, d, start=0, stop=i, f3=False)
        base = list(st)
        E.run(base, d, gi=gi, start=i)
        win = d[i:i + k]
        for perm in itertools.permutations(win):
            if list(perm) == win:
                continue
            d2 = d[:i] + list(perm) + d[i + k:]
            s = list(st)
            E.run(s, d2, gi=gi, start=i)
            tests += 1
            if s == base:
                hits += 1
                if ex is None:
                    ex = (i, win, perm)
    return tests, hits, ex


def x_local(workers, rule='C36', chunks=6):
    """Review t5: (a) k random cards / (b) rank-structured cards, all k! orderings, from a
    uniform random state and grip at a random mid-block position (NOT from the IV): a hit is
    two orderings reaching the same (state, grip); (c) windows of k consecutive cards in real
    blocks from IV-COOK12, every other ordering run to the end of the block (dm compared)."""
    fact = {2: 2, 3: 6, 4: 24}
    print(f"rule {rule} ({chunks} chunks per size)")
    for structured in (False, True):
        for k in (2, 3, 4):
            n_st = 600000 // fact[k]
            res = pmap(_local_ab,
                       [(rule, k, n_st // chunks, structured, 1000 * k + 17 * c + structured)
                        for c in range(chunks)], workers)
            orders = sum(r[0] for r in res)
            full = sum(r[1] for r in res)
            npairs = (n_st // chunks) * chunks * fact[k] * (fact[k] - 1) // 2
            lo, hi = ci95(full, npairs)
            print(f"{rule} ({'b' if structured else 'a'}) k={k} "
                  f"{'rank-structured' if structured else 'random cards'}: "
                  f"{orders:,} orderings, {npairs:,} ordering pairs, full collisions {full}; "
                  + (f"per pair 1/{npairs / full:,.0f}, 95% CI [{lo:.1e},{hi:.1e}]" if full
                     else f"per-pair 95% upper bound {hi:.1e} (=1/{1 / hi:,.0f})"))
    for k in (2, 3, 4):
        nw = 240000 // (fact[k] - 1)
        res = pmap(_local_c, [(rule, k, nw // chunks, 5000 * k + c) for c in range(chunks)],
                   workers)
        tests = sum(r[0] for r in res)
        hits = sum(r[1] for r in res)
        exs = [r[2] for r in res if r[2]]
        lo, hi = ci95(hits, tests)
        print(f"{rule} (c) k={k} window reorderings in IV blocks: {tests:,} tests, "
              f"dm collisions {hits}"
              + (f", rate 1/{tests / hits:,.0f}, 95% CI [{lo:.1e},{hi:.1e}]" if hits
                 else f", 95% upper bound {hi:.1e} (=1/{1 / hi:,.0f})")
              + (f"; example window at position {exs[0][0] + 1}: {exs[0][1]} -> "
                 f"{list(exs[0][2])}" if exs else ""))


def x_truncated(workers, rule='C36', N=200000):
    """Review t7b: birthday collisions of 32-bit truncations of the digest of N random
    one-block messages (a random function expects N(N-1)/2^33)."""
    E = engine(rule)
    rng = random.Random(55)
    lo = Counter()
    hi = Counter()
    for _ in range(N):
        msg = bytes(rng.randrange(256) for _ in range(28))
        dg = position_to_bytes(from_st(E.dm(IV_ST, phi_chunk(list(msg)))))
        lo[dg[-4:]] += 1
        hi[dg[1:5]] += 1
    pl = sum(v * (v - 1) // 2 for v in lo.values())
    ph = sum(v * (v - 1) // 2 for v in hi.values())
    exp = N * (N - 1) / 2 / 2 ** 32
    print(f"{rule:5s}: N={N} one-block messages (seed 55): 32-bit collisions low bytes {pl}, "
          f"bytes 1..4 {ph}; "
          f"expected {exp:.1f} (Poisson 95% range ~{max(0, exp - 1.96 * math.sqrt(exp)):.0f}-"
          f"{exp + 1.96 * math.sqrt(exp):.0f})")


def lgf(n):
    return math.lgamma(n + 1) / math.log(2)


def _coverage_work(args):
    rule, NB, NA, seed = args
    E = engine(rule)
    rng = random.Random(seed)
    uc = []
    ue = []
    bits = []
    sameW = 0
    allc = alle = 0
    nread = []
    for _ in range(NB):
        h = uniform_st(rng)
        d = rand_deal(rng)
        rec = []
        E.em(h, d, rec=rec)
        hs = read_hslots(h, rec)
        RC = {s for k, s in hs if k == 'c'}
        RE = {s for k, s in hs if k == 'e'}
        UC = [s for s in range(20) if s not in RC]
        UE = [s for s in range(30) if s not in RE]
        uc.append(len(UC))
        ue.append(len(UE))
        allc += not UC
        alle += not UE
        nread.append(len(rec))
        b = lgf(len(UC)) + len(UC) * math.log2(3) + lgf(len(UE)) + len(UE)
        b -= ((1 if len(UC) >= 2 else 0) + (1 if len(UE) >= 2 else 0)
              + (math.log2(3) if UC else 0) + (1 if UE else 0))
        bits.append(max(b, 0))
        cp, co, ep, eo = [list(x) for x in from_st(h)]
        pc = [cp[s] for s in UC]
        rng.shuffle(pc)
        pe = [ep[s] for s in UE]
        rng.shuffle(pe)
        for s, p in zip(UC, pc):
            cp[s] = p
            co[s] = rng.randrange(3)
        for s, p in zip(UE, pe):
            ep[s] = p
            eo[s] = rng.randrange(2)
        if len(UC) >= 2 and perm_parity(cp):
            cp[UC[0]], cp[UC[1]] = cp[UC[1]], cp[UC[0]]
        if UC:
            co[UC[0]] = (co[UC[0]] - sum(co)) % 3
        if len(UE) >= 2 and perm_parity(ep):
            ep[UE[0]], ep[UE[1]] = ep[UE[1]], ep[UE[0]]
        if UE:
            eo[UE[0]] = (eo[UE[0]] + sum(eo)) % 2
        h2 = (cp, co, ep, eo)
        if legal(h2):
            s2 = to_st(h2)
            t1, t2 = [], []
            E.em(h, d, trace=t1)
            E.em(s2, d, trace=t2)
            sameW += t1 == t2
        # an illegal re-randomised h is not counted as same W, so the sameW == n check
        # in x_coverage (parent process) fails the run; it never fires (sameW = n in the log)
    inv = {'flip2': 0, 'twist2': 0, 'ecyc3': 0}
    for _ in range(NB):
        h = uniform_st(rng)
        d = rand_deal(rng)
        t0 = []
        E.em(h, d, trace=t0)
        for kind in inv:
            cp, co, ep, eo = [list(x) for x in from_st(h)]
            if kind == 'flip2':
                a, b = rng.sample(range(30), 2)
                eo[a] ^= 1
                eo[b] ^= 1
            elif kind == 'twist2':
                a, b = rng.sample(range(20), 2)
                co[a] = (co[a] + 1) % 3
                co[b] = (co[b] + 2) % 3
            else:
                a, b, c = rng.sample(range(30), 3)
                ep[a], ep[b], ep[c] = ep[b], ep[c], ep[a]
            t1 = []
            E.em(to_st((cp, co, ep, eo)), d, trace=t1)
            inv[kind] += t1 == t0
    # read-class recipe: 'edges' = same corners + 2-edge flip, 'corners' = same edges + twist
    hit_flip = sum(attack(E, uniform_st(rng), rand_deal(rng), 'edges', rng) is not None
                   for _ in range(NA))
    hit_twist = sum(attack(E, uniform_st(rng), rand_deal(rng), 'corners', rng) is not None
                    for _ in range(NA))
    return uc, ue, bits, sameW, allc, alle, hit_flip, hit_twist, nread, inv


def x_coverage(workers, rules=(('C36', 3), ('C76', 4)), NB=3000, NA=1500):
    """Review t6: pieces of the input h read per block, the re-randomisation check (unread
    pieces never change the word W), small changes of h that leave W unchanged, and the
    read-class free-start recipe (every hit is re-checked with the real dm on both sides).
    Chunk counts per rule are the review's (3 for C36, 4 for C76; README.md)."""
    for rule, chunks in rules:
        res = pmap(_coverage_work,
                   [(rule, NB // chunks, NA // chunks, 777 + c) for c in range(chunks)], workers)
        uc = sum((r[0] for r in res), [])
        ue = sum((r[1] for r in res), [])
        bits = sorted(sum((r[2] for r in res), []))
        n = len(uc)
        na = (NA // chunks) * chunks
        sameW = sum(r[3] for r in res)
        allc = sum(r[4] for r in res)
        alle = sum(r[5] for r in res)
        hit_flip = sum(r[6] for r in res)
        hit_twist = sum(r[7] for r in res)
        nr = sum(sum(r[8]) for r in res) / n
        lo_flip, hi_flip = ci95(hit_flip, na)
        lo_twist, hi_twist = ci95(hit_twist, na)
        print(f"{rule:5s}: {n} blocks from uniform random h ({chunks} chunks, seeds 777+c); "
              f"reads/block {nr:.0f}; unread corners {sum(uc) / n:.2f}, "
              f"unread edges {sum(ue) / n:.2f}; P(all corners read) {allc / n:.3f}, "
              f"P(all edges read) {alle / n:.3f}; free bits mean {sum(bits) / n:.1f} "
              f"median {bits[n // 2]:.1f} max {bits[-1]:.1f}; "
              f"unread re-randomised -> same W {sameW}/{n}")
        se = [math.sqrt(sum((x - sum(v) / n) ** 2 for x in v) / (n - 1) / n) for v in (uc, ue)]
        print(f"       standard error of the two unread means: corners {se[0]:.3f}, "
              f"edges {se[1]:.3f}")
        iv = {k: sum(r[9][k] for r in res) for k in ('flip2', 'twist2', 'ecyc3')}
        print(f"       small change of h leaves W unchanged: "
              f"flip 2 random edges {iv['flip2']}/{n}, "
              f"twist 2 corners {iv['twist2']}/{n}, 3-cycle of edges {iv['ecyc3']}/{n}")
        # hit_flip: recipe 'edges' (h, h' share their corners and differ by a 2-edge flip),
        # printed as "same corners"; hit_twist: recipe 'corners' (same edges, 2-corner twist)
        print(f"       pseudo-collision (read-class recipe): same corners {hit_flip}/{na} = "
              f"{hit_flip / na:.3f} [{lo_flip:.3f},{hi_flip:.3f}]"
              f"{f' (~{na / hit_flip:.0f} (h,m) draws per hit)' if hit_flip else ''}; "
              f"same edges {hit_twist}/{na} = {hit_twist / na:.3f} [{lo_twist:.3f},{hi_twist:.3f}]"
              f"{f' (~{na / hit_twist:.0f} draws per hit)' if hit_twist else ''}")
        if sameW != n:
            fail(f'{rule}: re-randomising unread pieces changed W or gave an illegal h')


def x_coverage_chunks(workers, rules=('C36', 'C76'), counts=(1, 2, 3, 4, 5, 6, 8, 10, 12),
                      NB=3000, NA=1500):
    """Sensitivity of x_coverage to the chunk count: each count splits the draws differently
    over the seeds 777+c (partly overlapping samples), so the spread shows which digits of
    the coverage statistics are sampling noise."""
    print('rule chunks | unread corners, edges | read-class same corners | 2-edge flip keeps W')
    for rule in rules:
        for chunks in counts:
            res = pmap(_coverage_work,
                       [(rule, NB // chunks, NA // chunks, 777 + c) for c in range(chunks)],
                       workers)
            uc = sum((r[0] for r in res), [])
            ue = sum((r[1] for r in res), [])
            n = len(uc)
            na = (NA // chunks) * chunks
            hit_flip = sum(r[6] for r in res)
            fl = sum(r[9]['flip2'] for r in res)
            print(f"{rule:4s} {chunks:6d} | {sum(uc) / n:.2f}, {sum(ue) / n:.2f} | "
                  f"{hit_flip}/{na} = {hit_flip / na:.3f} | {fl}/{n}")


def x_suit_sampled(workers, rule='C36', N=30000, NB=1000):
    """Review t3 (sampled): the 4 suits of a random rank from a uniform state, grip and
    parity; and in situ at every card of NB real blocks from IV-COOK12."""
    E = engine(rule)
    rng = random.Random(3)
    dep = all4 = 0
    pair_counts = defaultdict(lambda: [0, 0])
    n_distinct = 0
    for _ in range(N):
        st0 = uniform_st(rng)
        gi = rng.randrange(60)
        r = rng.randrange(13)
        par = rng.randrange(2)
        gs = [E.step_grip(list(st0), par, gi, 4 * r + s) for s in range(4)]
        dep += len(set(gs)) > 1
        all4 += len(set(gs)) == 4
        n_distinct += len(set(gs))
        for a, b in itertools.combinations(range(4), 2):
            pair_counts[r][0] += gs[a] == gs[b]
            pair_counts[r][1] += 1
    pair = sum(v[0] for v in pair_counts.values()) / sum(v[1] for v in pair_counts.values())
    same = tot = blindc = 0
    for _ in range(NB):
        d = rand_deal(rng)
        st = list(IV_ST)
        gi = 0
        for i, c in enumerate(d):
            gs = {}
            for s in range(4):
                c2 = 4 * (c // 4) + s
                gs[c2] = E.step_grip(list(st), (i + 1) & 1, gi, c2)
            same += sum(gs[x] == gs[c] for x in gs if x != c)
            tot += 3
            blindc += len(set(gs.values())) == 1
            gi = E.run(st, d, gi=gi, start=i, stop=i + 1, f3=False)
    print(f"{rule:5s}: {N} uniform (state, grip, rank, parity), seed 3: "
          f"grip depends on the suit {dep / N:.4f}, "
          f"all 4 grips distinct {all4 / N:.4f}, mean distinct {n_distinct / N:.2f}, "
          f"P(two given suits give the same grip) {pair:.4f}")
    print(f"       in situ ({NB} IV blocks x 52 cards): "
          f"P(another suit gives the same grip) {same / tot:.4f}, "
          f"P(all 4 suits the same) {blindc / (NB * 52):.4f}")


def _place(d, placements):
    """Move each (position, card) into place by swapping it with the card's current slot."""
    for pos, card in placements:
        j = d.index(card)
        d[pos], d[j] = d[j], d[pos]


def _swap_trials(rule, n, seed, draw, keys, max_ex):
    """Shared loop of the targeted and telescoping searches.  draw(rng) returns (key, i, d,
    d2) or None (a rejected draw); a trial needs both deals to be messages (rank < 2^224),
    runs both from the IV-COOK12 state before card i to the end of the block and compares
    the final states.  Stops after n trials in all."""
    E = engine(rule)
    rng = random.Random(seed)
    tests = dict.fromkeys(keys, 0)
    hits = dict.fromkeys(keys, 0)
    ex = []
    while sum(tests.values()) < n:
        drawn = draw(rng)
        if drawn is None:
            continue
        key, i, d, d2 = drawn
        if phi_rank(d) >= LIM or phi_rank(d2) >= LIM:
            continue
        st = list(IV_ST)
        gi = E.run(st, d, start=0, stop=i, f3=False)
        a = list(st)
        E.run(a, d, gi=gi, start=i)
        b = list(st)
        E.run(b, d2, gi=gi, start=i)
        tests[key] += 1
        if a == b:
            hits[key] += 1
            if len(ex) < max_ex:
                ex.append((phi_rank(d).to_bytes(28, 'big').hex(),
                           phi_rank(d2).to_bytes(28, 'big').hex()))
    return tests, hits, ex


def _draw_targeted(rng):
    """A same-rank pair at i and i + gap (gap 2 or 3; rank not T) around a T card at i + 1."""
    d = rand_deal(rng)
    g = rng.choice((2, 3))
    i = rng.randrange(0, 52 - g)
    r = rng.randrange(12)
    if r == 9:
        r = 12
    s1, s2 = rng.sample(range(4), 2)
    t = 36 + rng.randrange(4)
    _place(d, ((i, 4 * r + s1), (i + g, 4 * r + s2), (i + 1, t)))
    if not (d[i] == 4 * r + s1 and d[i + g] == 4 * r + s2 and d[i + 1] == t):
        return None
    d2 = d[:]
    d2[i], d2[i + g] = d2[i + g], d2[i]
    return g, i, d, d2


def _targeted_work(args):
    rule, n, seed = args
    return _swap_trials(rule, n, seed, _draw_targeted, (2, 3), 3)


def x_targeted_T(workers, rules=('A', 'A_vn'), N=2000000, chunks=20, seed=4):
    """Review t4d: a same-rank swap at distance 2 or 3 around a rank-T card at i+1 (the
    table-noon degeneracy of x_grip_merge), from IV-COOK12; both deals are messages."""
    for rule in rules:
        res = pmap(_targeted_work, [(rule, N // chunks, seed * 7919 + c) for c in range(chunks)],
                   workers)
        for g in (2, 3):
            t = sum(r[0][g] for r in res)
            h = sum(r[1][g] for r in res)
            print(f"{rule}: gap {g} with a T at i+1: {h} collisions / {t:,} trials, "
                  f"{rate_text(h, t)}")
        for r in res:
            for e in r[2][:1]:
                m1, m2 = bytes.fromhex(e[0]), bytes.fromhex(e[1])
                ok = (m1 != m2 and Hash(m1, rule) == Hash(m2, rule)
                      and ref_hash(m1, rule) == ref_hash(m2, rule))
                print(f"  example: {e[0]} / {e[1]}; "
                      f"Hash collision re-verified (fast and slow): {ok}")
                if not ok:
                    fail('targeted example')


TELE_PAIRS = ((2, 49), (1, 50), (2, 26))   # A-spades/K-hearts, A-hearts/K-spades, A-spades/7-spades


def _draw_tele(rng):
    """One of TELE_PAIRS, in either order, at positions i and i + 1; d2 swaps them."""
    d = rand_deal(rng)
    i = rng.randrange(0, 51)
    x, y = rng.choice(TELE_PAIRS)
    if rng.randrange(2):
        x, y = y, x
    _place(d, ((i, x), (i + 1, y)))
    if d[i] != x or d[i + 1] != y:
        return None
    d2 = d[:]
    d2[i], d2[i + 1] = d2[i + 1], d2[i]
    return 0, i, d, d2


def _tele_work(args):
    rule, n, seed = args
    tests, hits, ex = _swap_trials(rule, n, seed, _draw_tele, (0,), 2)
    return tests[0], hits[0], ex


def x_telescoping(workers, rule='A_vn', N=2000000, chunks=24, seed=6):
    """Review t4e 'pairs': adjacent swaps of the telescoping card pairs A♠K♥, A♥K♠, A♠7♠
    (ids 2/49, 1/50, 2/26; CHaSeD suit order) at a random position of an IV block."""
    res = pmap(_tele_work, [(rule, N // chunks, seed * 7919 + c) for c in range(chunks)], workers)
    t = sum(r[0] for r in res)
    h = sum(r[1] for r in res)
    print(f"{rule}: adjacent telescoping-pair (A♠K♥, A♥K♠, A♠7♠) swaps from IV-COOK12 "
          f"({chunks} chunks): "
          f"{h} collisions / {t:,}, {rate_text(h, t)}")


# ================================================================ driver

QUICK = {
    'selfcheck': x_selfcheck,
    'cost': x_cost,
    'grip_merge': x_grip_merge,
    'suit_exact': x_suit_exact,
    'v2e_pair': x_v2e_pair,
    'pseudo_pairs': x_pseudo_pairs,
}
HEAVY = {
    'swaps': x_swaps,
    'same_blocks': x_same_blocks,
    'local': x_local,
    'truncated': x_truncated,
    'coverage': x_coverage,
    'coverage_chunks': x_coverage_chunks,
    'suit_sampled': x_suit_sampled,
    'targeted_T': x_targeted_T,
    'telescoping': x_telescoping,
}
ALL = {**QUICK, **HEAVY}
SETS = {'quick': QUICK, 'heavy': HEAVY, 'all': ALL}


def main():
    from gencheck import emit
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--check', action='store_true',
                    help='fail if a committed log differs from a fresh run')
    ap.add_argument('--set', choices=sorted(SETS), default='quick')
    ap.add_argument('--only', nargs='+', choices=sorted(ALL))
    ap.add_argument('--workers', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()
    if a.list:
        for s in ('quick', 'heavy'):
            for k, f in SETS[s].items():
                print(f"{s:5s} {k:13s} {f.__doc__.strip().splitlines()[0]}")
        return 0
    selfcheck()                       # raises (non-zero exit) before any experiment on a mismatch
    names = a.only or list(SETS[a.set])
    rc = 0
    for name in names:
        buf = io.StringIO()
        n0 = len(VERIFY_FAIL)
        t0 = time.time()
        with contextlib.redirect_stdout(buf):
            ALL[name](a.workers)
        print(f"{name}: {time.time() - t0:.1f} s wall ({a.workers} workers; not part of the log)",
              file=sys.stderr)
        text = f"$ python3 experiments.py --only {name}\n" + buf.getvalue()
        rc |= emit(os.path.join(LOGS, f'{name}.log'), text, a.check,
                   fix=f'python3 proofs/megadreifach/security/v2/experiments.py --only {name}')
        if len(VERIFY_FAIL) > n0:
            print(f'FAIL {name}: ' + '; '.join(VERIFY_FAIL[n0:]), file=sys.stderr)
            rc = 1
    return rc


if __name__ == '__main__':
    sys.exit(main())
