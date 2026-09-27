"""Adversarial search (hill climbing with plateau moves and restarts) for low output-difference
weight. State = (deck d, difference delta), where delta is a cycle on a few positions
(length 2 = swap, length 3 = 3-cycle). Objective = wt(F(d), F(d o delta)).

usage: python3 search.py seconds_per_target seed [regex] > search.log
  (search.log: `search.py 120 777`; search2.log: `search.py 480 991 'q<=|4 keyed|5 keyed|encrypt'`)
Analysis only. A found minimum is a witness (an upper bound on the branch number); failing to go
lower is not a proof of anything.
"""
import sys, time, random, re
from multiprocessing import Pool
from common import FIXED_KEY, FIXED_KEY_SEED, GC, LAYERS, SR, rdeck, wt
import ddport
from dd_v8 import rank, expand_keys

SECS, SEED = (float(sys.argv[1]), int(sys.argv[2])) if __name__ == '__main__' else (0.0, 0)
KEYS6 = expand_keys(FIXED_KEY)          # real PassKey schedule from the fixed master key

def rounds(v, n):
    ks = KEYS6[1:1+n]
    def f(d):
        for k in ks: d = ddport.full_round(d, k, v)
        return d
    return f

def apply_cycle(d, pos):
    e = list(d); vals = [d[p] for p in pos]
    for k, p in enumerate(pos): e[p] = vals[(k - 1) % len(pos)]
    return e

def sr_diffrow_diffrank(d, pos):
    i, j = pos
    return i % 4 != j % 4 and rank(d[i]) != rank(d[j])

# name -> (layer builder, cycle length, constraint(d,pos) or None, fixed first position or None)
TARGETS = {}
for v in (8, 9):
    for L in ('GC', 'SR', 'SRGC', 'RK'):
        TARGETS[f'v{v} {L} swap'] = (lambda v=v, L=L: LAYERS[L](v), 2, None, None)
        TARGETS[f'v{v} {L} 3-cycle'] = (lambda v=v, L=L: LAYERS[L](v), 3, None, None)
    for p0 in (0, 1, 2):
        TARGETS[f'v{v} GC swap p={p0}'] = (lambda v=v: GC(v), 2, None, p0)
    TARGETS[f'v{v} SR swap diff-rows diff-ranks'] = (lambda v=v: SR(v), 2, sr_diffrow_diffrank, None)
    TARGETS[f'v{v} 2 keyed rounds swap'] = (lambda v=v: rounds(v, 2), 2, None, None)
    TARGETS[f'v{v} 3 keyed rounds swap'] = (lambda v=v: rounds(v, 3), 2, None, None)
    # second pass (run with a filter): early swaps in the walk, more rounds, the whole cipher
    for Q in (1, 2, 3, 4, 5, 6):
        TARGETS[f'v{v} GC swap q<={Q}'] = (lambda v=v: GC(v), 2, (lambda d, pos, Q=Q: max(pos) <= Q), None)
    TARGETS[f'v{v} 4 keyed rounds swap'] = (lambda v=v: rounds(v, 4), 2, None, None)
    TARGETS[f'v{v} 5 keyed rounds swap'] = (lambda v=v: rounds(v, 5), 2, None, None)
    TARGETS[f'v{v} encrypt swap'] = (lambda v=v: (lambda d: ddport.encrypt(d, FIXED_KEY, v)), 2, None, None)

def keys_note(name):
    """Which keys a target uses, for the log."""
    m = re.search(r'(\d) keyed rounds', name)
    if m: return f'  keys K1..K{m.group(1)}'
    if name.endswith('encrypt swap'): return '  keys K0..K6 (whole cipher)'
    if ' RK ' in name: return '  key FIXED_KEY (one round)'
    return ''

def climb(name, seed):
    build, L, ok, p0 = TARGETS[name]
    F = build(); rng = random.Random(seed)
    def rand_pos(d):
        while True:
            pos = rng.sample(range(52), L) if ok is None or 'q<=' not in name else rng.sample(range(int(name[-1]) + 1), L)
            if p0 is not None: pos[0] = p0
            if len(set(pos)) == L and (ok is None or ok(d, pos)): return pos
    def score(d, pos): return wt(F(d), F(apply_cycle(d, pos)))
    best = (99, None, None); evals = 0; t_end = time.time() + SECS; restarts = 0
    while time.time() < t_end:
        restarts += 1
        d = rdeck(rng); pos = rand_pos(d); s = score(d, pos); stale = 0
        while stale < 3000 and time.time() < t_end:
            d2, pos2 = list(d), list(pos)
            if rng.random() < 0.75:
                a, b = rng.sample(range(52), 2); d2[a], d2[b] = d2[b], d2[a]
            else:
                k = rng.randrange(L) if p0 is None else rng.randrange(1, L)
                pos2[k] = rng.randrange(52) if 'q<=' not in name else rng.randrange(int(name[-1]) + 1)
                if len(set(pos2)) < L: continue
            if ok is not None and not ok(d2, pos2): continue
            s2 = score(d2, pos2); evals += 1
            if s2 <= s:
                stale = 0 if s2 < s else stale + 1
                d, pos, s = d2, pos2, s2
            else: stale += 1
            if s < best[0]: best = (s, list(d), list(pos))
            if s <= 2: break
        if best[0] <= 2: break          # 2 is the floor for any bijection on decks
    return name, best, evals, restarts

if __name__ == '__main__':
    pat = sys.argv[3] if len(sys.argv) > 3 else None
    second = re.compile('q<=|4 keyed|5 keyed|encrypt')
    names = [n for n in TARGETS if (re.search(pat, n) if pat else not second.search(n))]
    with Pool() as pool:
        res = pool.starmap(climb, [(n, SEED + i) for i, n in enumerate(names)])
    print(f'# hill climbing, {SECS:.0f}s budget per target (stops early at weight 2), seed {SEED}')
    print(f'# fixed key = shuffle(seed {FIXED_KEY_SEED}); an n-round target uses the real PassKey keys '
          f'K1..Kn of that master key (shown per target)')
    for name, (s, d, pos), evals, restarts in res:
        inw = len(pos)
        print(f'{name:36s} min out={s:2d}  in+out={inw + s:2d}  evals={evals} restarts={restarts}{keys_note(name)}')
        print(f'    positions={pos} deck={d}')
