"""Check the v8/v9/v10/v11 Python port: v11 against the current vectors, v10 and v9 against
their frozen vectors, v8 against frozen dd_v8.py."""
import json, random, sys, ddport as P, dd_v8 as V8
from ddport import REPO
from dd_v8 import lay_cm, scoop_cm
d = json.load(open(REPO / 'proofs/doubledeal/vectors/doubledeal_vectors.json'))
def check(d, v):
    n = 0
    for vec in d['vectors']:
        k = vec['kind']
        if k == 'encrypt': got, exp = P.encrypt(vec['message'], vec['key'], v), vec['cipher']
        elif k == 'mix_columns': got, exp = P.mix_columns(vec['input'], v), vec['output']
        elif k == 'sum_ranks': got, exp = scoop_cm(P.sum_ranks(lay_cm(vec['input']), v)), vec['output']
        elif k == 'unkeyed_full': got, exp = P.mix_columns(P.stem(vec['input'], v), v), vec['output']
        else: continue
        if got != exp: print(f'MISMATCH v{v}', vec['name']); sys.exit(1)
        n += 1
    print(f'v{v} port matches', n, 'vectors')
check(d, 11)
check(json.load(open(REPO / 'proofs/deprecated/doubledeal-v10/vectors/doubledeal_v10_vectors.json')), 10)
check(json.load(open(REPO / 'proofs/deprecated/doubledeal-v9/vectors/doubledeal_v9_vectors.json')), 9)
for _ in range(50):
    m = list(range(52)); random.shuffle(m)
    g = lay_cm(m)
    assert P.inv_sum_ranks_v10(P.sum_ranks_v10(g)) == g
print('v10 inv SumRanks undoes SumRanks on 50 random decks')
for _ in range(200):
    m = list(range(52)); random.shuffle(m)
    assert P.inv_mix_columns_v11(P.mix_columns(m, 11)) == m
print('v11 inverse GridCycle undoes GridCycle on 200 random decks')
rng = random.Random(1)
for _ in range(300):
    m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
    assert P.encrypt(m, k, 8) == V8.encrypt(m, k)
print('v8 port == frozen dd_v8.py on 300 random (m,k)')
# Frozen-v10 analysis checks (need numpy and gcc; ~4 s). They read the frozen v10 vectors, so they
# break loudly here instead of silently when the live vectors move.
import subprocess
AN = REPO / 'proofs/doubledeal/analysis/v10-sumranks'
for script in (AN / 'check_cand.py', AN / 'sbox-search/verify.py'):
    r = subprocess.run([sys.executable, str(script)], cwd=script.parent, capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout, r.stderr); print('FAIL', script.relative_to(REPO)); sys.exit(1)
    print(script.relative_to(REPO), 'ok:', r.stdout.strip().splitlines()[-1][:120])
