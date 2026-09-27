"""Check the v8/v9 Python port: v9 against the current vectors, v8 against frozen dd_v8.py."""
import json, random, sys, ddport as P, dd_v8 as V8
from ddport import REPO
from dd_v8 import lay_cm, scoop_cm
d = json.load(open(REPO / 'proofs/doubledeal/vectors/doubledeal_vectors.json'))
n = 0
for vec in d['vectors']:
    k = vec['kind']
    if k == 'encrypt': got, exp = P.encrypt(vec['message'], vec['key'], 9), vec['cipher']
    elif k == 'mix_columns': got, exp = P.mix_columns(vec['input'], 9), vec['output']
    elif k == 'sum_ranks': got, exp = scoop_cm(P.sum_ranks(lay_cm(vec['input']), 9)), vec['output']
    elif k == 'unkeyed_full': got, exp = P.mix_columns(P.stem(vec['input'], 9), 9), vec['output']
    else: continue
    if got != exp: print('MISMATCH', vec['name']); sys.exit(1)
    n += 1
print('v9 port matches', n, 'vectors')
rng = random.Random(1)
for _ in range(300):
    m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
    assert P.encrypt(m, k, 8) == V8.encrypt(m, k)
print('v8 port == frozen dd_v8.py on 300 random (m,k)')
