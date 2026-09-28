"""Cross-check dd.h (C) against the repo's own Python port and the committed known-answer vectors.
usage (from this folder): python3 xcheck.py [N]"""
import json, subprocess, sys
from pathlib import Path
REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / 'proofs/doubledeal/security/checks'))
import ddport as D
from dd_v8 import passkey, passkey_inv
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
here = Path(__file__).resolve().parent
bad = 0
for line in subprocess.run([str(here / 'vec'), str(N)], capture_output=True, text=True, check=True).stdout.split('\n'):
    if not line: continue
    k, p, c, f, g = [list(map(int, x.split(','))) for x in line.rstrip(';').split(';')]
    bad += (D.encrypt(p, k, 11) != c) + (passkey(k) != f) + (g != k)
print(f'random: {N} (key, plain) pairs, encrypt + F + F^-1 vs ddport/dd_v8: {bad} mismatches')
vec = [v for v in D.vectors(11) if v['kind'] == 'encrypt']
inp = ''.join(';'.join(','.join(map(str, v[x] if isinstance(v[x], list) else json.loads(v[x]))) for x in ('key', 'message')) + '\n' for v in vec)
out = subprocess.run([str(here / 'vec'), '-'], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
vb = sum(list(map(int, o.rstrip(';').split(','))) != (v['cipher'] if isinstance(v['cipher'], list) else json.loads(v['cipher'])) for v, o in zip(vec, out))
print(f'committed v11 encrypt vectors: {len(vec)} checked, {vb} mismatches')
