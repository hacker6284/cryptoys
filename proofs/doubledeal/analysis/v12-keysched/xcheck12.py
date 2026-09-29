"""Cross-check dd12.h (C, v12) against ddport.py (v=12) on random decks, and ddport against the
committed v12 vectors. Analysis only."""
import random, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'security' / 'checks'))
import ddport as P
rng = random.Random(1)
decks = []
for _ in range(300):
    d = list(range(52)); rng.shuffle(d); decks.append(d)
inp = '\n'.join(' '.join(map(str, d)) for d in decks) + '\n'
out = subprocess.run([str(HERE / 'xcheck12')], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
ident = list(range(52))
for i, d in enumerate(decks):
    pk, un, ct = (list(map(int, out[3 * i + j].split())) for j in range(3))
    assert pk == P.passkey(d, 12), 'passkey'
    assert un == P.mix_columns(P.stem(d, 12), 12), 'unkeyed'
    assert ct == P.encrypt(ident, d, 12), 'encrypt'
nv = 0
for v in P.vectors(12):
    if v['kind'] == 'encrypt':
        assert P.encrypt(v['message'], v['key'], 12) == v['cipher']; nv += 1
assert nv > 0
npk = 0
for v in P.vectors(12):
    if v['kind'] == 'passkey' and len(v['input']) == 52:
        o = subprocess.run([str(HERE / 'xcheck12')], input=' '.join(map(str, v['input'])) + '\n',
                           capture_output=True, text=True, check=True).stdout.split('\n')[0]
        assert list(map(int, o.split())) == v['output'], v['name']; npk += 1
assert npk > 0
print(f'OK: C == port on {len(decks)} random decks (passkey, unkeyed round, encrypt); port == {nv} committed encrypt vectors; C == {npk} committed 52-card passkey vectors')
