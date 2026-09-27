"""dd9.c == dd_v9.py on every target shape, and F6 == the frozen v9 encrypt vectors."""
import sys, json, random, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v9 as P, dd9
def ref(m, keys, nfull, fin):
    s = P.compose(m, keys[0])
    for r in range(1, nfull + 1): s = P.full_round(s, keys[r])
    return P.final_round(s, keys[nfull + 1]) if fin else s
rng = random.Random(5); n = 0
for _ in range(200):
    m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
    keys = P.expand_keys(k)
    assert (dd9.real_keys(np.array([k]))[0] == np.array(keys)).all()
    for t, (nf, fin) in dd9.TARGETS.items():
        assert list(dd9.enc(np.array([m]), np.array([keys]), t)[0]) == ref(m, keys, nf, fin), t
        n += 1
d = json.load(open(HERE.parent / 'vectors/doubledeal_v9_vectors.json'))
v = 0
for vec in d['vectors']:
    if vec['kind'] == 'encrypt':
        ks = dd9.real_keys(np.array([vec['key']]))
        assert list(dd9.enc(np.array([vec['message']]), ks, 'F6')[0]) == vec['cipher']; v += 1
print(f"dd9.c == dd_v9.py on {n} (message, key, target) cases; F6 == frozen v9 encrypt on {v} vectors")
