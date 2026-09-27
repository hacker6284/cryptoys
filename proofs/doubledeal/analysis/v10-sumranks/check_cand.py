"""cand.c == candidates.py for every variant; v9 variant == frozen vectors; decrypt inverts."""
import sys, json, random, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import candidates as C, cport
d = json.loads((HERE.parents[2] / "deprecated/doubledeal-v9/vectors/doubledeal_v9_vectors.json").read_text())
nv = 0
for v in d["vectors"]:
    if v["kind"] == "encrypt":
        assert C.encrypt(v["message"], v["key"], 0) == v["cipher"]
        assert cport.enc(np.array([v["message"]]), cport.real_keys(np.array([v["key"]])), "F6", 0)[0].tolist() == v["cipher"]
        nv += 1
rng = random.Random(9); n = 0
for name, var in C.VARIANTS.items():
    for _ in range(60):
        m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
        c = C.encrypt(m, k, var)
        assert cport.enc(np.array([m]), cport.real_keys(np.array([k])), "F6", var)[0].tolist() == c, name
        assert C.decrypt(c, k, var) == m, name
        n += 1
print(f"v9 variant matches {nv} frozen encrypt vectors (Python and C); "
      f"cand.c == candidates.py and decrypt(encrypt) = id on {n} cases over {len(C.VARIANTS)} variants")
