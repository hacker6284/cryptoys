"""cand.c == candidates.py for every variant; v9 variant == frozen v9 vectors;
W5c variant == frozen v10 encrypt vectors; decrypt inverts."""
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
d10 = json.loads((HERE.parents[2] / "deprecated/doubledeal-v10/vectors/doubledeal_v10_vectors.json").read_text())  # frozen v10 (live vectors are v11)
W5c = C.VARIANTS["W5c"]; nw = nt = 0
for v in d10["vectors"]:
    if v["kind"] == "encrypt":
        nt += 1
        ok = C.encrypt(v["message"], v["key"], W5c) == v["cipher"]
        ok &= cport.enc(np.array([v["message"]]), cport.real_keys(np.array([v["key"]])), "F6", W5c)[0].tolist() == v["cipher"]
        nw += ok
assert nt > 0 and nw == nt, f"W5c matches only {nw}/{nt} v10 encrypt vectors"
rng = random.Random(9); n = 0
for name, var in C.VARIANTS.items():
    for _ in range(60):
        m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
        c = C.encrypt(m, k, var)
        assert cport.enc(np.array([m]), cport.real_keys(np.array([k])), "F6", var)[0].tolist() == c, name
        assert C.decrypt(c, k, var) == m, name
        n += 1
print(f"v9 variant matches {nv} frozen encrypt vectors (Python and C); W5c matches {nw}/{nt} v10 encrypt vectors (Python and C); "
      f"cand.c == candidates.py and decrypt(encrypt) = id on {n} cases over {len(C.VARIANTS)} variants")
