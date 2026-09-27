"""dd_v9.py against the frozen v9 vectors, and the vectors' sudo_sha256 against the frozen sudo."""
import hashlib, json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(HERE))
import dd_v9 as V
d = json.loads((HERE.parent / "vectors/doubledeal_v9_vectors.json").read_text())
sudo = REPO / "primitives/cipher/doubledeal/v9/doubledeal_v9.sudo"
sha = hashlib.sha256(sudo.read_bytes()).hexdigest()
assert d["source"] == "primitives/cipher/doubledeal/v9/doubledeal_v9.sudo", d["source"]
assert d["sudo_sha256"] == sha, f"vectors were built from sudo {d['sudo_sha256']}, frozen sudo is {sha}"
check = {
    "encrypt": lambda v: V.encrypt(v["message"], v["key"]) == v["cipher"],
    "passkey": lambda v: V.passkey(v["input"]) == v["output"],
    "expand_keys": lambda v: V.expand_keys(v["k0"]) == v["keys"],
    "compose": lambda v: V.compose(v["message"], v["key"]) == v["output"],
    "mix_columns": lambda v: V.mix_columns(v["input"]) == v["output"],
    "unkeyed_full": lambda v: V.mix_columns(V.stem(v["input"])) == v["output"],
}
n = 0
for v in d["vectors"]:
    if v["kind"] in check:
        assert check[v["kind"]](v), v["name"]; n += 1
print(f"frozen v9 vectors: sudo_sha256 matches v9/doubledeal_v9.sudo; dd_v9.py agrees on {n} vectors")
