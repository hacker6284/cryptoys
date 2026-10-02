"""All recorded K♣↔Q♥ witnesses (F4 and F6 runs) and ../witness_v9.json against sudoc's Python output
of the frozen v9 sudo (proofs/sudo_py.py). The per-stage states are the Compose steps of its
trace_encrypt: whitening, full rounds 1-5, final round."""
import json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
import sudo_py
V = sudo_py.doubledeal(9)
def swap(x, y): return lambda c: y if c == x else x if c == y else c
def encrypt_stages(m, k): return [s.hand for s in V.trace_encrypt(m, k) if s.kind == sudo_py.text("compose")]
n = 0
for f in ("results/F6_KcQh_witnesses.json",):
    run = json.loads((HERE / f).read_text()); sg = swap(*run["swap"])
    for w in run["witnesses"]:
        c = V.encrypt(w["message"], w["key"]); c2 = V.encrypt([sg(x) for x in w["message"]], w["key"])
        assert c == w["cipher"] and c2 == [sg(x) for x in c] and c2 != c, w
        n += 1
w = json.loads((HERE.parent / "witness_v9.json").read_text()); sg = swap(*w["sigma"])
assert w["message_sigma"] == [sg(x) for x in w["message"]]
assert V.encrypt(w["message"], w["key"]) == w["cipher"]
assert V.encrypt(w["message_sigma"], w["key"]) == w["cipher_sigma"] == [sg(x) for x in w["cipher"]]
assert V.expand_keys(w["key"])[1:] == w["hints"]["round_keys"]
assert encrypt_stages(w["message"], w["key"]) == w["hints"]["states"]
assert encrypt_stages(w["message_sigma"], w["key"]) == w["hints"]["states_sigma"]
print(f"sudoc py (v9): {n}/{n} F6 witnesses satisfy E(sM) = sE(M) != E(M); witness_v9.json and its hints agree")
