"""All recorded K♣↔Q♥ witnesses (F4 and F6 runs) and ../witness_v9.json against dd_v9.py."""
import json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v9 as V
n = 0
for f in ("results/F6_KcQh_witnesses.json",):
    run = json.loads((HERE / f).read_text()); sg = V.swap(*run["swap"])
    for w in run["witnesses"]:
        c = V.encrypt(w["message"], w["key"]); c2 = V.encrypt([sg(x) for x in w["message"]], w["key"])
        assert c == w["cipher"] and c2 == [sg(x) for x in c] and c2 != c, w
        n += 1
w = json.loads((HERE.parent / "witness_v9.json").read_text()); sg = V.swap(*w["sigma"])
assert w["message_sigma"] == [sg(x) for x in w["message"]]
assert V.encrypt(w["message"], w["key"]) == w["cipher"]
assert V.encrypt(w["message_sigma"], w["key"]) == w["cipher_sigma"] == [sg(x) for x in w["cipher"]]
assert V.expand_keys(w["key"])[1:] == w["hints"]["round_keys"]
assert V.encrypt_stages(w["message"], w["key"]) == w["hints"]["states"]
assert V.encrypt_stages(w["message_sigma"], w["key"]) == w["hints"]["states_sigma"]
print(f"dd_v9.py: {n}/{n} F6 witnesses satisfy E(sM) = sE(M) != E(M); witness_v9.json and its hints agree")
