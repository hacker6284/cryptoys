"""Write ../witness_v9.json from witness #INDEX of results/F6_KcQh_witnesses.json.

The JSON carries the witness (sigma, key, message, cipher, sigma M, sigma C) and, as
hints for the Lean kernel check, the round keys K1..K6 and the state after each stage for
both runs (computed with sudoc's Python output of the frozen v9 sudo, via proofs/sudo_py.py;
the states are the Compose steps of its trace_encrypt). The kernel re-derives every hint from the emitted
Lean, so a wrong hint makes the Lean build fail; nothing here is trusted by Lean.
usage: python3 make_witness.py [INDEX]
"""
import json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
import sudo_py
V = sudo_py.doubledeal(9)
def swap(x, y): return lambda c: y if c == x else x if c == y else c
def encrypt_stages(m, k): return [s.hand for s in V.trace_encrypt(m, k) if s.kind == sudo_py.text("compose")]
idx = int(sys.argv[1]) if len(sys.argv) > 1 else 0
run = json.loads((HERE / "results/F6_KcQh_witnesses.json").read_text())
w = run["witnesses"][idx]
x, y = run["swap"]; sg = swap(x, y)
key, msg = w["key"], w["message"]
keys = V.expand_keys(key)
A = encrypt_stages(msg, key)
B = encrypt_stages([sg(c) for c in msg], key)
assert A[-1] == w["cipher"] and B[-1] == w["cipher2"] == [sg(c) for c in A[-1]]
doc = {
    "sigma": [x, y],
    "about": "DoubleDeal v9 (frozen) full 6-round encrypt: E_K(sigma M) = sigma E_K(M) for sigma = "
             "K♣<->Q♥ (card ids 12, 24). One witness of the related-plaintext distinguisher; "
             "not a rate, not key recovery.",
    "source": f"attack/results/F6_KcQh_witnesses.json witness #{idx} (lowdiff.py witness F6 400000000 22 12,24; "
              f"{run['exact']} exact pairs in {run['n']})",
    "key": key, "message": msg, "cipher": A[-1],
    "message_sigma": [sg(c) for c in msg], "cipher_sigma": B[-1],
    "hints": {
        "note": "round keys K1..K6 (K0 = key) and the deck after whitening, full rounds 1-5 and the "
                "final round, for M and for sigma M. Checked by the Lean kernel, not trusted.",
        "round_keys": keys[1:], "states": A, "states_sigma": B,
    },
}
out = HERE.parent / "witness_v9.json"
import re
text = json.dumps(doc, indent=1, ensure_ascii=False)
text = re.sub(r"\[\s*([0-9,\s]+?)\s*\]", lambda m: "[" + ", ".join(m.group(1).split()).replace(",,", ",") + "]", text)
out.write_text(text + "\n")
print(f"wrote {out} (witness #{idx})")
