"""Cross-check bs_vectors.json (generated from bs.sudo by regen.sh) against the
Python evidence code, which is an oracle here and not a second spec:

  BUILD   ../ships-pegs/keygrid.py build(), fed the same dice faces by kind
  READ    keygrid.key_cells() (its ship pass is itself checked against read_rule.encode)
  B3-B8   ../reference/bspegs.py peg recipes: multiply, tidy, walk, check_and_square
  values  ../reference/bsref.py and Python's pow(): A = 3^a, B8 base = B^2,
          K = 3^(2ab mod q) = (B^2)^a, all mod p, canonical
  §3.1    the answer for each hole (red Hit, white Miss, empty Misfire), all n holes

Also checks that the JSON records the pinned sudocode commit and the current
bs.sudo hash. Prints one line per vector; exits 1 on any mismatch.

  python3 check_oracle.py > check_oracle_output.txt
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path[:0] = [os.path.join(HERE, "..", "reference"), os.path.join(HERE, "..", "ships-pegs")]
import bspegs as P, bsref as R, keygrid as KG

PAR = json.load(open(os.path.join(HERE, "..", "reference", "params.json")))
PARAMS = {"T1": PAR["T1"], "T2": PAR["T2"], "T6": PAR["T6demo"]}
DIE = {(1, 12): "d12", (1, 6): "d6", (0, 9): "d10"}
KIND = {"D": "Destroyer", "S": "Sub", "C": "Cruiser", "B": "Battleship", "A": "Carrier"}
CALL = {"R": "Hit", "W": "Miss", ".": "Misfire"}

failures = []


def check(name, cond, what):
    if not cond:
        failures.append(f"{name}: {what}")
    return cond


def field(tier):
    d = PARAMS[tier]; n = d["n"]; toll = R.enc(int(d["c"]), n)
    while toll[-1] == ".": toll.pop()
    return P.Field(n, toll), int(d["p"]), int(d["q"])


class Faces:
    """Serves keygrid.build the recorded faces, by kind of die."""
    def __init__(self, faces):
        self.q = {k: list(v) for k, v in faces.items()}

    def randint(self, a, b):
        return self.q[DIE[(a, b)]].pop(0)


def oracle_key(name, faces, key_json):
    src = Faces(faces)
    ships, pegs = KG.build(src)
    check(name, all(not v for v in src.q.values()), "keygrid.build left dice unread")
    want = sorted((KIND[K], "across" if o == "H" else "down", "ABCDEFGHIJ"[r] + str(c + 1), "last" if bow else "first")
                  for K, o, (r, c), bow in ships)
    got = sorted((s["kind"], s["lies"], s["first"], s["bow"]) for s in key_json["ships"])
    check(name, want == got, "BUILD fleet differs from keygrid.build")
    check(name, "".join(key_json["pegs"]) == "".join(".WR"[t] for t in pegs), "BUILD pegs differ from keygrid.build")
    cells = KG.key_cells([(ships, pegs)])
    return "".join(".WR"[t] for t in cells)


def reg(s):
    return list(s)


def run(v):
    name, F_p_q = v["name"], field(v["tier"])
    F, p, q = F_p_q
    n = F.n
    if v["kind"] == "exchange":
        ca = oracle_key(name + " Alice", v["dice_a"], v["key_a"])
        cb = oracle_key(name + " Bob", v["dice_b"], v["key_b"])
        check(name, ca == v["cells_a"] and cb == v["cells_b"], "READ cells differ from keygrid.key_cells")
        ea, eb = R.exponent([ca]), R.exponent([cb])
        A, B = pow(3, ea, p), pow(3, eb, p)
        check(name, v["public_a"] == "".join(R.enc(A, n)) and v["public_b"] == "".join(R.enc(B, n)), "public values != pow(3, e, p)")
        check(name, reg(v["public_a"]) == P.walk(F, [ca]) and reg(v["public_b"]) == P.walk(F, [cb]), "public values != bspegs.walk")
        for who, pub, shots, rec in (("A", v["public_a"], v["shots_a"], v["received_a"]), ("B", v["public_b"], v["shots_b"], v["received_b"])):
            check(name, len(shots) == n and shots == [CALL[c] for c in pub], f"§3.1 answers for {who}")
            check(name, rec == pub, f"§3.1 copy of {who}")
        CB, CA = pow(B, 2, p), pow(A, 2, p)
        check(name, v["base_a"] == "".join(R.enc(CB, n)) and v["base_b"] == "".join(R.enc(CA, n)), "B8 bases != square mod p")
        check(name, reg(v["base_a"]) == P.check_and_square(F, reg(v["received_b"]))
              and reg(v["base_b"]) == P.check_and_square(F, reg(v["received_a"])), "B8 bases != bspegs.check_and_square")
        K = pow(3, 2 * ea * eb % q, p)
        check(name, K == pow(CB, ea, p) == pow(CA, eb, p), "pow identities")
        check(name, v["secret_a"] == "".join(R.enc(K, n)) == v["secret_b"], "K != 3^(2ab) mod p, or K_A != K_B")
        check(name, reg(v["secret_a"]) == P.walk(F, [ca], reg(v["base_a"]))
              and reg(v["secret_b"]) == P.walk(F, [cb], reg(v["base_b"])), "K != bspegs.walk (shared phase)")
        tz = lambda s: len(s) - len(s.rstrip("."))
        return (f"cells {len(ca) - 1}/{len(cb) - 1}, ships {len(v['key_a']['ships'])}/{len(v['key_b']['ships'])}, "
                f"trailing misfires A {tz(v['public_a'])} B {tz(v['public_b'])}, K = {K}")
    if v["kind"] == "multiply":
        got = P.multiply(F, reg(v["a"]), reg(v["b"]), v["nudge"])
        check(name, reg(v["product"]) == got, "!= bspegs.multiply")
        check(name, R.dec(v["product"]) % p == R.dec(v["a"]) * R.dec(v["b"]) * 3 ** v["nudge"] % p, "!= a*b*3^nudge mod p")
        return f"product {R.dec(v['product'])}"
    if v["kind"] == "tidy":
        check(name, reg(v["tidy"]) == P.tidy(F, reg(v["x"])), "!= bspegs.tidy")
        check(name, R.dec(v["tidy"]) == R.dec(v["x"]) % p, "!= x mod p")
        return f"tidy {R.dec(v['tidy'])}"
    if v["kind"] == "check":
        try:
            want = "".join(P.check_and_square(F, reg(v["received"])))
        except ValueError:
            want = None
        check(name, v["base"] == want, f"!= bspegs.check_and_square ({want})")
        x2 = R.dec(v["received"]) ** 2 % p
        check(name, (v["base"] is None) == (x2 in (0, 1)), "reject iff the square is 0 or 1")
        return "rejected" if v["base"] is None else f"base {R.dec(v['base'])}"
    if v["kind"] == "call":
        check(name, v["shots"] == [CALL[c] for c in v["x"]] and len(v["shots"]) == n, "§3.1 answers")
        check(name, v["y"] == v["x"], "§3.1 copy")
        return f"{len(v['shots'])} calls, {sum(s == 'Misfire' for s in v['shots'])} misfires"
    raise ValueError(v["kind"])


def main():
    doc = json.load(open(os.path.join(HERE, "bs_vectors.json")))
    pin = [l.strip() for l in open(os.path.join(ROOT, "proofs", "SUDOCODE_PIN")) if len(l.strip()) == 40 and not l.startswith("#")][0]
    sha = hashlib.sha256(open(os.path.join(ROOT, doc["source"]), "rb").read()).hexdigest()
    check("header", doc["sudocode_commit"] == pin, f"sudocode_commit {doc['sudocode_commit']} != pin {pin}")
    check("header", doc["sudo_sha256"] == sha, "sudo_sha256 is not the current bs.sudo")
    print(f"bs_vectors.json: sudocode {doc['sudocode_commit'][:7]}, {len(doc['vectors'])} vectors")
    for v in doc["vectors"]:
        before = len(failures)
        info = run(v)
        print(f"{'ok ' if len(failures) == before else 'BAD'} {v['name']}: {info}")
    if failures:
        print("\n".join(failures))
        sys.exit(1)
    print("all vectors agree with the Python reference and pow()")


if __name__ == "__main__":
    main()
