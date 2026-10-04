"""Cross-check ecbs_vectors.json (generated from ecbs.sudo by regen.sh) against PARI/GP.
ecbs.sudo, SPEC.md and CARD.md are normative; PARI (../oracle/ecbs_oracle.py) computes
every expected value from the curve alone, never from the board:

  arithmetic   x*y, x^3 and 1/x in GF(3^n) = GF(3)[w]/(w^n - w^k - 1)
  base point   P = [5](w^j, rhs^((3^n+1)/4)) for the first working j (SPEC 5.1)
  points       curve test = ellisoncurve; certificate = pi(C) - C on the curve, none iff x in GF(3)
  walks        the walk of key cells over a subgroup point B is [k]B, k = sum c_j lambda^(m-1-j) mod l
  receive      the verdict each class must get, and the rebuilt A = pi(C) - C when accepted
  exchanges    C = [a]P, A = [(lambda-1)a]P = pi(C) - C, each rebuilt A = the sender's A,
               shared = [(lambda-1)ab]P on both sides, folded = the SPEC 6 fold of its x
  fold         z_j = sum of x_i over i = j (mod m)
  roll         the keypad rule of SPEC 4 (face row = first hole, column = second; 0 thrown again)

Also checks that the JSON records the pinned sudocode commit and the current ecbs.sudo
hash. Prints one line per check group; exits 1 on any mismatch. Needs cypari2.

  python3 check_oracle.py > check_oracle_output.txt
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.dont_write_bytecode = True
from ecbs_oracle import Tier, pari

failures = []
T_ = lambda s: [".WR".index(c) for c in s]
S_ = lambda t: "".join(".WR"[d] for d in t)


def check(name, cond, what):
    if not cond:
        failures.append(f"{name}: {what}")
    return cond


def keypad_roll(cells, faces):
    """SPEC 4: two holes per die; a 0 is thrown again; an all-empty key is rolled again."""
    nxt = 0; rolls = 0
    while True:
        rolls += 1; out = []
        while len(out) < cells:
            while nxt < len(faces) and faces[nxt] == 0: nxt += 1
            if nxt >= len(faces): return None
            f = faces[nxt]; nxt += 1
            out.append((f - 1) // 3)
            if len(out) < cells: out.append((f - 1) % 3)
        if any(out): return {"cells": S_(out), "used": nxt, "rolls": rolls}


def tier_checks(name, v):
    T = Tier(name); R = T.R; l = T.l; lam1 = (T.lam - 1) % l
    pt = lambda p: T.point({"x": T_(p["x"]), "y": T_(p["y"])})
    same = lambda p, Q: len(Q) == 2 and p is not None and pt(p) == Q
    counts = {}
    def group(g, ok):
        counts.setdefault(g, [0, 0]); counts[g][0] += 1; counts[g][1] += bool(ok)
        check(name, ok, f"{g} #{counts[g][0]}")
    group("tier", v["tier"]["n"] == T.n and v["tier"]["k"] == T.k and v["tier"]["cells"] == T.cells)
    group("base point", same(v["base_point"], T.Pref))
    for a in v["arith"]:
        x, y = R.el(a["x"]), R.el(a["y"])
        group("arith", a["product"] == "".join(R.reg(x * y)) and a["cube"] == "".join(R.reg(x ** 3))
              and a["inverse"] == "".join(R.reg(1 / x)))
    for f in v["fold"]:
        group("fold", f["folded"] == S_(T.ref_fold(T_(f["x"]))))
    for p in v["points"]:
        Q = pt(p); on = R.on(Q); in3 = Q[0] == Q[0] ** 3
        ok = p["curve_test"] == on and ((p["certificate"] is None) == bool(in3))
        if on and not in3: ok = ok and same(p["certificate"], T.pi_minus_1(Q))
        group("points", ok)
    for w in v["walks"]:
        k = T.scalar(T_(w["cells"]))
        group("walks", keypad_roll(T.cells, w["faces"])["cells"] == w["cells"]
              and same(w["walked"], R.mul(k, pt(w["base"]))))
    want = {"honest": "Accept", "A = C": "Mismatch", "C outside the subgroup, correct certificate": "Accept",
            "C an order-5 point": "EmptyCertificate", "C off the curve": "CurveFails"}
    for r in v["receive"]:
        ok = r["verdict"] == want[r["why"]] and r["peak"] <= 7
        if r["verdict"] == "Accept":
            ok = ok and same(r["rebuilt"], T.pi_minus_1(pt(r["C"])))
            if r["why"] == "honest": ok = ok and len(R.mul(l, pt(r["rebuilt"]))) == 1
        group("receive", ok)
    for x in v["exchanges"]:
        ka, kb = T.scalar(T_(x["cells_a"])), T.scalar(T_(x["cells_b"]))
        K = R.mul(ka * kb * lam1 % l, T.Pref)
        ok = keypad_roll(T.cells, x["faces_a"])["cells"] == x["cells_a"]
        ok &= keypad_roll(T.cells, x["faces_b"])["cells"] == x["cells_b"]
        ok &= same(x["P"], T.Pref)
        for me, other, k in (("A", "B", ka), ("B", "A", kb)):
            p = x[me]; C = R.mul(k, T.Pref)
            ok &= p["base_hole"] == T.base_hole and same(p["sent_C"], C)
            ok &= same(p["sent_A"], R.mul(k * lam1 % l, T.Pref)) and same(p["sent_A"], T.pi_minus_1(C))
            ok &= p["rebuilt_A"] == x[other]["sent_A"] and p["matched"] and p["on_curve"]
            ok &= same(p["shared"], K) and p["folded"] == S_(T.ref_fold(T.trits(K[0])))
            ok &= p["peak"] == 7 and p["max_bench_hole"] < v["tier"]["bench"]
            ok &= p["control_highest"] < v["tier"]["control"]
        group("exchanges", ok)
    for r in v["roll"]:
        group("roll", r["rolled"] == keypad_roll(T.cells, r["faces"]))
    return ", ".join(f"{g} {a[1]}/{a[0]}" for g, a in counts.items())


def main():
    path = os.path.join(HERE, "ecbs_vectors.json")
    doc = json.load(open(path))
    pin = [l.strip() for l in open(os.path.join(ROOT, "proofs", "SUDOCODE_PIN"))
           if len(l.strip()) == 40 and all(c in "0123456789abcdef" for c in l.strip())][0]
    sha = hashlib.sha256(open(os.path.join(ROOT, doc["source"]), "rb").read()).hexdigest()
    check("header", doc["sudocode_commit"] == pin,
          f"sudocode_commit {doc['sudocode_commit']} != pin {pin}")
    check("header", doc["sudo_sha256"] == sha, "sudo_sha256 is not the current ecbs.sudo")
    print(f"ecbs_vectors.json: sudocode {doc['sudocode_commit'][:7]}, tiers {', '.join(doc['tiers'])}")
    for name, v in doc["tiers"].items():
        before = len(failures)
        info = tier_checks(name, v)
        print(f"{'ok ' if len(failures) == before else 'BAD'} {name}: {info}")
    if failures:
        print("\n".join(failures))
        sys.exit(1)
    print("all vectors agree with PARI/GP")


if __name__ == "__main__":
    main()
