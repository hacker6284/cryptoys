"""Soundness of the certificate check on the code sudoc generates from ecbs.sudo (Toy, Hobby,
Serious), checked against PARI/GP.

Every trial is one call of the generated receive_check(): a receiver board holding its own A
(an honest pi(C') - C') in the across and up; the sender's C called into the base bands; curve
test; certificate rebuilt in the base bands; the sender's A called into the bottom and gap;
compare. The verdict is accept / curve / empty / mismatch. PARI (../oracle/ecbs_oracle.py)
picks the attack inputs and checks every accepted A. Classes, as in the Phase-1 field-level run
(../card/soundness_v3_field_*.json; the script was removed when ecbs.sudo replaced it):
  honest; C outside the subgroup with the correct certificate pi(C) - C; C outside with a wrong
  one (A = C, a random non-subgroup point, or minus the certificate); the 4 nonzero order-5
  points (4 A's each); A not matching pi(C) - C (5 kinds); C off the curve with A = the card's
  own certificate formulas on C (the generated make_certificate).
Plus the ladder-and-tally inversion (generated invert_number) on N random nonzero numbers.

Usage: python soundness.py Toy|Hobby|Serious [N]   (default N: 5000 / 3000 / 1000)
  writes results/soundness_<tier>.json; stdout -> results/soundness_<tier>.txt
"""
import json, os, random, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle")); sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
from ecbs_oracle import Tier, pari
import sudo_js as SJ

DEFAULT_N = {"Toy": 5000, "Hobby": 3000, "Serious": 1000}
VERDICT = {"Accept": "accept", "CurveFails": "curve", "EmptyCertificate": "empty", "Mismatch": "mismatch"}


def main():
    name = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else DEFAULT_N[name]
    T = Tier(name); R = T.R; l = T.l; w = R.w; one = w ** 0; zero = 0 * w
    rnd = random.Random(31 + len(name) + N)
    sudo = SJ.Sudo(); tier = SJ.tier(name)
    gf3 = [pari([zero, one]), pari([zero, -one]), pari([one, one]), pari([one, -one])]
    for t in gf3: assert R.on(t) and len(R.mul(5, t)) == 1 and R.frob(t) == t
    sub = lambda P: len(R.mul(l, P)) == 1
    honest = lambda: R.mul(rnd.randrange(1, l), T.Pref)
    plusT = lambda: R.add(honest(), gf3[rnd.randrange(4)])
    def rand_out():
        while True:
            P = pari.random(R.E)
            if len(P) == 2 and not sub(P): return P
    def off_curve():
        while True:
            P = pari([pari.random(w), pari.random(w)])
            if not R.on(P): return P
    def outside():
        C = plusT() if rnd.random() < .5 else rand_out(); assert not sub(C); return C
    def one_peg_off(A):
        reg = [list(T.trits(A[0])), list(T.trits(A[1]))]; c = rnd.randrange(2); i = rnd.randrange(T.n)
        reg[c][i] = rnd.choice([z for z in range(3) if z != reg[c][i]])
        return T.point(reg)
    U = lambda Q: T.unpoint(Q) if len(Q) == 2 else {"x": [0] * T.n, "y": [0] * T.n}
    out = {"provenance": SJ.provenance(), "tier": name, "N": N}
    t0 = time.time()

    def tally(label, trials):
        res = {"trials": 0, "accept": 0, "curve": 0, "empty": 0, "mismatch": 0, "peak": 0,
               "max_check_moves": 0, "tally_max": 0, "control_highest": 0}
        for C, A, note in trials:
            own = U(T.pi_minus_1(honest()))
            r = sudo.call("receive_check", tier, own, U(C), U(A))
            v = VERDICT[r["verdict"]["$"]]
            res["trials"] += 1; res[v] += 1
            for k in ("peak", "tally_max", "control_highest"): res[k] = max(res[k], r[k])
            res["max_check_moves"] = max(res["max_check_moves"], r["check_moves"])
            if v == "accept":
                Ap = T.point(r["rebuilt"])
                res["accepted_A_in_subgroup"] = res.get("accepted_A_in_subgroup", 0) + (R.on(Ap) and sub(Ap))
                res["accepted_A_equals_pari_piC_minus_C"] = res.get("accepted_A_equals_pari_piC_minus_C", 0) + (Ap == T.pi_minus_1(C))
            if note: res[note] = res.get(note, 0) + 1
        out[label] = res
        print(label, json.dumps(res), flush=True)

    tally("honest", [(C, T.pi_minus_1(C), None) for C in (honest() for _ in range(N))])
    tally("C outside subgroup, correct certificate", [(C, T.pi_minus_1(C), None) for C in (outside() for _ in range(N))])
    def outside_bad():
        C = outside(); k = rnd.randrange(3)
        A = [C, rand_out(), R.neg(T.pi_minus_1(C))][k]
        return C, A, ["A = C", "A = random non-subgroup point", "A = minus the certificate"][k]
    tally("C outside subgroup, wrong certificate", [outside_bad() for _ in range(N)])
    o5 = []
    for t in gf3:
        for A, note in ((pari([zero]), "A = empty bands"), (t, "A = C"), (honest(), "A = random subgroup point"),
                        (honest(), "A = another subgroup point")):
            o5.append((t, A, note))
    tally("C = nonzero order-5 point", o5)
    def mism():
        C = honest(); Ac = T.pi_minus_1(C); k = rnd.randrange(5)
        A = [honest, lambda: R.neg(Ac), lambda: one_peg_off(Ac), lambda: C, rand_out][k]()
        if k != 2 and A == Ac: return mism()
        return C, A, ["A = random subgroup point", "A = minus the certificate", "A = certificate with one peg changed",
                      "A = C", "A = non-subgroup point"][k]
    tally("A not matching pi(C) - C", [mism() for _ in range(N)])
    oc = []; passed = 0
    for _ in range(N):
        if rnd.random() < .5:
            C = off_curve(); note = "random (x, y)"
        else:
            while True:
                h = honest(); C = pari([h[0], h[1] + w ** rnd.randrange(T.n)])
                if not R.on(C): break
            note = "honest C, y nudged"
        a = sudo.call("make_certificate", tier, U(C))
        A = T.point(a) if a is not None else pari([zero])
        # the comparison step alone: the receiver's rebuild of an off-curve C is the same card
        # formulas (make_certificate), so it would equal this A whenever the run is not empty
        passed += a is not None and sudo.call("make_certificate", tier, U(C)) == U(A)
        oc.append((C, A, note))
    tally("C off the curve (A = the card formulas on C)", oc)
    out["C off the curve (A = the card formulas on C)"]["would_pass_without_curve_test"] = passed
    bad = 0
    for _ in range(N):
        z = pari.random(w)
        if z != 0:
            inv = T.el(sudo.call("invert_number", tier, T.trits(z)))
            bad += inv * z != one
    out["inversion_wrong"] = bad
    out["secs"] = round(time.time() - t0, 1)
    sudo.close()
    print("inversion_wrong", bad, "secs", out["secs"], flush=True)
    json.dump(out, open(os.path.join(HERE, "results", f"soundness_{name}.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
