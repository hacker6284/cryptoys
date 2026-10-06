"""Write inputs.json: the inputs of the ECBS known-answer vectors (ecbs_vectors.json).

The outputs are not computed here: regen.sh runs the sudoc JS build of
primitives/key_exchange/ecbs/ecbs.sudo over these inputs, and check_oracle.py then
cross-checks every output against PARI/GP (../oracle/ecbs_oracle.py). PARI is used
here only to pick inputs (points of the subgroup, points outside it, an off-curve
pair); it computes no expected output.

Numbers are '.WR' strings, hole 0 first ('.' empty, 'W' white, 'R' red). Keys are
given as the d10 faces of the row cup (SPEC 4); roll_key turns them into cells.

  /path/to/python-with-cypari2 make_inputs.py      # rewrites inputs.json
"""
import json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.dont_write_bytecode = True
from ecbs_oracle import Tier, pari

S = lambda t: "".join(".WR"[d] for d in t)
TIERS = ["Demo", "Toy", "Hobby", "Serious"]
EXCHANGES = {"Demo": 2, "Toy": 2, "Hobby": 1, "Serious": 1}   # Serious: ~20 s each in JS
WALKS = {"Demo": 2, "Toy": 2, "Hobby": 1, "Serious": 0}        # Serious walks are inside the exchange

def faces(rnd, cells):
    """enough d10 faces for one roll plus re-throws: a 0 now and then (thrown again)."""
    out = []
    while len(out) < (cells + 1) // 2 + 4:
        out.append(rnd.choice([0] + list(range(1, 10)) * 3))
    return out

def main():
    out = {"schema": 1, "tiers": {}}
    for name in TIERS:
        T = Tier(name); R = T.R; n = T.n; l = T.l
        rnd = random.Random(f"ecbs-vectors-{name}")
        rand = lambda: S([rnd.randrange(3) for _ in range(n)])
        def nonzero():
            while True:
                x = rand()
                if x != "." * n: return x
        def sub_point():
            return R.mul(rnd.randrange(1, l), T.Pref)
        def outside():
            while True:
                Q = pari.random(R.E)
                if len(Q) == 2 and len(R.mul(l, Q)) != 1: return Q
        def off_curve():
            while True:
                Q = pari([R.el(rand()), R.el(rand())])
                if not R.on(Q): return Q
        pt = lambda Q: {"x": "".join(R.reg(Q[0])), "y": "".join(R.reg(Q[1]))}
        order5 = {"x": "." * n, "y": "W" + "." * (n - 1)}
        tin = {}
        tin["arith"] = [{"x": nonzero(), "y": rand()} for _ in range(4)]
        tin["fold"] = [rand() for _ in range(3)]
        P = pt(T.Pref)
        tin["points"] = [
            {"why": "P", **P},
            {"why": "a subgroup point", **pt(sub_point())},
            {"why": "a point outside the subgroup", **pt(outside())},
            {"why": "an order-5 point (x in GF(3))", **order5},
            {"why": "off the curve", **pt(off_curve())},
        ]
        tin["walks"] = []
        for i in range(WALKS[name]):
            tin["walks"].append({"faces": faces(rnd, T.cells), "base": pt(sub_point() if i else T.Pref)})
        C = sub_point(); A = T.pi_minus_1(C); own = T.pi_minus_1(sub_point()); O = outside()
        tin["receive"] = [
            {"why": "honest", "own": pt(own), "c": pt(C), "a": pt(A)},
            {"why": "A = C", "own": pt(own), "c": pt(C), "a": pt(C)},
            {"why": "C outside the subgroup, correct certificate", "own": pt(own), "c": pt(O), "a": pt(T.pi_minus_1(O))},
            {"why": "C an order-5 point", "own": pt(own), "c": order5, "a": order5},
            {"why": "C off the curve", "own": pt(own), "c": pt(off_curve()), "a": pt(A)},
        ]
        tin["exchanges"] = [{"faces_a": faces(rnd, T.cells), "faces_b": faces(rnd, T.cells)}
                            for _ in range(EXCHANGES[name])]
        tin["roll"] = [[0] * ((T.cells + 1) // 2), [1] * ((T.cells + 1) // 2) + [5] + faces(rnd, T.cells)]
        out["tiers"][name] = tin
    with open(os.path.join(HERE, "inputs.json"), "w") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print("wrote inputs.json")

if __name__ == "__main__":
    main()
