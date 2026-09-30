"""Checks keygrid.py (the SPEC-literal BUILD and READ, BS SPEC §4.2-§4.3) against the exact model.

1. Small boards, both dice sets (d12 + row cup, and the all-d6 fallback): chi-square of the
   sampled layouts against the exact grow-until-it-bumps distribution (brute_build.enumerate_build
   with rules.extra_rules()["bump_reroll"]), of the peg patterns against uniform 3^cells, and on
   2x2 of the joint (layout, pegs) against model x uniform.  z is the Wilson-Hilferty normal score.
2. 10x10: 20000 builds per dice set; read() -> exponent -> digits round trip; mean key cells,
   mean hit units, dice rolls per grid.
Output: keygrid_check_results.txt / .json.  Seed 2027."""
import collections, itertools, json, math, random, statistics
import keygrid
from brute_build import enumerate_build
from rules import extra_rules

RULE = extra_rules()["bump_reroll"]


def z_of(chi, df):
    a = 2 / (9 * df)
    return ((chi / df) ** (1 / 3) - (1 - a)) / math.sqrt(a)


def chi2(cnt, probs, N):
    chi = sum((cnt.get(k, 0) - N * p) ** 2 / (N * p) for k, p in probs.items())
    assert all(k in probs for k in cnt), "sampled outcome outside the model"
    return chi, len(probs) - 1


def digits(e):
    d = []
    while e: d.append(e % 3); e //= 3
    return d[::-1]


def main():
    rng = random.Random(2027)
    out = {"small": {}, "10x10": {}}
    for fb in (None, "d6"):
        tag = "d12+cup" if fb is None else "d6"
        for g, N in [((2, 2), 300000), ((2, 3), 300000), ((3, 2), 300000), ((1, 5), 200000), ((5, 1), 200000)]:
            exact = enumerate_build(RULE, *g)
            cells = g[0] * g[1]
            lay, peg, joint = collections.Counter(), collections.Counter(), collections.Counter()
            for _ in range(N):
                s, p = keygrid.build(rng, *g, fallback=fb)
                k = tuple(sorted(s)); lay[k] += 1; peg[tuple(p)] += 1
                if g == (2, 2): joint[(k, tuple(p))] += 1
            upeg = {pg: 3 ** -cells for pg in itertools.product(range(3), repeat=cells)}
            res = {"N": N, "layouts": len(exact)}
            for name, cnt, pr in [("layout", lay, exact), ("pegs", peg, upeg)] + (
                    [("joint", joint, {(k, pg): q * 3 ** -cells for k, q in exact.items() for pg in upeg})]
                    if g == (2, 2) else []):
                c, df = chi2(cnt, pr, N)
                res[name] = {"chi2": round(c, 1), "df": df, "z": round(z_of(c, df), 2)}
            out["small"][f"{tag} {g[0]}x{g[1]}"] = res
            print(tag, g, json.dumps(res), flush=True)
        N = 20000; st = {}; C = []; H = []
        for _ in range(N):
            s, p = keygrid.build(rng, fallback=fb, stats=st)
            t = keygrid.key_cells([(s, p)])
            assert digits(keygrid.exponent(t)) == t
            C.append(len(t) - 1); H.append(sum(t) - 1)
        r = {"N": N, "mean_cells": round(statistics.mean(C), 3), "max_cells": max(C),
             "mean_hit_units": round(statistics.mean(H), 3),
             "rolls_per_grid": {k: round(v / N, 3) for k, v in sorted(st.items())}}
        out["10x10"][tag] = r
        print(tag, "10x10", json.dumps(r), flush=True)
    json.dump(out, open("keygrid_check_results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
