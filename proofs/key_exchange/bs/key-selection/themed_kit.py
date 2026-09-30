"""Checks for the themed three-state fleet key's dice (a candidate key that was not chosen;
NOTES.md): the face rules of the d20 / d8 / d4 readings and the former BS §4.1 = ECBS §1.3
full-restart placement with the spec d10 and the best-fit along-dice (part D of the former
randomizer-kit script).  ecbs13_kit.py is the same placement end to end."""
import json, random, collections, math
from fractions import Fraction as F
out = {}
def uniform_check(name, faces, rule, void=()):
    cnt = collections.Counter()
    used = [f for f in faces if f not in void]
    for f in used: cnt[rule(f)] += 1
    vals = set(cnt.values()); outcomes = len(cnt)
    ok = len(vals) == 1
    return {"rule": name, "faces": len(faces), "void": len(void), "outcomes": outcomes,
            "exact_uniform": ok, "void_rate": str(F(len(void), len(faces))),
            "bits_per_read": (math.log2(outcomes) * len(used) / len(faces)) if ok else None}
T = lambda x, lo, n: ("low", "mid", "high")[(x - lo) * 3 // n]
A = []
A.append(uniform_check("d20 last digit: group/place of last digit + teens; 10,20 void", range(1, 21),
                       lambda f: (T(f % 10, 1, 9), ("low", "mid", "high")[(f % 10 - 1) % 3], f > 10), void=(10, 20)))
A.append(uniform_check("d8 top half + odd/even", range(1, 9), lambda f: (f > 4, f % 2)))
A.append(uniform_check("d8 top half + top pair of its half + odd/even", range(1, 9), lambda f: (f > 4, (f - 1) % 4 >= 2, f % 2)))
A.append(uniform_check("d4 top half (3-4) + odd/even", range(1, 5), lambda f: (f > 2, f % 2)))
out["A_face_rules"] = A
for a in A: print("A", a)

rng = random.Random(2026)
# ---------------------------------------------------------------- D. ECBS 1.3 themed fleet placement
FLEET = [5, 4, 3, 3, 2]
ALONG = {5: 6, 4: 8, 3: 8, 2: 10}      # best-fit along-die: smallest die whose top face still fits
def per_ship_dist(L, along_sides):
    """One ship, face by face: coin orientation, d10 across (face 0 reads 10), along die re-rolled
    while the ship would hang off.  Each accepted along face s <= 11-L keeps mass 1/sides and the
    re-roll renormalises by the accepted mass, so nothing here is uniform by construction: a die
    too small for the ship (sides < 11-L) never shows the far starts and the check below fails."""
    res = collections.Counter(); valid = 11 - L
    acc = [s for s in range(1, along_sides + 1) if s <= valid]
    Z = F(len(acc), along_sides)                                     # accepted mass per roll
    for o in "HV":
        for face in range(10):
            a = 10 if face == 0 else face
            for s in acc:
                res[(o, a, s)] += F(1, 2) * F(1, 10) * F(1, along_sides) / Z
    return res, 1 - Z
def placement_ok(L, dist):
    """Exactly uniform over all 2 x 10 x (11-L) placements of a length-L ship."""
    want = {(o, a, s) for o in "HV" for a in range(1, 11) for s in range(1, 12 - L)}
    return set(dist) == want and len(set(dist.values())) == 1 and sum(dist.values()) == 1
D = {"per_ship": {}, "negative_controls": {}}
for L in (5, 4, 3, 2):
    for name, sides in (("spec_d10", 10), ("bestfit", ALONG[L])):
        dist, rej = per_ship_dist(L, sides)
        assert placement_ok(L, dist)
        D["per_ship"][f"L{L}_{name}"] = {"along_die": f"d{sides}", "reroll_rate": str(rej), "placements": len(dist)}
for L, sides in ((2, 8), (3, 6), (5, 4)):              # dice one size too small: the check must fail
    dist, rej = per_ship_dist(L, sides)
    ok = placement_ok(L, dist); assert not ok
    D["negative_controls"][f"L{L}_d{sides}"] = {"placements_reached": len(dist), "needed": 2 * 10 * (11 - L), "check": ok}
print("D per_ship", D["per_ship"]); print("D negative controls (must fail)", D["negative_controls"])
def place_fleet(rng, along, st):
    while True:
        st["attempts"] += 1; occ = set(); ok = True
        for L in FLEET:
            st["reads"] += 1; o = rng.randint(0, 1)                 # orientation
            st["reads"] += 1; a = rng.randint(1, 10)                # across coordinate (d10, 0=10)
            sides = 10 if along == "spec" else ALONG[L]
            while True:
                st["reads"] += 1; s = rng.randint(1, sides)
                if s <= 11 - L: break
                st["offgrid_rerolls"] += 1
            cells = {(a, s + t) if o == 0 else (s + t, a) for t in range(L)}
            if cells & occ: ok = False; break
            occ |= cells
        if ok: break
        st["restarts"] += 1
    st["reads"] += 17; st["sign_reads"] += 17
for along in ("spec", "bestfit"):
    st = collections.Counter(); M = 100000
    for _ in range(M): place_fleet(rng, along, st)
    D[along] = {k: v / M for k, v in st.items()}
    print("D", along, D[along])
out["D_ecbs13"] = D
json.dump(out, open("themed_kit_results.json", "w"), indent=1, default=str)
