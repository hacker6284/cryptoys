"""Verification for RANDOMIZER_KIT.md (PROPOSED kit; no spec is changed).
A. Face rules: every die-reading rule is enumerated face by face (exact Fractions).
B. Ship build: the kit's hole-die rules give exactly the spec's 'grow until it bumps'
   local distribution for every room state (so the whole build distribution is identical),
   plus a global exact enumeration on small grids.
C. Monte Carlo counts: reads, throws (queue cups), voids/rerolls per grid for each kit.
D. ECBS 1.3 themed fleet placement: spec d10 vs best-fit along-die; per-ship exact
   uniformity; reads, rerolls, restarts per fleet.
E. Per-tier totals."""
import sys, json, random, itertools, collections, math
from fractions import Fraction as F
sys.path.insert(0, "/workspace/bs/key")
out = {}

# ---------------------------------------------------------------- A. face rules
def uniform_check(name, faces, rule, void=()):
    cnt = collections.Counter()
    used = [f for f in faces if f not in void]
    for f in used: cnt[rule(f)] += 1
    vals = set(cnt.values()); outcomes = len(cnt)
    ok = len(vals) == 1
    # independence of components (if tuple): product of marginals == joint
    return {"rule": name, "faces": len(faces), "void": len(void), "outcomes": outcomes,
            "exact_uniform": ok, "void_rate": str(F(len(void), len(faces))),
            "bits_per_read": (math.log2(outcomes) * len(used) / len(faces)) if ok else None}

T = lambda x, lo, n: ("low", "mid", "high")[(x - lo) * 3 // n]
A = []
A.append(uniform_check("d6 thirds (1-2 low, 3-4 mid, 5-6 high)", range(1, 7), lambda f: T(f, 1, 6)))
A.append(uniform_check("d6 thirds + odd/even", range(1, 7), lambda f: (T(f, 1, 6), f % 2)))
A.append(uniform_check("d6 halves + odd/even  (EXPECTED NOT uniform)", range(1, 7), lambda f: (f > 3, f % 2)))
A.append(uniform_check("d6 'a six'", range(1, 7), lambda f: f == 6) | {"note": "1/6 event, not uniform by design"})
A.append(uniform_check("d10 group (1-3/4-6/7-9) then place in group; 0 void", range(0, 10),
                       lambda f: (T(f, 1, 9), ("low", "mid", "high")[(f - 1) % 3]), void=(0,)))
A.append(uniform_check("d12 thirds (1-4/5-8/9-12) + odd/even", range(1, 13), lambda f: (T(f, 1, 12), f % 2)))
A.append(uniform_check("d12 halves (1-6/7-12) + odd/even", range(1, 13), lambda f: (f > 6, f % 2)))
A.append(uniform_check("d12 thirds + odd/even + low/high pair of its third", range(1, 13),
                       lambda f: (T(f, 1, 12), f % 2, ((f - 1) % 4) >= 2)))
A.append(uniform_check("d12 '11-12' + odd/even", range(1, 13), lambda f: (f >= 11, f % 2)) | {"note": "1/6 event independent of parity: P(11-12 & odd)=1/12"})
A.append(uniform_check("d20 last digit: group/place of last digit + teens; 10,20 void", range(1, 21),
                       lambda f: (T(f % 10, 1, 9), ("low", "mid", "high")[(f % 10 - 1) % 3], f > 10), void=(10, 20)))
A.append(uniform_check("d8 top half + odd/even", range(1, 9), lambda f: (f > 4, f % 2)))
A.append(uniform_check("d8 top half + top pair of its half + odd/even", range(1, 9), lambda f: (f > 4, (f - 1) % 4 >= 2, f % 2)))
A.append(uniform_check("d4 top half (3-4) + odd/even", range(1, 5), lambda f: (f > 2, f % 2)))
A.append(uniform_check("d10 odd/even (0 even; no void)", range(0, 10), lambda f: f % 2))
A.append(uniform_check("percentile d100 read as 2 separate d10 group/place rules (00 or 0 void per die)",
                       [(a, b) for a in range(10) for b in range(10)],
                       lambda f: (T(f[0], 1, 9), (f[0] - 1) % 3, T(f[1], 1, 9), (f[1] - 1) % 3),
                       void=[(a, b) for a in range(10) for b in range(10) if a == 0 or b == 0]) |
         {"note": "same as two d10s thrown separately (void rate per die 1/10 if re-thrown singly)"})
out["A_face_rules"] = A
for a in A: print("A", a)

# ---------------------------------------------------------------- B. ship build equivalence
GROW = {2: F(1, 2), 3: F(1, 6), 4: F(1, 6)}
def ref_local(r, rl):
    """spec 'grow until it bumps; re-roll the whole hole if not even a Destroyer fits', exact."""
    sea = F(1, 3); pairs = {}
    for o, space in (("H", r), ("V", rl)):
        if space < 2: continue
        p = F(1); L = 2
        while True:
            if L == 5 or space <= L:
                pairs[(L, o)] = pairs.get((L, o), 0) + p; break
            g = GROW[L]; pairs[(L, o)] = pairs.get((L, o), 0) + p * (1 - g); p *= g; L += 1
    raw = {None: sea}
    for (L, o), p in pairs.items(): raw[(L, o)] = (1 - sea) * F(1, 2) * p
    Z = sum(raw.values())
    res = collections.Counter()
    for k, p in raw.items():
        if k is None: res[None] += p / Z; continue
        L, o = k
        kinds = ["S", "C"] if L == 3 else [{2: "D", 4: "B", 5: "A"}[L]]
        for K in kinds:
            for bow in (0, 1): res[(K, o, bow)] += p / Z / len(kinds) / 2
    return res

def kit_local(r, rl, hole_die):
    """kit procedure, enumerated face by face.  hole_die = 'd6' (thirds/halves; separate bow d6)
    or 'd12' (thirds/halves + odd/even bow)."""
    fitH, fitV = r >= 2, rl >= 2
    res = collections.Counter()
    def grow(o, p0, bow_given):
        space = r if o == "H" else rl
        def rec(L, p):
            if L < 5 and space > L:
                need = 4 if L == 2 else 6
                for f in range(1, 7):
                    if f >= need: rec(L + 1, p / 6)
                    else: finish(L, p / 6)
            else: finish(L, p)
        def finish(L, p):
            kinds = [(K, F(1, 2)) for K in ("S", "C")] if L == 3 else [({2: "D", 4: "B", 5: "A"}[L], F(1))]
            for K, pk in kinds:
                if bow_given is None:
                    for bow in (0, 1): res[(K, o, bow)] += p * pk / 2
                else: res[(K, o, bow_given)] += p * pk
        rec(2, p0)
    if not (fitH or fitV): res[None] += 1; return res
    if hole_die == "d6":
        faces = range(1, 7)
        for f in faces:
            if fitH and fitV: what = [None, None, "H", "H", "V", "V"][f - 1]
            else: what = None if f <= 3 else ("H" if fitH else "V")
            if what is None: res[None] += F(1, 6)
            else: grow(what, F(1, 6), None)
    else:
        for f in range(1, 13):
            if fitH and fitV: what = [None] * 4 + ["H"] * 4 + ["V"] * 4
            else: what = [None] * 6 + [("H" if fitH else "V")] * 6
            w = what[f - 1]
            if w is None: res[None] += F(1, 12)
            else: grow(w, F(1, 12), 0 if f % 2 else 1)
    return res

B = {}
for hd in ("d6", "d12"):
    ok = all(ref_local(r, rl) == kit_local(r, rl, hd) for r in range(1, 6) for rl in range(1, 6))
    B[f"hole_{hd}_local_equal_all_25_room_states"] = ok
    print("B", hd, "local distribution identical to spec for all (r, rl):", ok)
    assert ok
# global exact enumeration (Fractions) on small grids, kit vs spec
def enum_global(localf, n, m):
    outd = collections.Counter(); grid = [[None] * m for _ in range(n)]
    def rec(pos, prob, ships):
        while pos < n * m and grid[pos // m][pos % m] is not None: pos += 1
        if pos == n * m: outd[tuple(sorted(ships))] += prob; return
        i, j = divmod(pos, m); r = 0
        while j + r < m and grid[i][j + r] is None and r < 5: r += 1
        for k, p in localf(r, min(n - i, 5)).items():
            if k is None:
                grid[i][j] = "."; rec(pos + 1, prob * p, ships); grid[i][j] = None
            else:
                K, o, bow = k; L = {"D": 2, "S": 3, "C": 3, "B": 4, "A": 5}[K]
                cells = [(i, j + t) if o == "H" else (i + t, j) for t in range(L)]
                for a, b in cells: grid[a][b] = K
                rec(pos + 1, prob * p, ships + [(K, o, (i, j), bow)])
                for a, b in cells: grid[a][b] = None
    rec(0, F(1), []); return outd
for g in [(2, 3), (3, 3), (2, 5), (3, 4)]:
    ref = enum_global(ref_local, *g)
    for hd in ("d6", "d12"):
        kit = enum_global(lambda r, rl: kit_local(r, rl, hd), *g)
        assert kit == ref
    B[f"global_{g[0]}x{g[1]}"] = {"layouts": len(ref), "identical": True}
    print("B global", g, len(ref), "layouts: kit == spec exactly (both hole dice)")
# cross-check the Fraction reference against the float model used in FREE_FLEET_KEY
from brute_build import enumerate_build
from rules import extra_rules
fl = enumerate_build(extra_rules()["bump_reroll"], 3, 3)
ref = enum_global(ref_local, 3, 3)
flk = collections.Counter()
for k, p in fl.items(): flk[tuple(sorted(k))] += p
assert set(flk) == set(ref) and max(abs(float(ref[k]) - flk[k]) for k in ref) < 1e-12
B["fraction_reference_matches_float_model_3x3"] = True
out["B_ship_build"] = B

# ---------------------------------------------------------------- C. Monte Carlo counts per grid
def build(rng, kit, n=10, m=10, st=None):
    """kit: 'spec' (one d6 per spec roll, re-roll the hole), 'R' (hole d6 thirds/halves, no re-roll;
    growth, kind, bow d6), 'C' (hole d12 + odd/even bow; growth, kind d6)."""
    occ = [[None] * m for _ in range(n)]; ships = []
    def rd(kind, sides=6):
        st["reads"] += 1; st["reads_" + kind] += 1; return rng.randint(1, sides)
    def room(r, c, dr, dc, L):
        return all(r + dr * t < n and c + dc * t < m and occ[r + dr * t][c + dc * t] is None for t in range(L))
    for r in range(n):
        for c in range(m):
            if occ[r][c] is not None: continue
            st["decision_holes"] += 1
            fitH, fitV = room(r, c, 0, 1, 2), room(r, c, 1, 0, 2)
            bow = None
            if kit == "spec":
                while True:
                    if rd("sea") <= 2: o = None; break
                    o = "H" if rd("heading") <= 3 else "V"
                    if (fitH if o == "H" else fitV): break
                    st["hole_rerolls"] += 1
            elif not (fitH or fitV):
                o = None; st["no_roll_sea"] += 1
            elif kit == "R":
                f = rd("hole")
                o = ([None, None, "H", "H", "V", "V"][f - 1] if fitH and fitV else (None if f <= 3 else ("H" if fitH else "V")))
            else:
                f = rd("hole", 12)
                o = (([None] * 4 + ["H"] * 4 + ["V"] * 4)[f - 1] if fitH and fitV else (None if f <= 6 else ("H" if fitH else "V")))
                bow = 0 if f % 2 else 1
            if o is None: occ[r][c] = "."; st["sea"] += 1; continue
            dr, dc = (0, 1) if o == "H" else (1, 0); L = 2
            for need in (4, 6, 6):
                if not room(r, c, dr, dc, L + 1): break
                if rd("grow") >= need: L += 1
                else: break
            K = {2: "D", 4: "B", 5: "A"}.get(L)
            if L == 3: K = "S" if rd("kind") <= 3 else "C"
            if bow is None: bow = 0 if rd("bow") <= 3 else 1
            for t in range(L): occ[r + dr * t][c + dc * t] = K
            ships.append((K, o, (r, c), bow)); st["ships"] += 1
    return ships

def row_cup_throws(rng, holes, st):
    """d10 row cup: 5 rainbow d10 per 10-hole row (fewer dice for a partial row: ceil(h/2));
    zeros re-thrown together until none. Returns throws."""
    rows = [10] * (holes // 10) + ([holes % 10] if holes % 10 else [])
    for h in rows:
        dice = (h + 1) // 2; st["d10_dice_needed"] += dice
        pending = dice
        while pending:
            st["throws"] += 1; st["reads"] += pending
            z = sum(1 for _ in range(pending) if rng.randint(0, 9) == 0)
            st["voids"] += z; pending = z

rng = random.Random(2026); N = 20000
C = {}
for kit in ("spec", "R", "C"):
    st = collections.Counter()
    for _ in range(N): build(rng, kit, st=st)
    C[kit] = {k: v / N for k, v in sorted(st.items())}
    C[kit]["queue6_throws"] = C[kit]["reads"] / 6    # 6-die rainbow queue, carried over (+<=1 at the end)
    print("C build", kit, json.dumps(C[kit]))
for holes in (100, 200, 2, 16, 51, 162):
    st = collections.Counter()
    for _ in range(N): row_cup_throws(rng, holes, st)
    C[f"pegs_d10_rowcup_{holes}"] = {k: v / N for k, v in st.items()}
    print("C pegs", holes, C[f"pegs_d10_rowcup_{holes}"])
out["C_counts"] = C

# ---------------------------------------------------------------- D. ECBS 1.3 themed fleet placement
FLEET = [5, 4, 3, 3, 2]
ALONG = {5: 6, 4: 8, 3: 8, 2: 10}      # best-fit along-die: smallest die whose top face still fits
def per_ship_dist(L, along_sides):
    """one ship: coin orientation, d10 across (0 = 10), along die re-rolled while the ship would
    hang off; returns exact distribution over placements."""
    res = collections.Counter(); valid = 11 - L
    for o in "HV":
        for a in range(1, 11):
            for s in range(1, valid + 1):
                res[(o, a, s)] += F(1, 2) * F(1, 10) * F(1, valid)   # rejection => uniform on valid
    return res, F(along_sides - valid, along_sides)
D = {"per_ship": {}}
for L in (5, 4, 3, 2):
    for name, sides in (("spec_d10", 10), ("bestfit", ALONG[L])):
        dist, rej = per_ship_dist(L, sides)
        assert len(set(dist.values())) == 1 and len(dist) == 2 * 10 * (11 - L)
        D["per_ship"][f"L{L}_{name}"] = {"along_die": f"d{sides}", "reroll_rate": str(rej), "placements": len(dist)}
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
json.dump(out, open("randomizer_kit_results.json", "w"), indent=1, default=str)
print("saved randomizer_kit_results.json")
