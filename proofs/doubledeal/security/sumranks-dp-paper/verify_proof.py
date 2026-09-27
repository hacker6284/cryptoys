#!/usr/bin/env python3
"""Numerical checks of every intermediate lemma in PROOF.md against the C model of v10 SumRanks in
../../analysis/v10-sumranks/sbox-search/ (sbox.c via sb.py); the pure-Python model.py is first checked
equal to it. Output: verify_output.txt. Compiled helpers go to ./build/ (gitignored).
Conventions (as in sbox.c): grid cell 13*row+col, card = 13*suit+rank0, suits C,H,S,D, GF(4) labels C0 H=w S=w^2 D=1.
Run:  python3 verify_proof.py  (a few minutes; needs gcc with OpenMP and numpy)."""
import sys, os, random, math, subprocess, itertools, time
from pathlib import Path
from fractions import Fraction as Fr
from collections import Counter
HERE = Path(__file__).resolve().parent
os.chdir(HERE)
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'analysis' / 'v10-sumranks' / 'sbox-search'))
(HERE / 'build').mkdir(exist_ok=True)
import sb
from model import sr_trace, U, V, S, lab, rk, mulw
from rowlemma_exact import rho, dist
T0 = time.time()
R = random.Random(20260927)
def hdr(s): print("\n" + "=" * 100 + "\n" + s + "\n" + "=" * 100, flush=True)
def ok(cond, msg):
    print(("  [PASS] " if cond else "  [FAIL] ") + msg, flush=True)
    if not cond: ok.fails += 1
ok.fails = 0
def rand_grid(): g = list(range(52)); R.shuffle(g); return g
def apply(tau, g): return [tau[c] for c in g]
def cyc(*cs):
    p = list(range(52))
    for c in cs:
        for i, x in enumerate(c): p[x] = c[(i + 1) % len(c)]
    return p
C = sb.card
def delta(tau, c): return (rk(tau[c]) - rk(c)) % 13
def eps(tau, c): return lab(tau[c]) ^ lab(c)
def v10sym(a, x):
    inv = {0: 0, 2: 1, 3: 2, 1: 3}   # label -> suit index
    return [13 * inv[lab(c) ^ x] + (rk(c) + a) % 13 for c in range(52)]
def survives(tau, g):
    y, _ = sr_trace(g); y2, _ = sr_trace(apply(tau, g)); return y2 == apply(tau, y)
def rot_left(row, t): return row[t:] + row[:t]
def row_phase(g):
    g = list(g); ts = []
    for i in (1, 2, 3, 0):
        p = (i + 3) % 4; t = U(g[13*p:13*p+13]); ts.append(t); g[13*i:13*i+13] = rot_left(g[13*i:13*i+13], t)
    return g, ts
def inv_row_phase(h):
    g = list(h)
    for i in (0, 3, 2, 1):
        p = (i + 3) % 4; t = U(g[13*p:13*p+13]); r = g[13*i:13*i+13]; g[13*i:13*i+13] = r[-t:] + r[:-t] if t else r
    return g
LAMBDA = [lambda x: 0, lambda x: x, mulw, lambda x: mulw(mulw(x))]
def Vvec(e): return e[1] ^ mulw(e[2]) ^ mulw(mulw(e[3]))
def Svec(e): return e[0] ^ e[1] ^ e[2] ^ e[3]

# ------------------------------------------------------------------------------------------------
hdr("0. Model: pure-Python model.py == verified sbox.c (outputs and all 17 amounts)")
bad = 0
for _ in range(3000):
    g = rand_grid(); a, b = sr_trace(g); o, am = sb.sr(g); bad += (a != o or b != am)
ok(bad == 0, f"3000 random grids, mismatches = {bad}")
bad = 0
for _ in range(500):
    g = rand_grid(); h, _ = row_phase(g); bad += inv_row_phase(h) != g
ok(bad == 0, "inverse row phase really inverts the row phase (so the post-row grid H is uniform)")
for a in range(13):
    for x in range(4):
        s = v10sym(a, x)
        assert sorted(s) == list(range(52))
        assert all(delta(s, c) == a and eps(s, c) == x for c in range(52))
bad = sum(not survives(v10sym(R.randrange(13), R.randrange(4)), rand_grid()) for _ in range(300))
ok(bad == 0, "v10Sym(a,x) (delta==a, eps==x) survives on 300 random grids")

# ------------------------------------------------------------------------------------------------
hdr("1. Lemma 1 (per deck): survival <=> all 17 amounts equal <=> the 17 'trajectory' conditions\n"
    "   R_i : S(A_i) == t_i * D(A_i) (mod 13)   [A_i = original row i, t_i = G's turn applied to row i before it is read]\n"
    "   K_j : V(eps(column j-1 as read)) == S(eps(column j))   [only needed when all rows agree]")
def traj_conditions(tau, g):
    """evaluate the conditions on G's OWN trajectory; returns (row_ok list, col_ok list)."""
    x = list(g); rows_ok = []
    ts = {}
    for i in (1, 2, 3, 0):
        p = (i + 3) % 4
        read = x[13*p:13*p+13]                       # row p as it is now
        orig = g[13*p:13*p+13]; t_p = ts.get(p, 0)   # it equals rot_left(orig, t_p)
        assert read == rot_left(orig, t_p)
        d = [delta(tau, c) for c in orig]; Ssum = sum(j*d[j] for j in range(13)) % 13; D = sum(d) % 13
        rows_ok.append(Ssum == (t_p * D) % 13)
        t = U(read); ts[i] = t; x[13*i:13*i+13] = rot_left(x[13*i:13*i+13], t)
    cols_ok = []
    for j in list(range(1, 13)) + [0]:
        pc = [x[13*i+(j-1) % 13] for i in range(4)]; cc = [x[13*i+j] for i in range(4)]
        cols_ok.append(Vvec([eps(tau, c) for c in pc]) == Svec([eps(tau, c) for c in cc]))
        s = V(pc) ^ S(cc)
        for i in range(4): x[13*i+j] = cc[(i - s) % 4]
    return rows_ok, cols_ok
def planted_grid(cards_cells):
    g = [None]*52; rest = [c for c in range(52) if c not in cards_cells.values()] if False else None
    used = set(cards_cells.keys()); pool = [c for c in range(52) if c not in cards_cells.values()]
    R.shuffle(pool); it = iter(pool)
    return [cards_cells.get(i) if i in cards_cells else next(it) for i in range(52)]
taus = {
 "same-suit 3-cycle AC->2C->3C": cyc([C('C','A'), C('C','2'), C('C','3')]),
 "same-suit swap 2C<->7C": cyc([C('C','2'), C('C','7')]),
 "same-rank 3-cycle 2C->2H->2S": cyc([C('C','2'), C('H','2'), C('S','2')]),
 "label+1 on rank 2": cyc([C('C','2'), C('D','2')], [C('H','2'), C('S','2')]),
 "random 4-card perm": None, "random full perm": None, "rank shift in clubs (13-cycle)": cyc([C('C', r) for r in range(13)]),
}
tot = Counter()
for name, tau in taus.items():
    for trial in range(1500):
        tt = tau
        if name == "random 4-card perm":
            cs = R.sample(range(52), 4); tt = cyc(cs)
        if name == "random full perm":
            tt = list(range(52)); R.shuffle(tt)
        # half random decks, half planted decks that make survival likely
        if trial % 2 == 0 or tau is None: g = rand_grid()
        elif name.startswith("same-suit 3"):
            g = planted_grid({R.choice([0,13,26,39]) + 1: C('C','A'), 0: None} if False else {1: C('C','A'), 2: C('C','3'), 3: C('C','2')})
        elif name.startswith("same-rank 3") or name.startswith("label"):
            # plant the moved cards in one column of H, then undo the row phase
            h = rand_grid(); col = R.randrange(13); moved = [c for c in range(52) if tt[c] != c]
            cells = [13*i+col for i in range(4)]; R.shuffle(cells)
            for c, cell in zip(moved, cells):
                k = h.index(c); h[k], h[cell] = h[cell], h[k]
            g = inv_row_phase(h)
        else: g = rand_grid()
        surv = survives(tt, g)
        _, a1 = sr_trace(g); _, a2 = sr_trace(apply(tt, g)); amt_eq = a1 == a2
        rows_ok, cols_ok = traj_conditions(tt, g)
        traj = all(rows_ok) and all(cols_ok)
        tot[(surv, amt_eq, traj)] += 1
        if not (surv == amt_eq == traj):
            print("   counterexample", name, surv, amt_eq, traj); break
print("   (survive, amounts equal, trajectory conditions) counts:", dict(tot))
ok(all(k[0] == k[1] == k[2] for k in tot) and tot[(True, True, True)] > 500, "equivalence holds on every tested deck, including >500 surviving decks")

hdr("1b. Rotation identity: turn(rot_left(x,t)) - turn(x) == t * (sum of ranks)  and  S(rot x) = S(x) - t D(x)")
bad = 0
for _ in range(3000):
    row = R.sample(range(52), 13); t = R.randrange(13)
    bad += (U(rot_left(row, t)) - U(row) - t*sum(rk(c) for c in row)) % 13 != 0
ok(bad == 0, "3000 random rows")

# ------------------------------------------------------------------------------------------------
hdr("2. Lemma 2 (one row): D != 0 -> exactly 1/13 for every target; D = 0 -> p0; exhaustive scan of all 13-multisets")
subprocess.check_call(["gcc", "-O2", "-o", "build/p0scan", "p0scan.c"])
out = subprocess.check_output(["build/p0scan"]).decode(); print(out)
ok("D!=0 non-uniform count=0" in out and "max p0 (D=0, nonconstant) = 0.090909 = 1/11.000" in out,
   "every nonconstant row multiset with D=0 has p0 <= 1/11; D!=0 is exactly uniform")
ok("Lemma 2(b) exhaustive: 226002 (class, value) checks of max_c P[S=c] <= 1/(z_v+1), violations=0" in out,
   "Lemma 2(b) EXHAUSTIVE for p=13: every nonconstant 13-multiset (all 33,429 affine classes; the bound is affine-invariant),"
   " every value v in it, every target c: P[S=c] <= 1/(z_v+1)")
ok("Lemma 2(c) exhaustive: cancelling-pair classes with P[S=0]>0: 0" in out, "Lemma 2(c) exhaustive for p=13")
# independent implementation: brute force over all arrangements for the prime analogues p = 5, 7 (all multisets)
from math import factorial
def dist_brute(vals, p):
    c = Counter(sum(j*perm[j] for j in range(p)) % p for perm in itertools.permutations(vals))
    return [Fr(c[k], factorial(p)) for k in range(p)]
for p in (5, 7):
    bad = n = 0
    for ms in itertools.combinations_with_replacement(range(p), p):
        d = dist_brute(ms, p); n += 1; cnt = Counter(ms)
        if sum(ms) % p: bad += any(x != Fr(1, p) for x in d)
        if len(cnt) > 1:
            for v, z in cnt.items(): bad += max(d) > Fr(1, z+1)
    for v in range(p):
        for u in range(1, p): bad += dist_brute([v]*(p-2) + [(v+u) % p, (v-u) % p], p)[0] != 0
    ok(bad == 0, f"prime analogue p={p}: Lemma 2(a),(b),(c) by brute force over all {n} multisets x {factorial(p)} arrangements")
# independent implementation for p = 13 (rowlemma_exact.dist) on random multisets, all values v
bad = 0
for _ in range(300):
    k = R.randrange(1, 13); vals = [0]*(13-k) + [R.randrange(1, 13) for _ in range(k)]
    if len(set(vals)) == 1: continue
    d = dist(vals)
    bad += any(max(d) > Fr(1, z+1) for z in Counter(vals).values())
ok(bad == 0, "Lemma 2(b) cross-check with the independent Python DP on 300 random 13-rows (every value class)")
ok(rho([0]*11 + [4, 9]) == 0, "a row whose only non-majority cards are a cancelling pair (u,-u) never passes (p0 = 0)")

hdr("2b. Lemma 3 (row chain, exact): given the partition into row SETS, P[all 4 row conditions] = prod_i rho(M_i).\n"
    "    Test: fix row sets, shuffle inside rows, compare the model's row-amount agreement rate with prod rho.")
def row_amounts_agree(tau, g):
    _, a1 = sb.sr(g); _, a2 = sb.sr(apply(tau, g)); return a1[:4] == a2[:4]
tau3 = cyc([C('C','A'), C('C','2'), C('C','3')])   # deltas +1,+1,-2
def place_rows(place):
    """random grid, then move each card of `place` into the requested row (swapping with an unplaced card)."""
    g = rand_grid()
    for c, row in place.items():
        k = g.index(c)
        if k // 13 == row: continue
        for cell in range(13*row, 13*row+13):
            if g[cell] not in place: g[k], g[cell] = g[cell], g[k]; break
    return [g[13*i:13*i+13] for i in range(4)]
A_, B_, C_ = C('C','A'), C('C','2'), C('C','3')
# placements chosen so the predicted value is large AND rows with D != 0 sit downstream of rows whose ORDER sets their
# target theta_r * D (this is exactly what Lemma 3's nested-sum argument has to get right)
for place, nsamp in [({A_: 0, B_: 0, C_: 0}, 60000), ({A_: 1, B_: 1, C_: 1}, 60000), ({A_: 2, B_: 2, C_: 3}, 150000),
                     ({A_: 0, B_: 1, C_: 1}, 150000), ({A_: 3, B_: 0, C_: 0}, 150000), ({A_: 1, B_: 2, C_: 3}, 300000)]:
    rows = place_rows(place)
    pred = Fr(1)
    for r in rows: pred *= rho([delta(tau3, c) for c in r])
    hit = 0
    for _ in range(nsamp):
        gg = []
        for r in rows: rr = r[:]; R.shuffle(rr); gg += rr
        hit += row_amounts_agree(tau3, gg)
    p = hit / nsamp; se = math.sqrt(float(pred)*(1-float(pred)) / nsamp)
    lab_ = {A_: 'AC', B_: '2C', C_: '3C'}
    desc = ", ".join(f"{lab_[c]}->row{r}" for c, r in place.items())
    print(f"   3-cycle {desc:30s} predicted {str(pred):>8s} = {float(pred):.5f}  observed {p:.5f} ({hit} hits, z = {(p-float(pred))/se:+.2f})")
    ok(abs(p - float(pred)) < 4.5*se and hit >= 50, f"{desc}: observed matches prod rho (with >= 50 expected hits)")

# ------------------------------------------------------------------------------------------------
hdr("3. Case A, SIDE ROUTE of PROOF.md section 8 (uses the exhaustive Lemma R p0 <= 1/11). m = 52 - (largest delta class).\n"
    "   The MAIN route (A1)-(A3) is checked in section 3c and section 6.")
q = lambda m: Fr(4*math.comb(13, m), math.comb(52, m))
bA2 = Fr(39, 51) * Fr(1, 169)
print(f"   m = 2  : bound (exact) 39/51 * 1/169 = {bA2} = 1/{1/bA2}")
worst = max((10*q(m)+1)/121 for m in range(3, 13))
print(f"   3<=m<=12: bound (10 q_m + 1)/121, q_m = 4 C(13,m)/C(52,m); worst m=3: q_3 = {q(3)} -> {float(worst):.6f} = 1/{float(1/worst):.2f}")
PI0 = Fr(math.comb(39, 13) + 1, math.comb(52, 13))
P01 = Fr(math.comb(39, 26), math.comb(52, 26)) + Fr(12*math.comb(26, 13)**2, math.comb(52, 13)*math.comb(39, 13))
bA3 = Fr(1, 121) + 2*PI0/11 + P01
print(f"   m >= 13: P[row const] <= {float(PI0):.6f}, P[rows 0,1 const] <= {float(P01):.3g}; bound 1/121 + 2*{float(PI0):.5f}/11 + ... = {float(bA3):.6f} = 1/{float(1/bA3):.2f}")
ok(max(bA2, worst, bA3) < Fr(1, 64), f"all Case A bounds < 1/64 = 0.015625 (max = {float(max(bA2, worst, bA3)):.6f})")
# smoothing claims used: max sum C(n_v,13) with sum n = 52, n_v <= 39 is C(39,13)+1 ; brute force over partitions
def partitions(n, k, mx):
    if k == 0:
        if n == 0: yield ()
        return
    for a in range(min(n, mx), -1, -1):
        for rest in partitions(n - a, k - 1, a): yield (a,) + rest
best13 = best26 = bestpair = 0
for part in partitions(52, 13, 39):
    best13 = max(best13, sum(math.comb(a, 13) for a in part))
    best26 = max(best26, sum(math.comb(a, 26) for a in part))
    bestpair = max(bestpair, sum(math.comb(a, 13)*math.comb(b, 13) for i, a in enumerate(part) for j, b in enumerate(part) if i != j))
ok(best13 == math.comb(39, 13) + 1 and best26 <= math.comb(39, 26) and bestpair <= 12*math.comb(26, 13)**2,
   f"smoothing facts over all partitions of 52 into <=13 parts each <=39: max sum C(n,13)={best13}, max sum C(n,26)={best26}, max pair-sum={bestpair}")

hdr("3b. Case A: exact row-only survival E[prod rho] vs model Monte Carlo vs bound, for many rank-changing tau")
def exact_rowonly_small(tau):
    """exact E_partition[prod rho] when few cards have delta != majority: enumerate row assignments of those cards."""
    dl = [delta(tau, c) for c in range(52)]; maj = Counter(dl).most_common(1)[0][0]
    moved = [c for c in range(52) if dl[c] != maj]; m = len(moved)
    tot = Fr(0)
    for rows in itertools.product(range(4), repeat=m):
        cnt = Counter(rows)
        if any(v > 13 for v in cnt.values()): continue
        # probability of this labelled row assignment
        pr = Fr(1); used = Counter()
        for r in rows: pr *= Fr(13 - used[r], 52 - sum(used.values())); used[r] += 1
        val = Fr(1)
        for r in range(4):
            vals = [dl[c] for c, rr in zip(moved, rows) if rr == r]
            if vals: val *= rho([maj]*(13-len(vals)) + vals)
        tot += pr * val
    return tot, m
def mc_rowonly(tau, n):
    hit = 0
    for _ in range(n): hit += row_amounts_agree(tau, rand_grid())
    return hit / n
def mc_full(tau, n, seed): return sb.same_only(sb.u8(tau), n, seed) / n
def boundA(m):
    if m == 2: return bA2
    if m <= 12: return (10*q(m)+1)/121
    return bA3
cases = [("same-suit swap 2C<->7C", cyc([C('C','2'), C('C','7')])),
         ("same-suit 3-cycle AC->2C->3C", cyc([C('C','A'), C('C','2'), C('C','3')])),
         ("same-suit 3-cycle AC->8C->JC", cyc([C('C','A'), C('C','8'), C('C','J')])),
         ("same-suit 4-cycle", cyc([C('C', r) for r in range(4)])),
         ("(AC 2C)(5C 6C)", cyc([C('C','A'), C('C','2')], [C('C','5'), C('C','6')])),
         ("mixed swap AC<->2H", cyc([C('C','A'), C('H','2')])),
         ("mixed 3-cycle AC->5H->9S", cyc([C('C','A'), C('H','5'), C('S','9')]))]
for name, tau in cases:
    ex, m = exact_rowonly_small(tau)
    mc = mc_rowonly(tau, 40000); se = math.sqrt(float(ex)*(1-float(ex))/40000)
    full = mc_full(tau, 400000, 7)
    print(f"   {name:32s} m={m:2d} exact row-only {float(ex):.6f} (={ex if ex.denominator<10**7 else '...'}) MC row-only {mc:.6f} full MC {full:.6f}  bound {float(boundA(m)):.6f}")
    ok(abs(mc - float(ex)) < 4.5*se + 1e-9 and full <= float(ex) + 4.5*math.sqrt(float(ex)/400000) + 1e-9 and ex <= boundA(m), f"{name}: exact formula matches model, full <= row-only <= bound")
ex3, _ = exact_rowonly_small(cyc([C('C','A'), C('C','2'), C('C','3')]))
ok(ex3 == Fr(9, 1105), f"same-suit 3-cycle row-only exact = {ex3} (README: 9/1105)")
ex2, _ = exact_rowonly_small(cyc([C('C','2'), C('C','7')]))
ok(ex2 == Fr(1, 221), f"same-suit swap row-only exact = {ex2} (README: 1/221)")
# large-m examples: Monte Carlo over partitions of E[prod rho] and direct MC of the model's row agreement
def mc_prod_rho(tau, n):
    dl = [delta(tau, c) for c in range(52)]; s = 0.0
    for _ in range(n):
        g = rand_grid(); v = 1.0
        for i in range(4): v *= float(rho([dl[c] for c in g[13*i:13*i+13]]))
        s += v
    return s / n
big = [("rank shift in clubs (13-cycle)", cyc([C('C', r) for r in range(13)])),
       ("rank x2 on every card", [13*(c//13) + (2*(c % 13)) % 13 for c in range(52)]),
       ("uniformly random permutation", None)]
for name, tau in big:
    if tau is None: tau = list(range(52)); R.shuffle(tau)
    dl = [delta(tau, c) for c in range(52)]; m = 52 - Counter(dl).most_common(1)[0][1]
    e = mc_prod_rho(tau, 3000); mc = mc_rowonly(tau, 60000)
    print(f"   {name:32s} m={m:2d}  E[prod rho] (MC over partitions) {e:.3g}   model row-only MC {mc:.3g}   bound {float(boundA(m)):.4f}")
    ok(e < float(boundA(m)) and mc < float(boundA(m)), f"{name}: well below the Case A bound")

# ------------------------------------------------------------------------------------------------
hdr("3c. Case A, MAIN route (PROOF.md section 3: A1 n*=50, A2 9<=n*<=49 via h(z*), A3 n*<=12 via pigeonhole)")
def h_(z): return Fr(1) if z == 13 else Fr(1, z+1)
def E_A(ns):
    tot = Fr(0)
    for zs in itertools.product(range(14), repeat=3):
        z3 = ns - sum(zs)
        if 0 <= z3 <= 13:
            zz = zs + (z3,)
            tot += Fr(math.prod(math.comb(13, z) for z in zz), math.comb(52, ns)) * math.prod(h_(z) for z in zz)
    return tot
PIG = Fr(1, 81) + 4*Fr(4**13, math.comb(52, 13))
def main_bound(ns):
    if ns == 50: return Fr(1, 221)
    if ns >= 9: return E_A(ns)
    return PIG
def nstar(tau): return Counter(delta(tau, c) for c in range(52)).most_common(1)[0][1]
# (i) per-partition inequality behind A2 and A3, on random partitions for several tau
def per_partition_ok(tau, trials):
    dl = [delta(tau, c) for c in range(52)]; cnt = Counter(dl); vstar, ns = cnt.most_common(1)[0]
    bad = 0
    for _ in range(trials):
        g = rand_grid(); rows = [[dl[c] for c in g[13*i:13*i+13]] for i in range(4)]
        prod_rho = math.prod(rho(r) for r in rows)
        if 9 <= ns <= 49:
            bad += prod_rho > math.prod(h_(r.count(vstar)) for r in rows)        # (A2): rho_r <= h(z*_r)
        if ns <= 12:
            if all(len(set(r)) < 13 for r in rows): bad += prod_rho > Fr(1, 81)   # (A3): rows with a repeat give <= 1/3
    return bad
pp_cases = [("same-suit 3-cycle", tau3), ("same-suit 5-cycle", cyc([C('C', r) for r in range(5)])),
            ("rank shift in clubs (13-cycle)", cyc([C('C', r) for r in range(13)])),
            ("rank +1 on C,H,S", [13*(c//13) + ((c % 13 + 1) % 13 if c < 39 else c % 13) for c in range(52)]),
            ("rank x2 on every card (n*=4)", [13*(c//13) + (2*(c % 13)) % 13 for c in range(52)]),
            ("rank negation (n*=4)", [13*(c//13) + (-(c % 13)) % 13 for c in range(52)])]
for name, tau in pp_cases:
    b = per_partition_ok(tau, 150)
    ok(b == 0, f"{name} (n*={nstar(tau)}): prod rho <= prod h(z*) (A2) / <= 1/81 when every row repeats a value (A3), 150 random partitions")
# (ii) exact / Monte Carlo survival of concrete tau against the MAIN-route bound for their n*
for name, tau in cases + [(n_, t_) for n_, t_ in pp_cases[2:]]:
    ns = nstar(tau); bnd = main_bound(ns)
    full = mc_full(tau, 400000, 17); tol = 4.5*math.sqrt(float(bnd)/400000)
    ok(full <= float(bnd) + tol, f"{name:34s} n*={ns:2d}: full model survival {full:.6f} <= main-route bound {float(bnd):.6f} (+4.5 se = {tol:.6f}; the n*=50 bound 1/221 is exact for same-suit swaps)")
ok(max(main_bound(ns) for ns in list(range(4, 13)) + list(range(9, 51))) < Fr(1, 64),
   f"main route: max over all n* in [4,50] of the bound = {float(max(main_bound(ns) for ns in range(4, 51))):.6f} < 1/64")

# ------------------------------------------------------------------------------------------------
hdr("4. Case B (delta constant): per-column table, exact transfer-matrix formula, exhaustive scan")
# column phi table
def colV_dist(ms):
    c = Counter(Vvec(p) for p in itertools.permutations(ms)); return {t: Fr(c[t], 24) for t in range(4)}
def ctype(ms):
    k = Counter(ms)
    if len(k) == 1: return 'Z'
    if len(k) == 2 and max(k.values()) == 2: return 'P'
    if len(k) == 4: return 'F'
    return 'U'
tab_ok = True
for ms in itertools.combinations_with_replacement(range(4), 4):
    d = colV_dist(ms); t = ctype(ms); s = Svec(ms)
    want = {'Z': {0: 1}, 'P': {0: 0, 1: Fr(1, 3), 2: Fr(1, 3), 3: Fr(1, 3)}, 'F': {0: Fr(1, 2), 1: Fr(1, 6), 2: Fr(1, 6), 3: Fr(1, 6)},
            'U': {x: Fr(1, 4) for x in range(4)}}[t]
    tab_ok &= all(d[x] == want.get(x, 0) for x in range(4)) and ((s != 0) == (t == 'U'))
ok(tab_ok, "V(eps) distribution under a uniform column order: Z->{0}, P->uniform on nonzero, F->(1/2,1/6,1/6,1/6), else uniform; S!=0 <=> type U")
subprocess.check_call(["gcc", "-O2", "-fopenmp", "-o", "build/caseB_tm", "caseB_tm.c", "-lm"])
def F_tm(n): return float(subprocess.check_output(["build/caseB_tm"] + [str(x) for x in n]).decode().split("=")[1])
for name, tau, n in [("same-rank 3-cycle 2C->2H->2S", cyc([C('C','2'), C('H','2'), C('S','2')]), None),
                     ("label+1 on rank 2 (2C<->2D)(2H<->2S)", cyc([C('C','2'), C('D','2')], [C('H','2'), C('S','2')]), None),
                     ("same-rank swaps on ranks 2,3,4", cyc([C('C','2'), C('H','2')], [C('C','3'), C('S','3')], [C('H','4'), C('D','4')]), None),
                     ("same-rank 3-cycles on 5 ranks", cyc(*[[C('C',r), C('H',r), C('S',r)] for r in range(5)]), None),
                     ("label x w on ranks 0..3 (suit 3-cycles incl. clubs fixed)", None, None),
                     ("random suit permutation on every rank", None, None)]:
    if tau is None and name.startswith("label x w"):
        tau = list(range(52))
        for r in range(4):
            for s in range(4):
                inv = {0: 0, 2: 1, 3: 2, 1: 3}; tau[13*s+r] = 13*inv[mulw(lab(13*s+r))] + r
    if tau is None:
        tau = list(range(52))
        for r in range(13):
            p = list(range(4)); R.shuffle(p)
            for s in range(4): tau[13*s+r] = 13*p[s] + r
    assert all(rk(tau[c]) == rk(c) for c in range(52))
    e = Counter(eps(tau, c) for c in range(52)); n = sorted([e[x] for x in range(4)], reverse=True)
    f = F_tm(n); N = 2_000_000; mc = mc_full(tau, N, 11); se = math.sqrt(max(f*(1-f), 1e-15)/N)
    print(f"   {name:52s} eps counts {n}  exact F = {f:.4g}  model MC {mc:.4g} (|z|={abs(mc-f)/max(se,1e-12):.2f})")
    ok(abs(mc - f) < 4.5*se + 2/N, f"{name}: transfer-matrix exact value matches the model")
ok(abs(F_tm([49, 1, 1, 1]) - 1/850) < 1e-12 and abs(F_tm([48, 4, 0, 0]) - 3/20825) < 1e-12 and F_tm([50, 2, 0, 0]) == 0,
   "transfer matrix reproduces exact.py: same-rank 3-cycle 1/850, label map on one rank 3/20825, same-rank swap 0")
# conditional exactness: fix the column sets of H, shuffle inside columns, undo the row phase
tau = cyc([C('C','2'), C('H','2'), C('S','2')])
h = rand_grid()
for c, cell in zip([C('C','2'), C('H','2'), C('S','2')], [13*0+5, 13*2+5, 13*3+5]):
    k = h.index(c); h[k], h[cell] = h[cell], h[k]
cols = [[h[13*i+j] for i in range(4)] for j in range(13)]
phi = {('Z', 0): 1, ('Z', 1): 0, ('P', 1): Fr(1, 3), ('P', 0): 0, ('F', 0): Fr(1, 2), ('F', 1): Fr(1, 6), ('U', 0): Fr(1, 4), ('U', 1): Fr(1, 4)}
pred = Fr(1)
for j in range(13):
    e = [eps(tau, c) for c in cols[j]]; en = [eps(tau, c) for c in cols[(j+1) % 13]]
    pred *= phi[(ctype(e), int(Svec(en) != 0))]
hit = 0; NS = 30000
for _ in range(NS):
    hh = [None]*52
    for j in range(13):
        cc = cols[j][:]; R.shuffle(cc)
        for i in range(4): hh[13*i+j] = cc[i]
    hit += survives(tau, inv_row_phase(hh))
se = math.sqrt(float(pred)*(1-float(pred))/NS)
print(f"   fixed H-column sets (3-cycle cards in column 5): predicted prod phi = {pred} ; observed {hit/NS:.4f}")
ok(abs(hit/NS - float(pred)) < 4.5*se, "given the column sets of H, survival = prod_c phi(M_c, S(M_{c+1})) exactly")
out = subprocess.check_output(["build/caseB_tm"]).decode(); print(out)
ok("max F = 0.001176470588 = 1/850.000" in out, "exhaustive: over ALL 1284 eps-count vectors (nonconstant), Case B survival <= 1/850"
   " (the argmax listed, (49,3,0,0), is NOT realisable since sum eps must be 0; harmless, it only over-covers)")
ok("restricted to realisable vectors (sum eps = 0, i.e. #odd counts != 2): 374 vectors, max F = 0.001176470588 = 1/850.000 at (49,1,1,1)" in out,
   "restricted to vectors compatible with sum(eps)=0: max is still exactly 1/850, attained at (49,1,1,1) = the same-rank 3-cycle")
# analytic large-m' bound
beta = 2 ** (-1/3)
def worst_q(mp, j):
    n0 = 52 - mp; rem = mp; s = 0
    while rem > 0:
        a = min(n0, rem); s += math.comb(a, 4); rem -= a
    return s
okall = True
for mp in range(20, 40):
    s4 = worst_q(mp, 0)
    Ez = sum(math.comb(13, j) * (beta**-4 - 1)**j * math.prod(min(1.0, s4 / math.comb(52 - 4*i, 4)) for i in range(j)) for j in range(14))
    b = beta**mp * Ez; okall &= b < 1/64
    print(f"   m'={mp}: analytic bound beta^m' * E[beta^(-4 z4)] <= {b:.5f}")
ok(okall, "analytic Case B bound (no transfer matrix) < 1/64 for every m' >= 20")

# ------------------------------------------------------------------------------------------------
hdr("6. The computer-free route used in PROOF.md (Theorems A and B): one-parameter exact sums")
# Case A, regime n* <= 12: pigeonhole
p13 = Fr(4**13, math.comb(52, 13))
bP = Fr(1, 81) + 4*p13
# check AM-GM claim: max prod n_v over 13 nonneg integers summing to 52 is 4^13
ok(max(math.prod(p) for p in partitions(52, 13, 52)) == 4**13, "max over partitions of 52 into 13 parts of prod n_v = 4^13 (AM-GM)")
print(f"   n* <= 12: E[prod rho] <= 1/81 + 4*4^13/C(52,13) = {float(bP):.6f}")
# one-card bound with the row's own largest class: rows with >=2 equal values have rho <= 1/3
bad = 0
for _ in range(300):
    vals = [R.randrange(13) for _ in range(13)]
    if len(set(vals)) in (1, 13): continue
    d = dist(vals); z = max(Counter(vals).values()); bad += max(d) > Fr(1, 3) and z >= 2
ok(bad == 0, "rows with a repeated value: every P[S=c] <= 1/3 (300 random high-entropy rows)")
# Case A, regime 9 <= n* <= 49: E[prod h(z*_i)]
def h(z): return Fr(1) if z == 13 else Fr(1, z+1)
worstA = Fr(0)
for ns in range(9, 50):
    tot = Fr(0)
    for zs in itertools.product(range(14), repeat=3):
        z3 = ns - sum(zs)
        if not 0 <= z3 <= 13: continue
        zz = zs + (z3,)
        tot += Fr(math.prod(math.comb(13, z) for z in zz), math.comb(52, ns)) * math.prod(h(z) for z in zz)
    worstA = max(worstA, tot)
print(f"   9 <= n* <= 49: max_n* E[prod h(z*_i)] = {float(worstA):.6f}")
ok(max(bP, worstA, bA2) < Fr(1, 64), f"Theorem A (computer-free route): all regimes < 1/64; max = {float(max(bP, worstA, bA2)):.6f} = 1/{float(1/max(bP, worstA, bA2)):.1f}")
# Case B: column bound f(y, y') and the m' table
def fB(y, yn):
    if y == 0: return Fr(0) if yn == 1 else Fr(1)
    return [None, Fr(1, 4), Fr(1, 3), Fr(1, 2), Fr(1)][y]
good = True
for estar in range(4):
    for ms in itertools.product(range(4), repeat=4):
        y = sum(e != estar for e in ms); d = colV_dist(ms)
        for ms2 in itertools.product(range(4), repeat=4):
            yn = sum(e != estar for e in ms2); target = Svec(ms2)
            if d[target] > fB(y, yn): good = False
ok(good, "phi(M_c, S(M_{c+1})) <= f(y_c, y_{c+1}) for every pair of columns and every majority value eps* (65536 x 4 cases)")
outB = subprocess.check_output([sys.executable, "caseB_analytic.py"]).decode()
vals = {int(l.split("=")[1].split()[0]): float(l.split("bound =")[1].split("=")[0]) for l in outB.splitlines() if l.startswith("m'=")}
print("   m' table (first/last lines):", {k: f"{v:.3g}" for k, v in list(vals.items())[:4]}, "...", {k: f"{v:.3g}" for k, v in list(vals.items())[-2:]})
ok(max(v for k, v in vals.items() if k >= 3) < 1/64, f"Theorem B (computer-free route): for m' >= 3 the bound is <= {max(v for k, v in vals.items() if k >= 3):.4g} = 1/{1/max(v for k, v in vals.items() if k >= 3):.0f}")
ok(F_tm([50, 2, 0, 0]) == 0 and mc_full(cyc([C('C','2'), C('H','2')]), 400000, 5) == 0 and mc_full(cyc([C('C','K'), C('D','K')]), 400000, 6) == 0,
   "m' = 2 (a same-rank swap, possibly composed with a symmetry) never survives: exact 0, and 0 in 400k model decks each")
ok(mc_full([v10sym(3, 0)[c] for c in cyc([C('C','2'), C('H','2')])], 400000, 8) == 0, "same-rank swap composed with rank+3 symmetry: 0 in 400k")

# ------------------------------------------------------------------------------------------------
hdr("7. Corollary (PROOF.md section 5b): the exact supremum over non-symmetries is 9/1105, attained by same-suit 3-cycles\n"
    "   (uses the computer-checked Lemma R only in the regime n* <= 12)")
def rowonly_offs(offs):
    """exact E[prod rho] when the majority delta value is 0 (normalised by a symmetry) and the off cards have values offs."""
    m = len(offs); tot = Fr(0)
    for rows in itertools.product(range(4), repeat=m):
        p = Fr(1); used = [0]*4
        for i, r in enumerate(rows): p *= Fr(13 - used[r], 52 - i); used[r] += 1
        v = Fr(1)
        for r in range(4):
            o = [d for d, rr in zip(offs, rows) if rr == r]
            if o: v *= rho([0]*(13-len(o)) + o)
        tot += p*v
    return tot
classes49 = {}
for offs in itertools.combinations_with_replacement(range(1, 13), 3):
    if sum(offs) % 13: continue
    can = min(tuple(sorted(a*x % 13 for x in offs)) for a in range(1, 13))
    classes49.setdefault(can, rowonly_offs(list(can)))
print("   n* = 49 delta-classes (off values up to scaling) and exact row-only survival:", {k: str(v) for k, v in classes49.items()})
ok(all(v == Fr(9, 1105) for v in classes49.values()), "n* = 49: EVERY delta-class has row-only survival exactly 9/1105 (so full survival <= 9/1105)")
mid = max(E_A(ns) for ns in range(13, 49))
ok(mid <= Fr(3976, 10**6) and mid == E_A(13), f"13 <= n* <= 48: E_A <= E_A(13) = {float(E_A(13)):.6f} < 9/1105")
ok(Fr(1, 11**4) < Fr(9, 1105) and Fr(1, 221) < Fr(9, 1105) and Fr(1, 425) < Fr(9, 1105),
   "n* <= 12: <= 11^-4 (all four rows nonconstant, Lemma R); n* = 50: 1/221; Case B: <= 1/425 -- all < 9/1105")
ok(ex3 == Fr(9, 1105), "attained: same-suit 3-cycles have eps = 0, so full survival = row-only = 9/1105 exactly")

# ------------------------------------------------------------------------------------------------
hdr("5. Theorem sanity: full-model survival of many random non-symmetry tau and the worst known classes")
worst_seen = 0
for _ in range(40):
    k = R.choice([2, 3, 3, 3, 4, 5, 8, 52]); tau = list(range(52))
    if k == 52: R.shuffle(tau)
    else: tau = cyc(R.sample(range(52), k))
    p = mc_full(tau, 100000, R.randrange(1 << 30)); worst_seen = max(worst_seen, p)
for name, tau in cases[:3]:
    worst_seen = max(worst_seen, mc_full(tau, 400000, 3))
print(f"   max observed survival over tested tau = {worst_seen:.5f}  (1/64 = 0.015625)")
ok(worst_seen < 1/64, "no tested non-symmetry tau reaches 1/64")
print(f"\nTOTAL FAILS: {ok.fails}   ({time.time()-T0:.0f}s)")
