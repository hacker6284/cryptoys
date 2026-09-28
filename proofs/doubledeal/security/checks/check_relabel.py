"""T1 sanity checks for the relabelling statements (v8, v9, v10 and v11 ports)."""
import random, itertools, ddport as P
from dd_v8 import suit, rank, lay_cm, scoop_cm, shift_rows, compose, passkey
rng = random.Random(2026)
def rdeck(): d = list(range(52)); rng.shuffle(d); return d
def app(s, d): return [s[x] for x in d]
def appg(s, g): return [[s[x] for x in row] for row in g]
def transp(a, b): s = list(range(52)); s[a], s[b] = b, a; return s
ID = list(range(52))
card = lambda r, su: su * 13 + (r - 1)   # rank 1..13, suit 0..3
KC, KH, KS, KD = card(13,0), card(13,1), card(13,2), card(13,3)

# 1. positional layers commute with every sigma; key not relabelled
for _ in range(200):
    s, m, k = rdeck(), rdeck(), rdeck()
    assert compose(app(s, m), k) == app(s, compose(m, k))
    assert shift_rows(appg(s, lay_cm(m))) == appg(s, shift_rows(lay_cm(m)))
    assert scoop_cm(appg(s, lay_cm(m))) == app(s, m)
bad_key = sum(compose(m, app(s, k)) != app(s, compose(m, k)) for s, m, k in ((rdeck(), rdeck(), rdeck()) for _ in range(200)))
bad_both = sum(compose(app(s, m), app(s, k)) != app(s, compose(m, k)) for s, m, k in ((rdeck(), rdeck(), rdeck()) for _ in range(200)))
print(f"[1] compose/shift/lay/scoop commute with 200 random sigma; key-relabelled forms fail {bad_key}/200 (C(M,sK) vs sC) and {bad_both}/200 (C(sM,sK) vs sC)")
passfail = sum(passkey(app(s, k)) != app(s, passkey(k)) for s, k in ((rdeck(), rdeck()) for _ in range(200)))
print(f"    PassKey(sK) != s PassKey(K) in {passfail}/200 (schedule is value-dependent)")

# 2. weight-shift characterisation
def shifts(s, w, mod):
    ks = {(w(s[c]) - w(c)) % mod for c in range(52)}
    return len(ks) == 1
def commutes_sr(s, v, trials=20, decks=None):
    for m in (decks or [rdeck() for _ in range(trials)]):
        g = lay_cm(m)
        if P.sum_ranks(appg(s, g), v) != appg(s, P.sum_ranks(g, v)): return False
    return True
colw = {8: rank, 9: lambda x: rank(x) + suit(x)}
# v9 group: sigma_{a,b}
sig9 = P.v9sym
G = [sig9(a, b) for a in range(13) for b in range(4)]
assert all(sorted(s) == ID for s in G) and len({tuple(s) for s in G}) == 52
assert all(shifts(s, rank, 13) and shifts(s, colw[9], 4) for s in G)
assert all(commutes_sr(s, 9) for s in G)
print("[2] v9: all 52 sigma_{a,b} are bijections, weight-shift, and commute with SumRanks on 20 random decks each")
print("    e.g. sigma_{0,1}:", ' '.join(f"{c}->{G[1][c]}" for c in (0, 13, 26, 39)), "(A♣->A♥->A♠->A♦->A♣)")
# uniqueness: (rank mod 13, colw mod 4) determines the card
assert len({(rank(c) % 13, colw[9](c) % 4) for c in range(52)}) == 52
# only-if plan: explicit pair-swap witness decks (no random search)
def rows_of(g): return [row[:] for row in g]
def row_witness(s, v):
    """Two decks differing by a<->b (a in row 0, b in row 1); one must fail."""
    d = {c: (rank(s[c]) - rank(c)) % 13 for c in range(52)}
    a = 0; b = next(c for c in range(52) if d[c] != d[a])
    rest = [c for c in range(52) if c not in (a, b)]
    g1 = [[a] + rest[:12], [b] + rest[12:24], rest[24:37], rest[37:50]]
    g2 = [[b] + rest[:12], [a] + rest[12:24], rest[24:37], rest[37:50]]
    return [g1, g2]
def col_witness(s, v):
    """Row shift holds: pick the post-row grid with a / b in column 0."""
    w = colw[v]
    d = {c: (w(s[c]) - w(c)) % 4 for c in range(52)}
    a = 0; b = next(c for c in range(52) if d[c] != d[a])
    rest = [c for c in range(52) if c not in (a, b)]
    out = []
    for x, y in ((a, b), (b, a)):
        # column 0 = {x, t1, t2, t3}; y sits in column 1
        h = [[x, y] + rest[0:11], rest[11:24], rest[24:37], rest[37:50]]
        # undo the row stage: rotate each row right by its rank sum
        g = [P.rotl(row, -(sum(rank(c) for c in row) % 13)) for row in h]
        out.append(g)
    return out
def witness_fails(s, v):
    for g in (row_witness(s, v) if not shifts(s, rank, 13) else col_witness(s, v)):
        if P.sum_ranks(appg(s, g), v) != appg(s, P.sum_ranks(g, v)): return True
    return False
def rank_pres():
    s = list(range(52))
    for r in range(1, 14):
        cs = [card(r, x) for x in range(4)]; p = cs[:]; rng.shuffle(p)
        for a, b in zip(cs, p): s[a] = b
    return s
for v in (8, 9):
    pool = [transp(a, b) for a, b in itertools.combinations(range(52), 2)] + G + [rdeck() for _ in range(500)] + [rank_pres() for _ in range(200)]
    n_shift = n_ok = 0
    for s in pool:
        pred = shifts(s, rank, 13) and shifts(s, colw[v], 4)
        if pred:
            n_shift += 1; n_ok += commutes_sr(s, v, 10)
        else:
            assert witness_fails(s, v), (v, s)
            n_ok += 1
    print(f"    v{v}: {len(pool)} sigma (1326 transpositions, 52 v9Sym, 500 random, 200 rank-preserving): "
          f"{n_shift} weight-shift -> commute on 10 random decks; all others fail on the explicit pair-swap witness deck ({n_ok}/{len(pool)} as predicted)")
same_rank = [(a, b) for a, b in itertools.combinations(range(52), 2) if rank(a) == rank(b)]
tr8 = [(a, b) for a, b in itertools.combinations(range(52), 2) if shifts(transp(a, b), rank, 13) and shifts(transp(a, b), rank, 4)]
tr9 = [(a, b) for a, b in itertools.combinations(range(52), 2) if shifts(transp(a, b), rank, 13) and shifts(transp(a, b), colw[9], 4)]
print(f"    transpositions with the shift property: v8 {len(tr8)} (= the 78 same-rank pairs: {tr8 == same_rank}), v9 {len(tr9)}")
print("    v8 shift <-> rank-preserving on pool:", all((shifts(s, rank, 13) and shifts(s, rank, 4)) == all(rank(s[c]) == rank(c) for c in range(52)) for s in G + [rdeck() for _ in range(100)] + [rank_pres() for _ in range(100)]),
      "; v9Sym ∩ rank-preserving =", [ (a, b) for a in range(13) for b in range(4) if all(rank(sig9(a, b)[c]) == rank(c) for c in range(52))], "(the 4 suit rotations)")
for v in (8, 9):
    rates = []
    for a, b in ((KC, KD), (0, 13), (0, 4)):
        s = transp(a, b); N = 2000
        rates.append(sum(commutes_sr(s, v, decks=[rdeck()]) for _ in range(N)) / N)
    print(f"    v{v}: per-deck SumRanks commute rate: K♣↔K♦ {rates[0]:.3f}, A♣↔A♥ {rates[1]:.3f}, A♣↔5♣ {rates[2]:.3f}")

# 2b. v10 SumRanks: the group v10Sym commutes, and nothing else does (both directions
# proved: sumRanksV10_commutes_iff in SumRanksV10Iff.lean). Numerical cross-check:
# every other sampled sigma fails on some random deck.
# [2b] draws from its own RNG (seed 10), so the v8/v9 lines after it keep their pre-v10 values.
_rng_main = rng; rng = random.Random(10)
sig10 = P.v10sym
G10 = [sig10(a, x) for a in range(13) for x in range(4)]
assert all(sorted(s) == ID for s in G10) and len({tuple(s) for s in G10}) == 52
assert all(commutes_sr(s, 10) for s in G10)
print("[2b] v10: all 52 v10Sym (rank + a, suit label XOR x) are bijections and commute with v10 SumRanks on 20 random decks each")
def fails_somewhere(s, v, tries=40):
    return any(P.sum_ranks(appg(s, lay_cm(m)), v) != appg(s, P.sum_ranks(lay_cm(m), v)) for m in (rdeck() for _ in range(tries)))
tr_all = [transp(a, b) for a, b in itertools.combinations(range(52), 2)]
n_tr = sum(fails_somewhere(s, 10) for s in tr_all)
g10set = {tuple(s) for s in G10}
rsig = [s for s in (rdeck() for _ in range(500)) if tuple(s) not in g10set]
n_rnd = sum(fails_somewhere(s, 10) for s in rsig)
g9_out = [s for s in G[1:] if tuple(s) not in g10set]
n_g9 = sum(fails_somewhere(s, 10) for s in g9_out)
print(f"    v10: SumRanks fails to commute (some deck out of 40) for {n_tr}/1326 transpositions, {n_rnd}/{len(rsig)} random sigma, "
      f"{n_g9}/{len(g9_out)} nontrivial v9Sym outside v10Sym (the other {51 - len(g9_out)}, v9Sym 0 2 = v10Sym 0 3, is in v10Sym)")
rates = []
for a, b in ((KC, card(12, 1)), (KC, KD), (0, 13), (0, 4)):
    s = transp(a, b); N = 2000
    rates.append(sum(commutes_sr(s, 10, decks=[rdeck()]) for _ in range(N)) / N)
print(f"    v10: per-deck SumRanks commute rate: K♣↔Q♥ {rates[0]:.4f}, K♣↔K♦ {rates[1]:.4f}, A♣↔A♥ {rates[2]:.4f}, A♣↔5♣ {rates[3]:.4f}")
rng = _rng_main

# 3. GridCycle
def seat2(c, v): return P.walk([c] + [x for x in range(52) if x != c], v)[1]
for v in (8, 9, 11):
    s2 = {c: seat2(c, v) for c in range(52)}
    coll = [(a, b) for a, b in itertools.combinations(range(52), 2) if s2[a] == s2[b]]
    print(f"[3] v{v}: seat2 collisions {coll}  (K♣={KC}, K♠={KS})")
def mix_commutes(s, m, v): return P.mix_columns(app(s, m), v) == app(s, P.mix_columns(m, v))
def cfirst(c): return [c] + [x for x in range(52) if x != c]
for v in (8, 9, 11):
    w = cfirst(KD)
    print(f"    v{v}: K♣<->K♦ on deck [K♦, 0..]: commutes? {mix_commutes(transp(KC, KD), w, v)}; seats of 2nd card {P.walk(w, v)[1]} vs {P.walk(app(transp(KC,KD), w), v)[1]}")
    # K♣<->K♠ special
    found = None
    for m in [cfirst(KC)] + [rdeck() for _ in range(50)]:
        if not mix_commutes(transp(KC, KS), m, v): found = m; break
    print(f"    v{v}: K♣<->K♠ witness found: {found is not None}; cfirst(K♣) works: {not mix_commutes(transp(KC, KS), cfirst(KC), v)}")
    # all transpositions fail GridCycle on the cfirst family (+ special)
    ok = all(any(not mix_commutes(transp(a, b), m, v) for m in (cfirst(a), cfirst(b), cfirst(KC) if {a,b}=={KC,KS} else cfirst(a))) for a, b in itertools.combinations(range(52), 2))
    print(f"    v{v}: every transposition fails GridCycle on a c-first deck: {ok}")
    # G52 elements fail GridCycle
    print(f"    v{v}: every nontrivial G52 element fails GridCycle on some c-first deck: {all(any(not mix_commutes(s, cfirst(c), v) for c in range(52)) for s in G[1:])}")
    # per-deck commute rate for K♣<->K♦
    N = 20000; hit = sum(mix_commutes(transp(KC, KD), rdeck(), v) for _ in range(N))
    print(f"    v{v}: GridCycle commutes with K♣<->K♦ on {hit}/{N} random decks")
    # walk criterion: commutes iff same seat sequence
    agree = 0
    for _ in range(3000):
        m = rdeck(); s = transp(KC, KD) if rng.random() < .5 else transp(*rng.sample(range(52), 2))
        agree += mix_commutes(s, m, v) == (P.walk(app(s, m), v) == P.walk(m, v))
    print(f"    v{v}: commute <-> equal walk on {agree}/3000")

# 4. round / encrypt level
for v in (8, 9, 10, 11):
    def rnd(m, k): return P.full_round(m, k, v)
    allfail = True
    for a, b in itertools.combinations(range(52), 2):
        s = transp(a, b)
        if all(rnd(app(s, m), k) == app(s, rnd(m, k)) for m, k in ((rdeck(), rdeck()) for _ in range(3))):
            allfail = False; print("   round commutes?", a, b)
    gfail = all(any(rnd(app(s, m), k) != app(s, rnd(m, k)) for m, k in ((rdeck(), rdeck()) for _ in range(3))) for s in (G10[1:] if v >= 10 else G[1:]))
    rfail = all(any(rnd(app(s, m), k) != app(s, rnd(m, k)) for m, k in ((rdeck(), rdeck()) for _ in range(3))) for s in (rdeck() for _ in range(200)))
    efail = all(P.encrypt(app(s, m), k, v) != app(s, P.encrypt(m, k, v)) for s, m, k in ((transp(*rng.sample(range(52), 2)), rdeck(), rdeck()) for _ in range(200)))
    print(f"[4] v{v}: full round fails for every transposition: {allfail}; every nontrivial {'v10Sym' if v >= 10 else 'G52'}: {gfail}; 200 random sigma: {rfail}; encrypt fails 200/200 random transposition trials: {efail}")
