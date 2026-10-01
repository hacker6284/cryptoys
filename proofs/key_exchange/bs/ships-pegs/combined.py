"""Ships + pegs key grid: the rules are BS SPEC §4.2 (BUILD) and §4.3 (READ, "ships, then pegs").
Checks here: exhaustive injectivity of the two-pass read (and, not used by the SPEC, an
interleaved order); the board-only one-pass BUILD with random let-go/resume at hole boundaries
(step() finishes the whole ship decision, growth and Sub/Cruiser rolls included, before a
let-go is allowed) against the exact joint model; 10x10 round trips, walk and build statistics.
step() uses the former d6 wording for the ship decision and the d6 peg fallback; they have
exactly the SPEC's distribution (../randomizer-kit/, part B; the row cup gives uniform trits).
The SPEC-literal dice are in keygrid.py."""
import math, random, itertools, json, collections, statistics, sys
from read_rule import encode, decode, all_layouts, KL
from sim_bump import build_bump
from rules import extra_rules
from sim_build import model_logp
from brute_build import enumerate_build
from pathlib import Path
HERE = Path(__file__).resolve().parent            # every file path is anchored on this script's directory

LOG3 = math.log2(3)

def encode_combined(ships, pegs, order="two-pass", n=10, m=10):
    f = encode(ships, n, m)
    if order == "two-pass":
        return f + list(pegs)
    # interleaved: per hole peg cell then its ship cells
    per = []; pos = 0; out = []
    # recover per-hole grouping of the fleet cells: 1 cell per hole, 2 at a Sub/Cruiser last hole
    extra = set()
    for K, o, (r, c), bow in ships:
        if KL[K] == 3:
            extra.add((r, c + 2) if o == "H" else (r + 2, c))
    for h in range(n * m):
        k = 2 if divmod(h, m) in extra else 1
        out += [pegs[h]] + f[pos:pos + k]; pos += k
    return out

def decode_combined(t, order="two-pass", n=10, m=10):
    if order == "two-pass":
        ships = decode(t[:-n * m], n, m); return ships, list(t[-n * m:])
    pegs = []; fl = []; pos = 0
    # the fleet decoder is sequential; feed it hole by hole
    # simple approach: split greedily using the fleet decoder's knowledge of the extra cell
    # (re-implemented: an extra cell follows the last hole of a 3-hole ship)
    cover = {}
    for h in range(n * m):
        r, c = divmod(h, m)
        pegs.append(t[pos]); pos += 1
        x = t[pos]; pos += 1; fl.append(x)
        if (r, c) in cover:
            o, k = cover.pop((r, c))
            if x == 0:
                cover[(r, c + 1) if o == "H" else (r + 1, c)] = (o, k + 1)
            elif k + 1 == 3:
                fl.append(t[pos]); pos += 1
        elif x:
            o = "H" if x == 1 else "V"
            cover[(r, c + 1) if o == "H" else (r + 1, c)] = (o, 1)
    assert pos == len(t)
    return decode(fl, n, m), pegs

def exponent(t):
    e = 1
    for x in t: e = 3 * e + x
    return e

def digits_after_marker(e):
    ds = []
    while e: ds.append(e % 3); e //= 3
    ds.reverse(); assert ds[0] == 1
    return ds[1:]

def exhaustive(n, m, order):
    seen = set(); cnt = 0
    for ships in all_layouts(n, m):
        for pegs in itertools.product(range(3), repeat=n * m):
            t = encode_combined(ships, pegs, order, n, m)
            e = exponent(t)
            assert e not in seen
            seen.add(e); cnt += 1
            s2, p2 = decode_combined(digits_after_marker(e), order, n, m)
            assert s2 == sorted(ships) and p2 == list(pegs)
    return cnt

# ---------------------------------------------------------------- physical build, board-only state
def new_board(n=10, m=10):
    return {"n": n, "m": m, "ship_at": {}, "ships": [], "peg": {}, "cursor": 0, "lane10": None}

def step(board, rng, stats):
    """One hands-off-to-hands-off step, reading ONLY the board.  Returns False when done.
    Half-steps: (a) the ship decision at the cursor hole (if no ship covers it), after which
    a white peg is stood in control-lane hole 10; (b) the peg roll, after which the lane
    peg is lifted and the cursor moved on.  Letting go is allowed after (a) or (b)."""
    n, m = board["n"], board["m"]
    h = board["cursor"]
    if h == n * m: return False
    r, c = divmod(h, m)
    def d6():
        stats["rolls"] += 1; return rng.randint(1, 6)
    if board["lane10"] is None:                              # half-step (a)
        if (r, c) not in board["ship_at"]:
            occ = lambda a, b: (a, b) in board["ship_at"]
            while True:
                if d6() <= 2: break                          # sea: nothing to lay
                dr, dc = (0, 1) if d6() <= 3 else (1, 0)
                room = lambda L: all(r + dr * t < n and c + dc * t < m and not occ(r + dr * t, c + dc * t) for t in range(L))
                if not room(2): continue
                L = 2; stats["moves"] += 1
                for need in (4, 6, 6):
                    if not room(L + 1): break
                    if d6() >= need: L += 1; stats["moves"] += 2
                    else: break
                K = {2: "D", 4: "B", 5: "A"}.get(L)
                if L == 3:
                    K = "S" if d6() <= 3 else "C"; stats["moves"] += 2 * (K == "S")
                bow = 0 if d6() <= 3 else 1; stats["moves"] += bow
                cells = [(r + dr * t, c + dc * t) for t in range(L)]
                for x in cells: board["ship_at"][x] = len(board["ships"])
                board["ships"].append((K, "H" if dc else "V", (r, c), bow)); break
        board["lane10"] = "W"; stats["moves"] += 1
        return True
    x = d6()                                                  # half-step (b)
    if x >= 3:
        board["peg"][(r, c)] = 1 if x <= 4 else 2; stats["moves"] += 1
    board["lane10"] = None; board["cursor"] += 1; stats["moves"] += 2   # lift lane peg, move cursor
    return True

def build_combined(rng, n=10, m=10, stats=None, letgo_prob=0.3):
    """Run step() to completion, 'letting go' at random step boundaries: the only thing
    carried between steps is the board dict itself (a fresh copy each time)."""
    stats = stats if stats is not None else collections.Counter()
    board = new_board(n, m)
    while True:
        if rng.random() < letgo_prob:
            board = json.loads(json.dumps({k: (list(v.items()) if isinstance(v, dict) else v)
                                           for k, v in board.items()}))
            board["ship_at"] = {tuple(k): v for k, v in board["ship_at"]}
            board["peg"] = {tuple(k): v for k, v in board["peg"]}
            board["ships"] = [(K, o, tuple(s), b) for K, o, s, b in board["ships"]]
        if not step(board, rng, stats): break
    pegs = [board["peg"].get(divmod(h, m), 0) for h in range(n * m)]
    return board["ships"], pegs

if __name__ == "__main__":
    out = {}
    rule = extra_rules()["bump_reroll"]
    R = {r["key"]: r for r in json.load(open(HERE / "rules_bump_turn_bump_reroll_grow_turn.json"))}["bump_reroll"]
    out["entropy"] = {"uniform_layout+pegs": 150.187464 + 100 * LOG3,
                      "bump_H": R["H"] + 100 * LOG3, "bump_H2": R["H2"] + 100 * LOG3, "bump_Hmin": R["Hmin"] + 100 * LOG3}
    print("entropy (bits):", json.dumps(out["entropy"]))
    print("== exhaustive injectivity (every layout x every peg pattern) ==")
    ex = {}
    for g in [(1, 2), (2, 1), (2, 2), (1, 5), (2, 3), (3, 2), (1, 7)]:
        for order in ("two-pass", "interleave"):
            k = exhaustive(*g, order); ex[f"{g[0]}x{g[1]} {order}"] = k
        print(f"  {g[0]}x{g[1]}: {k} keys, all distinct, decode = identity (both orders)", flush=True)
    out["exhaustive"] = ex
    print("== physical one-pass build (cursor + lane-10 marker) vs exact model, 2x2 and 2x3 ==")
    rng = random.Random(4242)
    for g in [(2, 2), (2, 3)]:
        exact = enumerate_build(rule, *g)
        exl = {}
        for kk, p in exact.items():
            key = tuple(sorted(kk)); exl[key] = exl.get(key, 0) + p
        N = 400000 if g == (2, 2) else 300000
        cnt = collections.Counter()
        for _ in range(N):
            sh, pg = build_combined(rng, *g)
            cnt[(tuple(sorted(sh)), tuple(pg))] += 1
        cells = g[0] * g[1]
        chi = 0.0; cats = 0
        for lk, p in exl.items():
            for pg in itertools.product(range(3), repeat=cells):
                e = N * p / 3 ** cells; chi += (cnt[(lk, pg)] - e) ** 2 / e; cats += 1
        assert sum(cnt.values()) == N and all(k[0] in exl for k in cnt)
        out[f"chi2_{g[0]}x{g[1]}"] = [chi, cats - 1]
        print(f"  {g}: chi-square {chi:.1f} on {cats-1} df", flush=True)
    print("== 10x10: 20000 builds, round trips, walk statistics ==")
    st = collections.Counter(); cells = []; hits = []; N = 20000
    for _ in range(N):
        sh, pg = build_combined(rng, stats=st)
        for order in ("two-pass", "interleave"):
            t = encode_combined(sh, pg, order)
            s2, p2 = decode_combined(digits_after_marker(exponent(t)), order)
            assert s2 == sorted(sh) and p2 == pg
        t = encode_combined(sh, pg)
        cells.append(len(t)); hits.append(sum(t))
    C, Hh = statistics.mean(cells), statistics.mean(hits)
    mults = 4 * C + Hh + 1
    SB = json.load(open(HERE / "sim_bump_results.json"))
    PEG = 500 - 5.5; FLEET = 4 * SB["cells"] + SB["hit_units"] + 1     # ship pass alone (as ../key-selection/costs.py)
    out["walk"] = {"cells": C, "cells_max_seen": max(cells), "cells_max_possible": 233, "hit_units": Hh,
                   "mults_per_grid": mults, "mults_per_H_bit": mults / out["entropy"]["bump_H"],
                   "mults_per_Hmin_bit": mults / out["entropy"]["bump_Hmin"],
                   "public_mults_per_bit": 2 * C / out["entropy"]["bump_H"],
                   "pegs_only_mults_per_bit": PEG / (100 * LOG3), "ships_only_mults_per_bit": FLEET / R["H"]}
    out["build"] = {"rolls": st["rolls"] / N, "moves_incl_cursor_and_lane": st["moves"] / N}
    print(json.dumps(out["walk"], indent=1)); print(json.dumps(out["build"]))
    # tiers
    mpm = {"R1024": 7.45e5, "R2048": 2.97e6, "R3072": 6.62e6, "R7680": 4.14e7, "R15360": 1.66e8}
    sec = {"R1024": 80, "R2048": 112, "R3072": 128, "R7680": 192, "R15360": 256}
    qbits = {"R1024": 1023, "R2048": 2047, "R3072": 3071, "R7680": 7679, "R15360": 15359}
    tiers = []
    for t, s in sec.items():
        gp = math.ceil(2 * s / (100 * LOG3)); cp = math.ceil(2 * s / LOG3)
        gH = math.ceil(2 * s / out["entropy"]["bump_H"]); gM = math.ceil(2 * s / out["entropy"]["bump_Hmin"])
        row = {"tier": t, "target": s, "pegs_grids": gp, "pegs_mults": 500 * gp - 5.5,
               "pegs_trim_cells": cp, "pegs_trim_mults": 5 * cp - 5.5,
               "comb_grids_H": gH, "comb_mults_H": gH * (4 * C + Hh) + 1,
               "comb_grids_Hmin": gM, "comb_mults_Hmin": gM * (4 * C + Hh) + 1,
               "injective_mod_q": all(1 + 1 + 233 * g * LOG3 < qbits[t] for g in (gH, gM))}
        for k in ("pegs_mults", "pegs_trim_mults", "comb_mults_H", "comb_mults_Hmin"):
            row[k.replace("mults", "moves")] = row[k] * mpm[t]
        tiers.append(row)
    out["tiers"] = tiers
    for r in tiers: print(r)
    json.dump(out, open(HERE / "combined_results.json", "w"), indent=1)
