"""Physical simulation of the SPEC BUILD rule ("grow until it bumps"), as a player does it
with the former one-d6 wording and ship pieces (same distribution as the SPEC's d12 hole die,
../randomizer-kit/ part B), counting rolls and moves; chi-square against the exact model;
READ-rule statistics on the results."""
import random, math, json, collections, statistics
from read_rule import encode, bs_decode_exponent, bs_exponent, KL
from rules import extra_rules
from sim_build import model_logp
from brute_build import enumerate_build
from pathlib import Path
HERE = Path(__file__).resolve().parent            # every file path is anchored on this script's directory

def build_bump(rng, n=10, m=10, st=None):
    occ = [[None] * m for _ in range(n)]
    ships = []; rolls = 0; moves = 0
    def d6():
        nonlocal rolls; rolls += 1; return rng.randint(1, 6)
    def room(r, c, dr, dc, L):
        return all(r + dr * t < n and c + dc * t < m and occ[r + dr * t][c + dc * t] is None for t in range(L))
    while True:
        pos = next(((r, c) for r in range(n) for c in range(m) if occ[r][c] is None), None)
        if pos is None: break
        r, c = pos
        while True:
            if d6() <= 2:
                occ[r][c] = "."; moves += 1; break               # miss peg
            dr, dc = (0, 1) if d6() <= 3 else (1, 0)            # low across, high down
            if not room(r, c, dr, dc, 2): continue               # no room for a Destroyer: roll again
            L = 2; moves += 1                                     # lay a Destroyer
            for need in (4, 6, 6):                                # grow on 4-6, then only on a 6, then on a 6
                if not room(r, c, dr, dc, L + 1): break           # bumped: stays as it is (no roll)
                if d6() >= need: L += 1; moves += 2              # swap for the next longer piece
                else: break
            K = {2: "D", 4: "B", 5: "A"}.get(L)
            if L == 3:
                K = "S" if d6() <= 3 else "C"
                if K == "S": moves += 2                            # placeholder 3-holer was a Cruiser
            bow = 0 if d6() <= 3 else 1                          # low: bow at the first hole
            moves += bow                                          # turn the piece round if needed
            for t in range(L): occ[r + dr * t][c + dc * t] = K
            ships.append((K, "H" if dc else "V", (r, c), bow)); break
    if st is not None: st["rolls"] += rolls; st["moves"] += moves; st["ships"] += len(ships)
    return ships

if __name__ == "__main__":
    rule = extra_rules()["bump_reroll"]
    rng = random.Random(77)
    out = {}
    for g in [(2, 3), (3, 3), (3, 4)]:
        exact = enumerate_build(rule, *g)
        ex = {}
        for k, p in exact.items():
            kk = tuple(sorted((K, o, c0, b) for K, o, c0, b in k)); ex[kk] = ex.get(kk, 0) + p
        N = 300000
        cnt = collections.Counter(tuple(sorted(build_bump(rng, *g))) for _ in range(N))
        assert set(cnt) <= set(ex)
        chi = sum((cnt[k] - N * p) ** 2 / (N * p) for k, p in ex.items())
        out[f"chi2_{g[0]}x{g[1]}"] = [chi, len(ex) - 1]
        print(f"chi-square {g}: {chi:.1f} on {len(ex)-1} df", flush=True)
    st = collections.Counter(); N = 20000
    cells = []; hits = []; nz = []; lps = []; kinds = collections.Counter(); miss = 0; heads = collections.Counter()
    for _ in range(N):
        sh = build_bump(rng, st=st)
        t = encode(sh); assert bs_decode_exponent(bs_exponent(t)) == sorted(sh)
        cells.append(len(t)); hits.append(sum(t)); nz.append(sum(1 for x in t if x))
        kinds.update(s[0] for s in sh); heads.update(s[1] for s in sh)
        miss += 100 - sum(KL[s[0]] for s in sh)
        lps.append(-model_logp(rule, sh))
    out.update({"N": N, "rolls": st["rolls"] / N, "piece_moves": st["moves"] / N, "ships": st["ships"] / N,
                "miss_pegs": miss / N, "cells": statistics.mean(cells), "cells_max_seen": max(cells),
                "hit_units": statistics.mean(hits), "nonzero_cells": statistics.mean(nz),
                "kinds": {k: v / N for k, v in kinds.items()}, "across_frac": heads["H"] / (heads["H"] + heads["V"]),
                "MC_H": statistics.mean(lps), "MC_H_se": statistics.stdev(lps) / math.sqrt(N)})
    print(json.dumps(out, indent=1))
    json.dump(out, open(HERE / "sim_bump_results.json", "w"), indent=1)
