"""Calling-rule checks (BS s3.1 as revised after DHH's #152 review) on the code sudoc generates
from ecbs.sudo, every tier. The receiver's board is driven only through the generated
start_calling() / call_step(); this driver reads the board between calls.
 (a) resume: let go before EVERY call of a two-band session and resume from the board alone
     (the cursor home and hole say where it stood; the copy so far is exact, the rest empty);
 (b) stale pegs: a receiving home holding old pegs. "Clear the homes named" (start_calling)
     gives an exact copy; laying the answers over the old pegs without clearing (computed
     here from the bands: a misfire lays nothing, so the old peg stays) would not;
 (c) coordinates (generated coordinate()): homes never share a hole, a call never names row J
     or a key grid (Demo: never rows I-J or lane 1), and the published bands' ranges.
Phase-1 results: ../history/card/calling_check.json, ../history/demo/soundness_demo.json "calling".

Usage: python calling_check.py [tiers]   (stdout -> results/calling_check.txt)
  With no argument, every tier, and writes results/calling_check.json. With a comma list (CI runs
  Demo,Toy) it prints only those tiers' lines, which equal the same lines of calling_check.txt
  (each tier draws from its own seeded generator), and writes no JSON.
"""
import json, os, random, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))   # proofs/: sudo_js
sys.dont_write_bytecode = True
from ecbs_oracle import TIERS
import sudo_js as SJ
ECBS = "primitives/key_exchange/ecbs/ecbs.sudo"

ACROSS, UP, BOTTOM, BASE_ACROSS, BASE_UP, GAP, SPARE = range(7)
SRC = {BASE_ACROSS: ACROSS, BASE_UP: UP, BOTTOM: ACROSS, GAP: UP}
HOMES = ["across", "up", "bottom", "base across", "base up", "gap", "spare"]
ROWS = "ABCDEFGHIJ"


def main():
    tiers = sys.argv[1].split(",") if len(sys.argv) > 1 else ["Demo", "Toy", "Hobby", "Serious"]
    sudo = SJ.Sudo(ECBS); out = {"provenance": SJ.provenance(ECBS)}
    for name in tiers:
        t0 = time.time()
        n = TIERS[name][0]; rnd = random.Random(5 + n); tier = SJ.tier(name)
        tr = sudo.call("tier", name)
        rand = lambda: [rnd.randrange(3) for _ in range(n)]
        def pair():
            snd = sudo.call("new_board", tier)
            snd = sudo.call("place", snd, ACROSS, rand()); snd = sudo.call("place", snd, UP, rand())
            rec = sudo.call("new_board", tier)
            rec = sudo.call("place", rec, ACROSS, rand()); rec = sudo.call("place", rec, UP, rand())
            return snd, rec
        # (a)
        snd, rec = pair(); rec = sudo.call("place", rec, BASE_UP, rand())
        rec = sudo.call("start_calling", rec); k = 0; ok_a = rec["cost"]["stale_cleared"] > 0
        while rec["row"][rec["calling_hole"]] == 1:
            dst, i = rec["cursor_home"], rec["cursor_hole"]; src = SRC[dst]
            if rec["held"][dst]:
                ok_a &= rec["home"][dst][:i] == snd["home"][src][:i] and not any(rec["home"][dst][i:])
            else:
                ok_a &= i == 0
            rec = sudo.call("call_step", rec, snd); k += 1
        ok_a &= k == 2 * n and sudo.call("band", rec, BASE_ACROSS) == snd["home"][ACROSS] \
            and sudo.call("band", rec, BASE_UP) == snd["home"][UP] and rec["cursor_home"] == -1
        # (b)
        trials = 200; wrong_noclear = wrong_rule = 0
        for _ in range(trials):
            snd, rec = pair(); stale = (rand(), rand())
            lay = lambda old, band: [b if b != 0 else o for o, b in zip(old, band)]
            wrong_noclear += lay(stale[0], snd["home"][ACROSS]) != snd["home"][ACROSS] or \
                lay(stale[1], snd["home"][UP]) != snd["home"][UP]
            rec = sudo.call("place", rec, BASE_ACROSS, stale[0]); rec = sudo.call("place", rec, BASE_UP, stale[1])
            rec = sudo.call("start_calling", rec)
            for _ in range(2 * n):
                rec = sudo.call("call_step", rec, snd)
            wrong_rule += sudo.call("band", rec, BASE_ACROSS) != snd["home"][ACROSS] or \
                sudo.call("band", rec, BASE_UP) != snd["home"][UP]
        # (c)
        cells = {}; allc = []; never_j = True; never_key = True; never_ij = True; never_lane1 = True
        for h in range(7):
            cs = [sudo.call("coordinate", tier, h, i) for i in range(n)]
            cs = [(c["grid"], c["row"], c["col"]) for c in cs]
            never_j &= all(c[1] != 9 for c in cs)
            never_ij &= all(c[1] < 8 for c in cs); never_lane1 &= all(c[2] > 2 for c in cs)
            never_key &= all(c[0] not in tr["geokey"] and c[0] <= tr["geowork"] for c in cs)
            allc += cs
            f, l = cs[0], cs[-1]
            cells[HOMES[h]] = f"grid {f[0]}, {ROWS[f[1]]}{f[2]} .. grid {l[0]}, {ROWS[l[1]]}{l[2]}"
        out[name] = dict(resume_every_hole=bool(ok_a), calls_in_session=k, stale_trials=trials,
                         stale_copy_wrong_without_clearing=wrong_noclear, stale_copy_wrong_with_rule=wrong_rule,
                         homes_disjoint=len(set(allc)) == len(allc), never_row_J=never_j, never_key_grid=never_key,
                         published_bands=dict(across=cells["across"], up=cells["up"]), all_homes=cells,
                         key_grids=tr["geokey"], workspace_grids=tr["geowork"])
        print(f"calling {name}: {time.time() - t0:.1f} s", file=sys.stderr, flush=True)
        if name == "Demo":                    # Demo: rows I-J are the control row, lane 1 the workbench
            out[name].update(never_control_rows_I_J=never_ij, never_lane_1=never_lane1)
        print(name, json.dumps(out[name]), flush=True)
    sudo.close()
    if len(sys.argv) > 1:
        return
    json.dump(out, open(os.path.join(HERE, "results", "calling_check.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
