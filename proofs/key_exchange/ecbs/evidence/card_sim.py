"""Full exchanges on the code sudoc generates from ecbs.sudo, checked against PARI/GP.

Each exchange is one call of the generated exchange(): both players on their own boards,
card play steps 9-14 (base point by rule, own walk, swap C by calls, curve test, make
certificate, rebuild theirs, swap A, compare, shared walk, fold). This driver only picks
keys and checks what the sudo returns against ../oracle/ecbs_oracle.py:
  base point = P; sent C = [a]P; sent A = [(lambda-1)a]P = pi(C) - C; each receiver's rebuilt
  A = the sender's A; curve test passed; shared points agree and equal [(lambda-1)ab]P; folded
  key = the SPEC 6 reference fold on both sides; every call names a hole of the sender's
  published band, in number order, 4 bands x n; coordinates of different homes never clash.
It also records the band peak, control-row use and moves per phase (phase and operation names
from the sudo's phase_names() / op_names()), and compares every run with the Phase-1 Python
simulation of the same keys (../history/card/card_sim_v3_*.json, ../history/demo/card_sim_demo.json; those
scripts were removed when ecbs.sudo replaced them). Calling no longer has a cursor (nobody lets
go, #175): Phase 1 counted each cursor step as one control-row move, so its ctrl less its
cursor_steps is compared. Phase 1 recorded the keys of each Demo
run but not of the Toy / Hobby / Serious runs: there the summary says so
(same_keys_as_phase1: "not recorded") and the match rests on the identical results.

Keys: Toy / Hobby / Serious draw them exactly as the Phase-1 simulation did
(random.Random(20261001 + len(name)); rnd.choice('.WR') per cell, redrawn
until both are non-empty; then the 4 calling sessions' rnd.sample(range(2n), 3) draws of
let-go points, from before nobody let go (#175); they change no result and are kept so the keys
stay the same), so run i here has the keys of run i there. Demo: all 8 x 8
pairs of non-empty 2-cell keys.

Usage: python card_sim.py Demo | Toy,Hobby,Serious [reps]
  writes results/card_sim_<tiers>.json; stdout -> results/card_sim_<tiers>.txt. Timings go to
  stderr only, so stdout and the JSON are byte-for-byte reproducible (CI diffs Demo).
"""
import itertools, json, os, random, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))   # proofs/: sudo_js
sys.dont_write_bytecode = True
from ecbs_oracle import Tier
import sudo_js as SJ
ECBS = "primitives/key_exchange/ecbs/ecbs.sudo"

PHASES, OPS = [], []                         # filled from the sudo (phase_names, op_names)
PEG = ".WR"
HIST = {"Demo": "../history/demo/card_sim_demo.json", "Toy": "../history/card/card_sim_v3_Toy.json",
        "Hobby": "../history/card/card_sim_v3_Hobby.json", "Serious": "../history/card/card_sim_v3_Serious.json"}
S_ = lambda t: "".join(PEG[d] for d in t)


def phase_dict(xs):
    return dict(zip(PHASES, xs))


def exchange(sudo, T, ca, cb):
    R = T.R; l = T.l; lam1 = (T.lam - 1) % l
    r = sudo.call("exchange", SJ.tier(T.name), ca, cb)
    a, b = r["a"], r["b"]
    for p in (a, b):
        p.update(p.pop("cost"))              # the board's Costs record, read like the other fields
    ka, kb = T.scalar(ca), T.scalar(cb)
    pt = T.point
    st = {"keys": [S_(ca), S_(cb)], "tier": T.name}
    st["P_ok"] = [pt(p["base"]) == T.Pref for p in (a, b)]
    st["base_hole"] = a["base_hole"]
    st["C_ok"] = [pt(a["sent_c"]) == R.mul(ka, T.Pref), pt(b["sent_c"]) == R.mul(kb, T.Pref)]
    st["on_curve"] = [a["on_curve"], b["on_curve"]]
    st["A_ok"] = [pt(a["sent_a"]) == R.mul(ka * lam1 % l, T.Pref), pt(b["sent_a"]) == R.mul(kb * lam1 % l, T.Pref),
                  pt(a["sent_a"]) == T.pi_minus_1(pt(a["sent_c"])) and pt(b["sent_a"]) == T.pi_minus_1(pt(b["sent_c"]))]
    st["match"] = [a["matched"] and a["rebuilt"] == b["sent_a"], b["matched"] and b["rebuilt"] == a["sent_a"]]
    K = R.mul(ka * kb * lam1 % l, T.Pref)
    st["agree"] = a["shared"] == b["shared"]
    st["shared_ok"] = pt(a["shared"]) == K
    ref = T.ref_fold(T.trits(K[0]))
    st["fold_ref_ok"] = [a["folded"] == ref, b["folded"] == ref]
    st["fold_agree"] = a["folded"] == b["folded"]
    st["peak_by_phase"] = {k: max(x, y) for k, x, y in zip(PHASES, a["peak_by_phase"], b["peak_by_phase"])
                           if k != "fold"}
    st["peak"] = [a["peak"], b["peak"]]; st["peak_strict"] = [a["peak_strict"], b["peak_strict"]]
    st["max_bench_hole"] = max(a["max_bench_hole"], b["max_bench_hole"])
    st["control"] = dict(ladder=S_(a["ladder"]), park_hole=a["park_hole"], tally_first=a["tally_first"],
                         tally_max=max(a["tally_max"], b["tally_max"]),
                         highest_hole_used=max(a["control_highest"], b["control_highest"]),
                         script_marker_max=max(a["script_marker_max"], b["script_marker_max"]),
                         phase_end=[PEG[a["phase_end"]], PEG[b["phase_end"]]], calling_hole=a["calling_hole"])
    st["moves"] = {"A": a["moves"], "B": b["moves"]}
    st["moves_by_phase"] = {"A": phase_dict(a["moves_by_phase"]), "B": phase_dict(b["moves_by_phase"])}
    st["ctrl"] = {"A": a["ctrl"], "B": b["ctrl"]}
    st["key_grid"] = {"A": a["key_grid_moves"], "B": b["key_grid_moves"]}
    st["calls"] = {"A": a["calls"], "B": b["calls"]}
    st["stale_cleared"] = {"A": a["stale_cleared"], "B": b["stale_cleared"]}
    st["ladder_build_once"] = a["ladder_moves"]
    st["ops"] = dict(zip(OPS, a["ops"]))
    # calls: number order, every hole, 4 bands; each names the sender's hole (coordinate of src, i)
    ok = True
    for p in (a, b):
        idx = [c["hole"] for c in p["log"]]
        ok &= idx == list(range(T.n)) * 4
        seen = set()
        for c in p["log"]:
            h = coords(sudo, T, c["src"], c["hole"])
            ok &= h == (c["grid"], c["row"], c["col"]) and h[1] != 9 and (h, c["dst"]) not in seen
            seen.add((h, c["dst"]))
    st["calls_ok"] = ok
    st["call_example"] = [f"grid {c['grid']}, {'ABCDEFGHIJ'[c['row']]}{c['col']}" for c in a["log"][:2]]
    return st


_coords = {}
def coords(sudo, T, home, i):
    key = (T.name, home, i)
    if key not in _coords:
        h = sudo.call("coordinate", SJ.tier(T.name), home, i)
        _coords[key] = (h["grid"], h["row"], h["col"])
    return _coords[key]


def homes_disjoint(sudo, T):
    allc = [coords(sudo, T, h, i) for h in range(7) for i in range(T.n)]
    return len(set(allc)) == len(allc)


CHECKS = ["P_ok", "C_ok", "on_curve", "A_ok", "match", "fold_ref_ok"]
SAME = ["moves", "moves_by_phase", "ctrl", "key_grid", "calls", "stale_cleared", "peak",
        "peak_strict", "max_bench_hole", "ladder_build_once", "base_hole", "peak_by_phase"]


def compare(st, old):
    """differences from the Phase-1 Python run of the same keys (empty = identical)."""
    diff = {}
    if "cursor_steps" in old:                # Phase 1's calling cursor (gone, #175), 1 ctrl per step
        old = dict(old, ctrl={w: old["ctrl"][w] - old["cursor_steps"][w] for w in "AB"})
    for k in SAME:
        if k in old and old[k] != st[k]: diff[k] = {"python": old[k], "sudo": st[k]}
    oc = old.get("control", {})
    for k, v in st["control"].items():
        if k in oc and oc[k] != v: diff[f"control.{k}"] = {"python": oc[k], "sudo": v}
    if "ops" in old and old["ops"] != st["ops"]: diff["ops"] = {"python": old["ops"], "sudo": st["ops"]}
    return diff


def all_ok(st):
    return all(all(st[k]) for k in CHECKS) and st["agree"] and st["shared_ok"] and st["fold_agree"] and st["calls_ok"]


def summary(T, runs, old_runs):
    people = [(r, w) for r in runs for w in "AB"]
    mv = [r["moves"][w] for r, w in people]
    by = {k: round(sum(r["moves_by_phase"][w].get(k, 0) for r, w in people) / len(people)) for k in runs[0]["moves_by_phase"]["A"]}
    chk = ["curve test", "make certificate", "rebuild theirs"]
    s = dict(exchanges=len(runs), people=len(people), all_checks_pass=sum(all_ok(r) for r in runs),
             base_point_is_P=sum(sum(r["P_ok"]) for r in runs), shared_is_lam1abP=sum(r["shared_ok"] for r in runs),
             band_peak=max(max(r["peak"]) for r in runs),
             peak_by_phase={k: max(r["peak_by_phase"][k] for r in runs) for k in runs[0]["peak_by_phase"]},
             highest_bench_hole=max(r["max_bench_hole"] for r in runs),
             moves_per_person_mean=round(sum(mv) / len(mv)), moves_min=min(mv), moves_max=max(mv),
             moves_by_phase_mean=by,
             check_moves_mean=round(sum(sum(r["moves_by_phase"][w][k] for k in chk) for r, w in people) / len(people)),
             control_moves_mean=round(sum(r["ctrl"][w] for r, w in people) / len(people)),
             ladder_build_once=runs[0]["ladder_build_once"],
             calls_per_receiver=sorted({r["calls"][w] for r, w in people}),
             tally_max=max(r["control"]["tally_max"] for r in runs),
             control_highest_hole=max(r["control"]["highest_hole_used"] for r in runs),
             script_marker_max=max(r["control"]["script_marker_max"] for r in runs))
    if old_runs is not None:
        diffs = [compare(r, o) for r, o in zip(runs, old_runs)]
        recorded = [(r, o) for r, o in zip(runs, old_runs) if "keys" in o]
        s["same_keys_as_phase1"] = (all(r["keys"] == o["keys"] for r, o in recorded)
                                    if len(recorded) == len(runs) else "not recorded")
        s["identical_to_phase1_python"] = f"{sum(not d for d in diffs)}/{len(runs)}"
        s["differences"] = [d for d in diffs if d]
    return s


def keys_like_phase1(rnd, M, n):
    while True:
        ca = [PEG.index(rnd.choice(PEG)) for _ in range(M)]
        cb = [PEG.index(rnd.choice(PEG)) for _ in range(M)]
        if any(ca) and any(cb): break
    for _ in range(4):                       # Phase 1's let-go draws (pre-#175), kept for the keys
        rnd.sample(range(2 * n), min(3, 2 * n))
    return ca, cb


def main():
    tiers = sys.argv[1].split(",")
    reps = int(sys.argv[2]) if len(sys.argv) > 2 else None
    sudo = SJ.Sudo(ECBS); res = {"provenance": SJ.provenance(ECBS)}
    PHASES[:] = sudo.call("phase_names"); OPS[:] = sudo.call("op_names")
    for name in tiers:
        T = Tier(name); t0 = time.time(); runs = []
        print(name, "n", T.n, "k", T.k, flush=True)
        if name == "Demo":
            keys = [list(k) for k in itertools.product(range(3), repeat=T.cells) if any(k)]
            pairs = list(itertools.product(keys, keys))
            old = json.load(open(os.path.join(HERE, HIST["Demo"])))["runs"]
        else:
            rnd = random.Random(20261001 + len(name))
            pairs = [keys_like_phase1(rnd, T.cells, T.n) for _ in range(reps or {"Toy": 10, "Hobby": 6, "Serious": 4}[name])]
            old = json.load(open(os.path.join(HERE, HIST[name])))[name]
        for i, (ca, cb) in enumerate(pairs):
            t1 = time.time(); st = exchange(sudo, T, ca, cb)
            print(f"  {name} run {i}: {time.time() - t1:.1f} s", file=sys.stderr, flush=True)
            if name != "Demo" or i < 3 or not all_ok(st):
                print(" ", json.dumps({k: v for k, v in st.items() if k != "moves_by_phase"}), flush=True)
                print("   by phase", json.dumps(st["moves_by_phase"]), flush=True)
            runs.append(st)
        old = old[:len(runs)] if len(old) >= len(runs) else None
        s = summary(T, runs, old)
        s["homes_disjoint"] = homes_disjoint(sudo, T)
        if name == "Demo":
            # Demo's 16-hole control row fits its 5-hole script; the 15-hole overrun is the
            # sudo test "§1 Demo's 16-hole control row overruns with a 15-hole script".
            try:
                sudo.call("new_board", SJ.tier("Demo")); s["fits_with_5_hole_script"] = True
            except SJ.SudoError:
                s["fits_with_5_hole_script"] = False
        print(f"{name}: {time.time() - t0:.1f} s", file=sys.stderr, flush=True)
        print(name, "summary", json.dumps(s, indent=1), flush=True)
        res[name] = {"summary": s, "runs": runs}
    sudo.close()
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    json.dump(res, open(os.path.join(HERE, "results", f"card_sim_{'_'.join(tiers)}.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
