"""Soundness of the certificate check at Demo (n = 7), EXHAUSTIVE, on the code sudoc generates
from ecbs.sudo, checked against PARI/GP.

 EXHAUSTIVE: demo_exhaustive.mjs runs the generated curve_test() and make_certificate() on every
   pair (x, y) in GF(3^7)^2 (4,782,969 pairs). The curve test is compared with the curve equation
   (../oracle/gf37.py, tables built from PARI and self-tested against it); for every on-curve C the
   certificate is compared with PARI's pi(C) - C, every accepted A is checked to lie in <P> minus
   O, and the multiplicity of each subgroup point is counted. Wrong A's for every on-curve C (the
   comparison step). Off the curve: how many pairs the curve test rejects and how many a
   self-consistent A (the certificate's own output) would get past the comparison alone.
   The generated invert_number() on every nonzero element.
 BOARD: the generated receive_check() (receiver board holding its own A while it rebuilds theirs;
   C and A called in from a sender board) on every on-curve C with its honest A, and sampled
   classes (C outside <P> with A = C and with the correct certificate, the 4 order-5 points, A
   not matching, C off the curve).
Phase-1 results: ../history/demo/soundness_demo.json (the script was removed when ecbs.sudo replaced
it). Calling at Demo: calling_check.py.

Usage: python soundness_demo.py [shards]   (writes results/soundness_demo.json; stdout -> .txt)
  Runs demo_exhaustive.mjs in `shards` parallel node processes (default 4) unless
  ECBS_DEMO_EXHAUSTIVE=<prefix> points at a finished run; that run's <prefix>.provenance.json
  must name the same ecbs.sudo hash and sudocode commit as this build. Timings go to stderr.
"""
import atexit, json, os, random, shutil, subprocess, sys, tempfile, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracle"))
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))   # proofs/: sudo_js
sys.dont_write_bytecode = True
import gf37 as F
from ecbs_oracle import Tier
import sudo_js as SJ
ECBS = "primitives/key_exchange/ecbs/ecbs.sudo"

T = Tier("Demo"); R = T.R; l = T.l; Q = F.Q
VERDICT = {"Accept": "accept", "CurveFails": "curve", "EmptyCertificate": "empty", "Mismatch": "mismatch"}


def exhaustive(shards):
    prefix = os.environ.get("ECBS_DEMO_EXHAUSTIVE")
    prov = SJ.provenance(ECBS)
    stamp = {k: prov[k] for k in ("sudo_sha256", "sudocode_commit")}
    if not prefix:
        out, _, _ = SJ.build(ECBS); d = tempfile.mkdtemp(prefix="ecbs-exh-"); prefix = os.path.join(d, "demo")
        atexit.register(shutil.rmtree, d, True)
        t0 = time.time()
        ps = [subprocess.Popen(["node", os.path.join(HERE, "demo_exhaustive.mjs"), out, prefix, str(s), str(shards)])
              for s in range(shards)]
        assert all(p.wait() == 0 for p in ps)
        json.dump(stamp, open(f"{prefix}.provenance.json", "w"))
        print(f"demo_exhaustive ({shards} node processes): {time.time() - t0:.1f} s", file=sys.stderr, flush=True)
    else:
        got = json.load(open(f"{prefix}.provenance.json"))
        assert got == stamp, f"exhaustive run at {prefix} was made from {got}, not {stamp}"
    curve = np.zeros(Q * Q, dtype=np.uint8); cx = np.full(Q * Q, -2, dtype=np.int64); cy = cx.copy()
    s = 0
    while os.path.exists(f"{prefix}.{s}.xs.json"):
        xs = json.load(open(f"{prefix}.{s}.xs.json"))
        c = np.fromfile(f"{prefix}.{s}.curve", dtype=np.uint8).reshape(len(xs), Q)
        a = np.fromfile(f"{prefix}.{s}.cx", dtype=np.int16).reshape(len(xs), Q)
        b = np.fromfile(f"{prefix}.{s}.cy", dtype=np.int16).reshape(len(xs), Q)
        for j, x in enumerate(xs):
            curve[x * Q:(x + 1) * Q] = c[j]; cx[x * Q:(x + 1) * Q] = a[j]; cy[x * Q:(x + 1) * Q] = b[j]
        s += 1
    assert (cx != -2).all(), "exhaustive run incomplete"
    return curve.astype(bool), cx, cy


def field(curve, cx, cy, sudo):
    out = {"selftest_oracle_tables_vs_PARI": F.selftest()}
    xs, ys = np.meshgrid(np.arange(Q), np.arange(Q), indexing="ij"); xs = xs.ravel(); ys = ys.ravel()
    b = F.add(F.sub(F.mul(ys, ys), F.cube(xs)), F.mul(xs, xs))         # b' = y^2 - x^3 + x^2
    oncurve = b == F.ONE
    xin3 = F.cube(xs) == xs
    has = cx >= 0
    out["pairs"] = int(len(xs))
    out["curve_test_agrees_with_curve_equation"] = int((curve == oncurve).sum())
    out["on_curve_affine"] = int(curve.sum())
    out["certificate_none_exactly_when_x_in_GF3"] = int(((~has) == xin3).sum())
    out["empty_run_on_curve"] = int((curve & ~has).sum())
    idx = np.nonzero(curve & has)[0]
    pari_ok = 0; in_sub = 0; mult = {}
    for i in idx:
        C = R.pt(([".WR"[d] for d in F.DIG[xs[i]]], [".WR"[d] for d in F.DIG[ys[i]]]))
        Ap = T.pi_minus_1(C); A = (int(cx[i]), int(cy[i]))
        pari_ok += len(Ap) == 2 and (F.to_int(Ap[0]), F.to_int(Ap[1])) == A
        in_sub += len(Ap) == 2 and len(R.mul(l, Ap)) == 1
        mult[A] = mult.get(A, 0) + 1
    out["honest"] = dict(accept=int(len(idx)), empty=out["empty_run_on_curve"], A_equals_PARI_piC_minus_C=pari_ok,
                         accepted_A_in_subgroup_minus_O=in_sub, distinct_accepted_A=len(mult),
                         multiplicity_of_each=sorted(set(mult.values())))
    o5 = np.nonzero(curve & ~has)[0]
    out["order5_points"] = [["".join(".WR"[d] for d in F.DIG[xs[i]]), "".join(".WR"[d] for d in F.DIG[ys[i]])] for i in o5]
    # wrong A for every non-empty on-curve C: -A, A = C, one peg changed, another subgroup point
    rng = np.random.default_rng(11); mism = 0; trials = 0; subs = list(mult.keys())
    for i in idx:
        A = (int(cx[i]), int(cy[i]))
        cands = [(A[0], int(F.neg(np.array([A[1]]))[0])), (int(xs[i]), int(ys[i]))]
        d = F.DIG[A[0]].copy(); h = rng.integers(7); d[h] = (d[h] + rng.integers(1, 3)) % 3
        cands.append((int(d @ F.P3), A[1]))
        while True:
            o = subs[rng.integers(len(subs))]
            if o != A: break
        cands.append(o)
        for c in cands:
            trials += 1; mism += c != A
    out["A_not_matching"] = dict(trials=trials, mismatch=mism)
    off = ~curve
    out["off_curve"] = dict(pairs=int(off.sum()), rejected_by_curve_test=int(off.sum()),
                            would_pass_without_curve_test=int((off & has).sum()),
                            run_empty_without_curve_test=int((off & ~has).sum()))
    b0 = sudo.call("new_board", SJ.tier("Demo"))
    out["ladder"] = "".join(".WR"[b0["row"][b0["ladder0"] + i]] for i in range(b0["nrungs"]))
    bad = 0
    for a in range(1, Q):
        inv = sudo.call("invert_number", SJ.tier("Demo"), [int(t) for t in F.DIG[a]])
        bad += int(np.array(inv) @ F.P3) != int(F.inv(np.array([a]))[0])
    out["inversion_wrong_of_2186"] = bad
    return out, (xs, ys, curve, has, cx, cy)


def board(data, sudo, rnd):
    xs, ys, curve, has, cx, cy = data
    trits = lambda a: [int(t) for t in F.DIG[a]]
    pt = lambda i: {"x": trits(xs[i]), "y": trits(ys[i])}
    cert = lambda i: {"x": trits(cx[i]), "y": trits(cy[i])} if has[i] else {"x": [0] * 7, "y": [0] * 7}
    out = {}
    def run(label, items):
        res = {"trials": 0, "accept": 0, "curve": 0, "empty": 0, "mismatch": 0, "peak": 0, "max_check_moves": 0,
               "highest_control_hole": 0, "accepted_A_is_PARI_piC_minus_C": 0}
        for C, A in items:
            own = T.unpoint(T.pi_minus_1(R.mul(rnd.randrange(1, l), T.Pref)))
            r = sudo.call("receive_check", SJ.tier("Demo"), own, C, A)
            v = VERDICT[r["verdict"]["$"]]; res["trials"] += 1; res[v] += 1
            res["peak"] = max(res["peak"], r["peak"]); res["max_check_moves"] = max(res["max_check_moves"], r["check_moves"])
            res["highest_control_hole"] = max(res["highest_control_hole"], r["control_highest"])
            if v == "accept":
                res["accepted_A_is_PARI_piC_minus_C"] += T.point(r["rebuilt"]) == T.pi_minus_1(T.point(C))
        out[label] = res
        print(label, json.dumps(res), flush=True)
    on = np.nonzero(curve)[0]
    run("every on-curve C, honest A", [(pt(i), cert(i)) for i in on])
    sub = lambda i: len(R.mul(l, T.point(pt(i)))) == 1
    outs = [int(i) for i in on if has[i] and not sub(i)]
    pick = rnd.sample(outs, 200)
    run("C outside <P>, A = C", [(pt(i), pt(i)) for i in pick])
    run("C outside <P>, correct certificate", [(pt(i), cert(i)) for i in pick])
    o5 = [int(i) for i in on if not has[i]]
    hon = lambda: T.unpoint(R.mul(rnd.randrange(1, l), T.Pref))
    run("C = nonzero order-5 point", [(pt(i), A) for i in o5 for A in ({"x": [0] * 7, "y": [0] * 7}, hon())])
    mm = []; nonempty = [int(i) for i in on if has[i]]
    for k in range(300):
        i = rnd.choice(nonempty); Ac = cert(i)
        if k % 3 == 0: A = {"x": Ac["x"], "y": [(3 - t) % 3 for t in Ac["y"]]}
        elif k % 3 == 1:
            A = {"x": list(Ac["x"]), "y": Ac["y"]}; h = rnd.randrange(7)
            A["x"][h] = rnd.choice([c for c in range(3) if c != A["x"][h]])
        else:
            while True:
                A = hon()
                if A != Ac: break
        mm.append((pt(i), A))
    run("A not matching pi(C) - C", mm)
    offs = np.nonzero(~curve & has)[0]
    pick = [int(offs[j]) for j in np.random.default_rng(5).choice(len(offs), 300, replace=False)]
    run("C off the curve, A = the card formulas on C", [(pt(i), cert(i)) for i in pick])
    return out


def main():
    shards = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    t0 = time.time(); rnd = random.Random(20261003)
    sudo = SJ.Sudo(ECBS)
    curve, cx, cy = exhaustive(shards)
    f, data = field(curve, cx, cy, sudo)
    print("EXHAUSTIVE", json.dumps(f, indent=1), flush=True)
    p = board(data, sudo, rnd)
    sudo.close()
    json.dump(dict(provenance=SJ.provenance(ECBS), exhaustive=f, board=p),
              open(os.path.join(HERE, "results", "soundness_demo.json"), "w"), indent=1)
    print(f"soundness_demo: {time.time() - t0:.1f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
