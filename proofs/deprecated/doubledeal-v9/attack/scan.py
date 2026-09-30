"""Discovery / confirmation scan of pair distinguishers.
usage: scan.py N_PAIRS SEED OUT.json [targets] [keysets]"""
import sys, json, time, numpy as np
from multiprocessing import Pool
import dd9, stats as S
from relations import relations

def job(args):
    target, keyset, n, seed = args
    rng = np.random.default_rng([seed, sum(map(ord, target)), 0 if keyset == "real" else 1])
    if target == "IDEAL": keyset = keyset
    keys = dd9.real_keys(dd9.rand_perms(rng, n)) if keyset == "real" else dd9.indep_keys(rng, n)
    m = dd9.rand_perms(rng, n)
    ideal = target == "IDEAL"          # null calibration: independent uniform decks
    C = dd9.rand_perms(rng, n) if ideal else dd9.enc(m, keys, target)
    ref = S.reference(); out = []
    for name, s in relations().items():
        m2 = s[m].astype(np.int32)              # sigma o m
        C2 = dd9.rand_perms(rng, n) if ideal else dd9.enc(m2, keys, target)
        D = S.delta(C, C2)
        exact = int((C2 == s[C]).all(1).sum())  # E(sm) == s E(m) exactly
        st = S.pair_stats(D, s)
        row = {"target": target, "keys": keyset, "rel": name, "n": n, "exact_commute": exact, "tests": {}}
        for k, x in st.items():
            if k == "R13": continue
            pm, pc, eff = S.test_scalar(x, ref[S.REF_OF[k]])
            row["tests"][k + ":mean"] = [pm, eff, float(x.mean())]
            row["tests"][k + ":dist"] = [pc, eff, float(x.mean())]
        pj, chi = S.joint_chi2(D)
        row["tests"]["joint"] = [pj, float(chi), 0.0]
        out.append(row)
    return out

if __name__ == "__main__":
    n, seed, outp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    targets = sys.argv[4].split(",") if len(sys.argv) > 4 else ["E1", "E2", "E3", "F1", "F2", "F3"]
    keysets = sys.argv[5].split(",") if len(sys.argv) > 5 else ["real", "indep"]
    S.reference()
    t = time.time()
    with Pool(8) as p:
        rows = [r for res in p.map(job, [(tg, ks, n, seed) for tg in targets for ks in keysets]) for r in res]
    json.dump(rows, open(outp, "w"))
    print(f"{len(rows)} (target,keys,relation) rows, {sum(len(r['tests']) for r in rows)} tests, {time.time()-t:.0f}s")
