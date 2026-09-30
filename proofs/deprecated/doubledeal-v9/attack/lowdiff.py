"""Low-difference pairs: m' = sigma o m, D = #positions where E(m), E(m') differ.
Ideal cipher: 52 - D = fixed points of a uniform permutation, P(D <= 26) < 1e-28,
so ANY observed pair with D <= 26 is decisive; 'exact' = (E(m') == sigma E(m)).
usage: lowdiff.py transpositions TARGET KEYS N_PER_PAIR SEED OUT.json
       lowdiff.py rel TARGET KEYS N SEED x,y[,x,y...]  (transpositions, one after another)
       lowdiff.py witness TARGET N SEED x,y OUT.json  (real keys; saves every exact pair)"""
import sys, json, time, numpy as np
from multiprocessing import Pool
import dd9
from relations import transposition
DMAX = 26

def count(target, keyset, sig, n, seed, witnesses=False):
    rng = np.random.default_rng(seed)
    done = 0; low = 0; exact = 0; hist = np.zeros(53, np.int64); wit = []
    while done < n:
        b = min(200_000, n - done)
        k0 = dd9.rand_perms(rng, b) if keyset == "real" else None
        keys = dd9.real_keys(k0) if keyset == "real" else dd9.indep_keys(rng, b)
        m = dd9.rand_perms(rng, b)
        C = dd9.enc(m, keys, target); C2 = dd9.enc(sig[m].astype(np.int32), keys, target)
        D = (C != C2).sum(1)
        hist += np.bincount(D, minlength=53)
        ex = (C2 == sig[C]).all(1)
        low += int((D <= DMAX).sum()); exact += int(ex.sum()); done += b
        if witnesses and keyset == "real":
            wit += [{"key": k0[i].tolist(), "message": m[i].tolist(), "cipher": C[i].tolist(),
                     "cipher2": C2[i].tolist()} for i in np.nonzero(ex)[0]]
    return (low, exact, hist, wit) if witnesses else (low, exact, hist)

def _tp(a):
    target, keyset, x, y, n, seed = a
    low, exact, _ = count(target, keyset, transposition(x, y), n, seed)
    return (x, y, low, exact)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "transpositions":
        target, keyset, n, seed, outp = sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        t = time.time()
        jobs = [(target, keyset, x, y, n, seed * 100000 + 52 * x + y) for x in range(52) for y in range(x + 1, 52)]
        with Pool(8) as p: res = p.map(_tp, jobs, chunksize=8)
        json.dump(res, open(outp, "w")); print(f"{len(res)} transpositions, {time.time()-t:.0f}s")
    elif mode == "witness":
        target, n, seed, (x, y), outp = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), map(int, sys.argv[5].split(",")), sys.argv[6]
        t = time.time()
        with Pool(8) as p:
            parts = p.starmap(count, [(target, "real", transposition(x, y), n // 8, seed * 1000 + w, True) for w in range(8)])
        wit = [w for q in parts for w in q[3]]
        out = {"target": target, "swap": [x, y], "n": (n // 8) * 8, "low(D<=26)": sum(q[0] for q in parts),
               "exact": sum(q[1] for q in parts), "secs": round(time.time() - t), "witnesses": wit}
        json.dump(out, open(outp, "w")); print(json.dumps({k: v for k, v in out.items() if k != "witnesses"}))
    else:
        target, keyset, n, seed = sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
        xs = list(map(int, sys.argv[6].split(",")))
        for x, y in zip(xs[::2], xs[1::2]):
            t = time.time()
            with Pool(8) as p:
                parts = p.starmap(count, [(target, keyset, transposition(x, y), n // 8, seed * 1000 + w) for w in range(8)])
            low = sum(q[0] for q in parts); exact = sum(q[1] for q in parts); hist = sum(q[2] for q in parts)
            N = (n // 8) * 8
            print(json.dumps({"target": target, "keys": keyset, "swap": [x, y], "n": N, "low(D<=26)": low,
                              "exact": exact, "minD": int(np.nonzero(hist)[0][0]), "secs": round(time.time() - t)}))
