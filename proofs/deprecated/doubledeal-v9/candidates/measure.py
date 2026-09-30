"""Measure candidate patches (candidates.py / cand.c) against:
  (1) the v9 swap distinguisher: per-layer survival of every transposition, the best pair,
      exact E_K(sM) = sE_K(M) rates at F2-F4 (real PassKey keys), extrapolation to F6;
  (2) the v8 same-rank distinguisher (K♣↔K♦);
  (3) the T1 symmetry group v9Sym (51 non-trivial elements).
usage: python3 measure.py [SCALE] [SEED]   (SCALE=1 is the committed run; log: measure.log)"""
import sys, json, time, pathlib, numpy as np
from multiprocessing import Pool
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent / "attack"))
import cport
from candidates import VARIANTS
from relations import v9sym, transposition
SCALE = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 11
NAMES = [r + s for s in "♣♥♠♦" for r in "A23456789TJQK"]
def nm(x, y): return f"{NAMES[x]}↔{NAMES[y]}"

def layers(a):
    var, sig, n, seed = a
    rng = np.random.default_rng(seed); ds = cport.rand_perms(rng, n)
    return cport.layer_counts(ds, np.asarray(sig, np.int32), var)

def exact(a):
    var, sig, target, n, seed = a
    rng = np.random.default_rng(seed); hits = 0; done = 0; sig = np.asarray(sig)
    while done < n:
        b = min(100_000, n - done)
        keys = cport.real_keys(cport.rand_perms(rng, b)); m = cport.rand_perms(rng, b)
        C = cport.enc(m, keys, target, var); C2 = cport.enc(sig[m].astype(np.int32), keys, target, var)
        hits += int((C2 == sig[C]).all(1).sum()); done += b
    return hits

def par_exact(pool, var, sig, target, n, seed):
    parts = pool.map(exact, [(var, sig, target, n // 8, seed * 100 + w) for w in range(8)])
    return sum(parts), (n // 8) * 8

def fmt(h, n): return f"{h}/{n:.1e}" + (f" = {h / n:.2e}" if h else f" (<{3 / n:.1e}, 95%)")

def main():
    t0 = time.time(); S = SCALE; out = {}
    pairs = [(x, y) for x in range(52) for y in range(x + 1, 52)]
    with Pool(8) as pool:
        for i, (name, var) in enumerate(VARIANTS.items()):
            print(("\n" if i else "") + f"=== {name} ===", flush=True)
            # (1a) round-level scan of all transpositions
            n1 = int(20000 * S)
            res = pool.map(layers, [(var, transposition(x, y), n1, SEED * 7919 + 52 * x + y) for x, y in pairs], chunksize=8)
            R = np.array(res, float) / n1          # P_S, P_G(fresh deck), P(round)
            order = np.argsort(-R[:, 2])
            nz = int((R[:, 0] > 0).sum())
            print(f"transpositions with SumRanks survival > 0: {nz}/1326; max P_S {R[:, 0].max():.4f}; "
                  f"max P(round) {R[:, 2].max():.2e}  [n={n1} decks each]")
            print("top 5 by per-round survival: " + ", ".join(
                f"{nm(*pairs[i])} {R[i, 2]:.2e} (P_S {R[i, 0]:.3f}, P_G {R[i, 1]:.3f})" for i in order[:5]))
            best = pairs[order[0]]
            cand = [(12, 24)] + ([best] if best != (12, 24) else [])
            for (x, y) in cand:
                n2 = int(400_000 * S)
                c = np.sum(pool.map(layers, [(var, transposition(x, y), n2 // 8, SEED * 31 + w + 1000 * x + y) for w in range(8)]), axis=0)
                pS, pG, pr = c / ((n2 // 8) * 8)
                f6 = pS ** 6 * (pr / pS) ** 5 if pS else 0.0
                print(f"{nm(x, y)}: P_S {pS:.4f}, P_G(fresh) {pG:.4f}, P(round) {pr:.2e} (1/{1 / pr if pr else float('inf'):.0f}); "
                      f"product-formula F6 ≈ P_S^6 (P_round/P_S)^5 = {f6:.1e}")
                row = {}
                # NB: the seed below depends on x + y only, so pairs with the same x + y share
                # decks/keys; a future rerun should use SEED + 1000 * r + 52 * x + y. The committed
                # measure.log was produced with this line as is (not rerun for the seed alone).
                for tgt, n3 in (("F2", int(1e6 * S)), ("F3", int(4e6 * S)), ("F4", int(1.6e7 * S))):
                    h, n = par_exact(pool, var, transposition(x, y), tgt, n3, SEED + 1000 * int(tgt[1]) + x + y)
                    row[tgt] = (h, n)
                print(f"   exact E(sM)=sE(M): " + "; ".join(f"{t} {fmt(*row[t])}" for t in row), flush=True)
                out[f"{name} {nm(x, y)}"] = {"P_S": pS, "P_G": pG, "P_round": pr, "F6_formula": f6,
                                              **{t: row[t] for t in row}}
            # (2) v8 same-rank distinguisher
            n2 = int(400_000 * S)
            c = np.sum(pool.map(layers, [(var, transposition(12, 51), n2 // 8, SEED * 37 + w) for w in range(8)]), axis=0) / ((n2 // 8) * 8)
            h, n = par_exact(pool, var, transposition(12, 51), "F2", int(1e6 * S), SEED + 5)
            print(f"v8 same-rank K♣↔K♦: P_S {c[0]:.4f}, P(round) {c[2]:.2e}, F2 exact {fmt(h, n)}")
            out[f"{name} v8 K♣↔K♦"] = {"P_S": c[0], "P_round": c[2], "F2": (h, n)}
            # (3) v9Sym
            n4 = int(20000 * S)
            G = [(a, b) for a in range(13) for b in range(4) if (a, b) != (0, 0)]
            rs = np.array(pool.map(layers, [(var, v9sym(a, b), n4, SEED * 13 + 4 * a + b) for a, b in G]), float) / n4
            h, n = par_exact(pool, var, v9sym(0, 1), "F2", int(1e6 * S), SEED + 6)
            print(f"v9Sym (51 elements): SumRanks commutes on {rs[:, 0].min():.3f}-{rs[:, 0].max():.3f} of decks; "
                  f"GridCycle commutes {int(rs[:, 1].sum() * n4)}/{n4 * 51}; round {int(rs[:, 2].sum() * n4)}/{n4 * 51}; "
                  f"v9Sym(0,1) F2 exact {fmt(h, n)}", flush=True)
            out[f"{name} v9Sym"] = {"sumranks_min": rs[:, 0].min(), "gridcycle": rs[:, 1].sum() * n4, "round": rs[:, 2].sum() * n4, "F2_01": (h, n)}
    json.dump(out, open(HERE / "measure.json", "w"), indent=1, default=float)
    print(f"\n({time.time() - t0:.0f}s)")

if __name__ == "__main__":
    main()
