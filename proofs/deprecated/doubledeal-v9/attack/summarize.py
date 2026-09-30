"""Summarize a scan: per (target, keys) the best test, Bonferroni over ALL tests in the file."""
import sys, json, math, collections
rows = json.load(open(sys.argv[1])); alpha = float(sys.argv[2]) if len(sys.argv) > 2 else 0.01
T = sum(len(r["tests"]) for r in rows); thr = alpha / T
print(f"{len(rows)} rows, {T} tests, Bonferroni threshold p < {thr:.2e}")
best = {}; nsig = collections.Counter(); exact = collections.Counter()
for r in rows:
    key = (r["target"], r["keys"]); exact[key] += r["exact_commute"]
    for tn, (p, eff, mean) in r["tests"].items():
        if p < thr: nsig[key] += 1
        if key not in best or p < best[key][0]: best[key] = (p, r["rel"], tn, eff, mean, r["n"])
for key in sorted(best):
    p, rel, tn, eff, mean, n = best[key]
    print(f"{key[0]:5s} {key[1]:5s} best p={p:.2e} [{rel} / {tn}] effect(sd)={eff:+.4f} mean={mean:.3f} n={n}  "
          f"significant tests={nsig[key]}  exact-commuting pairs={exact[key]}")
