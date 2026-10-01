import sys, json, multiprocessing as mp
from build_dp import analyse
from rules import make_rules, extra_rules, variant_rules
from pathlib import Path
HERE = Path(__file__).resolve().parent            # every file path is anchored on this script's directory
def job(k):
    allr = make_rules(); allr.update(extra_rules()); allr.update(variant_rules()); R = allr[k]
    if R.dattempt: R.dice_cost = (lambda opts, Z, d=R.dattempt: d / Z)
    res = analyse(R, 10, 10)
    res = {a: float(b) if not isinstance(b, str) else b for a, b in res.items()}
    res["key"] = k
    print(json.dumps(res), flush=True)
    return res
if __name__ == "__main__":
    keys = sys.argv[1:]
    with mp.Pool(3) as p:
        out = p.map(job, keys)
    json.dump(out, open(HERE / ("rules_" + "_".join(keys) + ".json"), "w"), indent=1)
