"""Full-size peg multiplications for the real tiers (long toll): correctness vs Python and move counts.
Full exchanges at these sizes (ships+pegs keys): ../exchange/exchange.py."""
from pathlib import Path
HERE = Path(__file__).resolve().parent                        # every path below is built from this directory
import json, random, time, sys
import bspegs as P, bsref as R
PAR = json.load(open(HERE / "params.json"))
if len(sys.argv) > 1: PAR.update(json.load(open(HERE / sys.argv[1])))
rng = random.Random(7); out = {}
for tier in [t for t in ("T1", "T2", "T6demo", "R1024", "R2048", "R3072", "R7680") if t in PAR]:
    d = PAR[tier]; n = d['n']; p = int(d['p']); c = int(d['c'])
    toll = R.enc(c, n)
    while toll[-1] == '.': toll.pop()
    F = P.Field(n, toll)
    trials = 3 if n > 600 else 30
    ok = 0; mv = []; carries = []; lifts = []; t0 = time.time()
    for k in range(trials):
        a, b = rng.randrange(p), rng.randrange(p)
        nud = k % 3
        P.C.reset(); r = P.multiply(F, R.enc(a, n), R.enc(b, n), nud)
        mv.append(P.C.moves); carries.append(P.C.ops.get('carry', 0)); lifts.append(P.C.ops.get('fold_lift', 0))
        ok += (R.dec(r) - a*b*3**nud) % p == 0 and R.dec(P.tidy(F, r)) == a*b*3**nud % p
    m = sum(mv)/trials
    out[tier] = dict(n=n, toll_trits=len(toll), toll_pegs=sum(x != '.' for x in toll), trials=trials, correct=f"{ok}/{trials}",
                     moves_per_mul=round(m), moves_per_mul_over_n2=round(m/n**2, 3),
                     carry_share=round(sum(carries)/sum(mv), 3), fold_lifts_per_mul=round(sum(lifts)/trials),
                     python_seconds_per_mul=round((time.time()-t0)/trials, 2))
    print(tier, json.dumps(out[tier]), flush=True)
json.dump(out, open(HERE / ("bigmul_output.json" if len(sys.argv) == 1 else "bigmul_7680_output.json"), "w"), indent=1)
