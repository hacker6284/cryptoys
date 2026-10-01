"""BS peg recipes (bspegs) vs integer arithmetic (bsref / Python pow): arithmetic tests and
malicious received values.  Full exchanges with ships+pegs keys: ../exchange/exchange.py."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent                        # every path below is built from this directory
sys.path.insert(0, str(HERE.parent / "ships-pegs"))
import keygrid as KG
KEY = lambda rng: [KG.board_string(rng)]                    # one ships+pegs key grid (BS SPEC §4.2-§4.3)
import json, random, sys, time
import bspegs as P, bsref as R
PAR = json.load(open(HERE / "params.json"))
def field(tier):
    d = PAR[tier]; n = d['n']; c = int(d['c']); p = int(d['p'])
    return P.Field(n, trim(R.enc(c, n))), p, int(d["q"])
def trim(reg):
    while reg and reg[-1] == '.': reg = reg[:-1]
    return reg
def arith_tests(tier, trials, rng):
    F, p, q = field(tier); n = F.n; res = {}
    ok = 0
    for _ in range(trials):
        a, b = rng.randrange(3**n), rng.randrange(3**n)            # any register contents, incl. >= p
        r = P.multiply(F, R.enc(a, n), R.enc(b, n)); ok += (R.dec(r) - a*b) % p == 0 and R.dec(r) < 3**n
    res['mul'] = f"{ok}/{trials}"
    ok = 0
    for _ in range(trials):
        a, b, s = rng.randrange(3**n), rng.randrange(3**n), rng.choice([1, 2])
        r = P.multiply(F, R.enc(a, n), R.enc(b, n), s); ok += (R.dec(r) - a*b*3**s) % p == 0
    res['mul_nudge'] = f"{ok}/{trials}"
    top = R.enc(3**n - 1, n)                                       # all red: worst case for fold/carries
    r = P.multiply(F, top, top, 2); res['worst_case_all_red_x_all_red_nudge2'] = (R.dec(r) - (3**n-1)**2*9) % p == 0
    # tidy: every value in [p, 3^n) plus random ones
    edge = list(range(p, 3**n)) if 3**n - p < 2000 else [p, p+1, 3**n-1] + [rng.randrange(p, 3**n) for _ in range(200)]
    vals = edge + [rng.randrange(p) for _ in range(trials)] + [0, 1, p-1]
    res['tidy'] = f"{sum(R.dec(P.tidy(F, R.enc(v, n))) == v % p for v in vals)}/{len(vals)}"
    return res

def malicious(tier):
    F, p, q = field(tier); n = F.n; out = {}
    for name, v in [("0", 0), ("1", 1), ("p-1 (order 2)", p - 1), ("p+1 (non-canonical 1)", p + 1 if p + 1 < 3**n else None)]:
        if v is None: continue
        try: P.check_and_square(F, R.enc(v, n)); out[name] = "ACCEPTED (bad)"
        except ValueError: out[name] = "rejected"
    # a quadratic non-residue (order 2q) is accepted, but its square lands in the order-q subgroup
    nr = next(x for x in range(2, 100) if pow(x, q, p) == p - 1)
    S = P.check_and_square(F, R.enc(nr, n)); out[f"non-residue {nr}"] = f"accepted; square in order-q subgroup: {pow(R.dec(S), q, p) == 1}"
    # the attack the check stops (Lim-Lee / Wong 5.4): without squaring, B = p-1 gives K = (p-1)^a = +-1
    rng = random.Random(5); leaks = 0
    for _ in range(4):
        fa = KEY(rng); ea = R.exponent(fa)
        K = P.walk(F, fa, R.enc(p - 1, n))          # victim skips the check and walks on B = p-1
        leaks += (R.dec(K) == 1) == (ea % 2 == 0)
    out["unchecked B=p-1: K = +-1 reveals a mod 2 (4 trials)"] = f"{leaks}/4"
    return out

if __name__ == "__main__":
    rng = random.Random(2026)
    report = {}
    plan = [("T1", 300), ("T2", 300), ("T6demo", 100)]
    if sys.argv[1:]: plan = [x for x in plan if x[0] in sys.argv[1:]]
    for tier, trials in plan:
        t0 = time.time()
        rep = dict(arith=arith_tests(tier, trials, rng), malicious=malicious(tier))
        rep['seconds'] = round(time.time() - t0, 1)
        report[tier] = rep
        print(tier, json.dumps(rep['arith']), json.dumps(rep['malicious']), flush=True)
    json.dump(report, open(HERE / ("run_output.json" if not sys.argv[1:] else f"run_output_{'_'.join(sys.argv[1:])}.json"), "w"), indent=1)
