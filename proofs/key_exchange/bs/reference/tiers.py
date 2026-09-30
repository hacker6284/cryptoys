"""BS tier table (BS SPEC §7) for the ships+pegs key: one key grid in every tier.
Inputs, all relative to this directory:
  params.json, params_323.json         verified primes (bsparams.py)
  bigmul_output.json                   measured moves per multiplication (bigmul.py)
  ../ships-pegs/combined_results.json  key entropy and multiplications per grid (20,000 built grids)
  ../exchange/exchange_output.json     full exchanges with ships+pegs keys: measured moves per multiplication
Moves per person = (mean multiplications per grid) x (moves per multiplication measured in the exchanges)."""
import json, math, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
P = json.load(open("params.json")); P["R512"] = json.load(open("params_323.json"))["n323"]
BM = json.load(open("bigmul_output.json"))
KEY = json.load(open(os.path.join("..", "ships-pegs", "combined_results.json")))
EX = json.load(open(os.path.join("..", "exchange", "exchange_output.json")))
H, HMIN = KEY["entropy"]["bump_H"], KEY["entropy"]["bump_Hmin"]
MULTS = KEY["walk"]["mults_per_grid"]
CELLS_MAX = KEY["walk"]["cells_max_possible"]
NIST = {1024: 80, 2048: 112, 3072: 128}                  # SP 800-57 Pt1 Table 2 [lit-mem]
def rawL(bits, c=(64/9)**(1/3)):
    lp = bits*math.log(2); return c*lp**(1/3)*math.log(lp)**(2/3)/math.log(2)
def nfs_bits(bits, special):
    """NIST where tabulated; otherwise raw L[1/3] shifted to agree with NIST at 1024 bits [est].
       Below ~128 bits the L-formula is meaningless (o(1) dominates): None = 'trivial'."""
    if bits < 128: return None, "trivial"
    if not special and bits in NIST: return NIST[bits], "NIST"
    c = (32/9)**(1/3) if special else (64/9)**(1/3)
    return round(rawL(bits, c) - rawL(1024) + 80, 1), "L-est"
ROWS = [("T1 skiff", "T1", 0), ("T2 frigate", "T2", 0), ("T6 demo", "T6demo", 50), ("R512", "R512", 162),
        ("R1024", "R1024", 323), ("R2048", "R2048", 646), ("R3072 (serious)", "R3072", 969)]   # toll holes (0 = kept in your head)
out = []
for name, key, t in ROWS:
    d = P[key]; n = d["n"]; q = int(d["q"]); bits = d["p_bits"]; qbits = bits - 1   # log2 q, rounded as in the SPEC
    ws = math.ceil((5*n + t + 10) / 100); grids = ws + 1
    nfs, src = nfs_bits(bits, t == 0)
    rho = qbits/2 - 0.17                                   # sqrt(pi q / 4)
    key_sqrt = min(HMIN, qbits)/2
    sec = min(x for x in (nfs, rho, key_sqrt) if x is not None)
    gmax = 0
    while 2 * 3**(CELLS_MAX*(gmax + 1)) < q: gmax += 1   # distinct keys -> distinct group elements
    ex = EX[key]
    mpm = ex["mean_moves_per_mult"]
    moves = MULTS * mpm; yrs = moves / 3.156e7
    bm = BM.get(key)
    out.append(dict(tier=name, grids=grids, workspace_grids=ws, game_sets=math.ceil(grids/4), n_trits=n, p_bits=bits,
                    toll_holes=t, nfs_bits=nfs, nfs_src=src + (" (SNFS: sparse p)" if t == 0 else ""),
                    rho_bits=round(rho, 1), key_sqrt_bits=round(key_sqrt, 1), key_sqrt_shannon_bits=round(min(H, qbits)/2, 1),
                    security_bits=round(sec, 1), injective_mod_q_max_grids=gmax,
                    mults_per_person=round(MULTS, 1), moves_per_mult_exchange=round(mpm), exchange_runs=ex["runs"],
                    moves_per_mult_bigmul=bm["moves_per_mul"] if bm else None,
                    moves_per_person=float(f"{moves:.4g}"), exchange_mean_moves_per_person=float(f"{ex['mean_moves_per_person']:.4g}"),
                    hours_nonstop=round(moves/3600, 1), years_nonstop=round(yrs, 3), years_8h_day=round(yrs*3, 3)))
for r in out: print(json.dumps(r))
json.dump(out, open("tiers_output.json", "w"), indent=1)
