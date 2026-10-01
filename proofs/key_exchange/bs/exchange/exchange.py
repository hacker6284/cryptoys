"""Full BS exchanges with ships+pegs keys through the peg recipes (BS SPEC §3, §4, §7).

Both parties build a key grid with the SPEC dice (../ships-pegs/keygrid.py), read it as
"ships, then pegs" behind one start marker, and run the exchange B9 with the unchanged peg
recipes (../reference/bspegs.py): public walk, received-value check and square, shared walk.
Every result is compared with Python's pow: A = 3^a, B = 3^b, K_A = K_B = 3^(2ab) mod p.
Moves are counted by bspegs (one peg placed, lifted or swapped = one move); moves per person =
all walks and checks of both parties / 2, as in the reference exchange tooling.

  python3 exchange.py T1 T2 ...     run tiers, write exchange_<tier>.json
  python3 exchange.py summary       merge them into exchange_output.json / print the table
"""
import json, random, sys, time
from pathlib import Path
HERE = Path(__file__).resolve().parent             # outputs are written beside this script
sys.path[:0] = [str(HERE.parent / "reference"), str(HERE.parent / "ships-pegs")]
import bspegs as P, bsref as R, keygrid as KG

PAR = json.load(open(HERE.parent / "reference" / "params.json"))
PAR["R512"] = json.load(open(HERE.parent / "reference" / "params_323.json"))["n323"]
PLAN = {"T1": 20, "T2": 5, "T6demo": 2, "R512": 1, "R1024": 1, "R2048": 1, "R3072": 1}
SEED = {"T1": 11, "T2": 12, "T6demo": 13, "R512": 14, "R1024": 15, "R2048": 16, "R3072": 17}


def field(tier):
    d = PAR[tier]; n = d["n"]; toll = R.enc(int(d["c"]), n)
    while toll[-1] == ".": toll.pop()
    return P.Field(n, toll), int(d["p"]), int(d["q"])


def one_exchange(tier, rng):
    F, p, q = field(tier)
    keys = []
    for _ in range(2):
        ships, pegs = KG.build(rng)
        cells = KG.key_cells([(ships, pegs)])
        board = ["".join(".WR"[t] for t in cells)]
        e = R.exponent(board); assert e == KG.exponent(cells)
        keys.append(dict(board=board, e=e, cells=len(cells) - 1, hit_units=sum(cells) - 1, ships=len(ships)))
    a, b = keys
    ph = {}
    def run(name, f, *args):
        P.C.reset(); t0 = time.time(); r = f(*args)
        ph[name] = dict(moves=P.C.moves, seconds=round(time.time() - t0, 1), **P.C.ops); return r
    A = run("A = walk(a, g=3)", P.walk, F, a["board"])
    B = run("B = walk(b, g=3)", P.walk, F, b["board"])
    CB = run("Alice checks+squares B", P.check_and_square, F, B)
    CA = run("Bob checks+squares A", P.check_and_square, F, A)
    KA = run("K_A = walk(a, base B^2)", P.walk, F, a["board"], CB)
    KB = run("K_B = walk(b, base A^2)", P.walk, F, b["board"], CA)
    ea, eb = a["e"], b["e"]
    mults = sum(v.get("mul", 0) for v in ph.values())
    moves = sum(v["moves"] for v in ph.values())
    return dict(tier=tier, n=F.n,
                key_cells=[a["cells"], b["cells"]], key_hit_units=[a["hit_units"], b["hit_units"]],
                key_ships=[a["ships"], b["ships"]],
                pub_A_ok=R.dec(A) == pow(3, ea, p), pub_B_ok=R.dec(B) == pow(3, eb, p),
                A_in_subgroup=pow(R.dec(A), q, p) == 1,
                agree=KA == KB,
                K_matches_pow=R.dec(KA) == pow(3, 2 * ea * eb % q, p) == pow(pow(R.dec(B), 2, p), ea, p),
                K_canonical=R.dec(KA) < p,
                mults_per_person=mults / 2, moves_per_person=moves / 2,
                moves_per_mult=moves / mults, phases=ph)


def run_tier(tier):
    rng = random.Random(SEED[tier]); t0 = time.time(); ex = []
    for i in range(PLAN[tier]):
        ex.append(one_exchange(tier, rng))
        e = ex[-1]
        print(tier, i, {k: e[k] for k in ("key_cells", "pub_A_ok", "pub_B_ok", "agree", "K_matches_pow",
                                            "K_canonical", "mults_per_person", "moves_per_person")}, flush=True)
    s = dict(tier=tier, runs=len(ex),
             all_ok=all(e["pub_A_ok"] and e["pub_B_ok"] and e["A_in_subgroup"] and e["agree"]
                        and e["K_matches_pow"] and e["K_canonical"] for e in ex),
             mean_mults_per_person=sum(e["mults_per_person"] for e in ex) / len(ex),
             mean_moves_per_person=sum(e["moves_per_person"] for e in ex) / len(ex),
             mean_moves_per_mult=sum(e["moves_per_person"] for e in ex) / sum(e["mults_per_person"] for e in ex),
             mean_key_cells=sum(sum(e["key_cells"]) for e in ex) / (2 * len(ex)),
             seconds=round(time.time() - t0, 1))
    print(tier, "SUMMARY", json.dumps(s), flush=True)
    json.dump(dict(summary=s, exchanges=ex), open(HERE / f"exchange_{tier}.json", "w"), indent=1)


def summary():
    out = {}
    for tier in PLAN:
        fn = HERE / f"exchange_{tier}.json"
        if fn.exists(): out[tier] = json.load(open(fn))["summary"]
    for tier, s in out.items():
        print(f"{tier:7s} runs {s['runs']:2d}  all correct {s['all_ok']}  mults/person {s['mean_mults_per_person']:8.1f}"
              f"  moves/person {s['mean_moves_per_person']:.4g}  moves/mult {s['mean_moves_per_mult']:.4g}"
              f"  key cells {s['mean_key_cells']:.1f}")
    json.dump(out, open(HERE / "exchange_output.json", "w"), indent=1)


if __name__ == "__main__":
    if sys.argv[1:] == ["summary"]: summary()
    else:
        for t in sys.argv[1:] or list(PLAN): run_tier(t)
