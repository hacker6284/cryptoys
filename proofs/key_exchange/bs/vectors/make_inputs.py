"""Write inputs.json: the inputs of the BS known-answer vectors (bs_vectors.json).

The outputs are not computed here: regen.sh runs the sudoc JS build of
primitives/key_exchange/bs/bs.sudo over these inputs. check_oracle.py then
cross-checks every output against pow() and the Python evidence harness
(not a reference; bs.sudo and the SPEC are normative).

Key grids are given as the dice faces that built them (BUILD, SPEC §4.2): one
stream per kind of die (d12 hole die, d6, d10). The faces are the ones
../exchange/exchange.py drew for its recorded exchanges (same seeds, same runs),
recorded by kind as ../ships-pegs/keygrid.py rolled them.

  python3 make_inputs.py          # rewrites inputs.json
"""
import json, os, random, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, "..", "ships-pegs")]
import keygrid as KG

SEED = {"T1": 11, "T2": 12, "T6demo": 13}     # ../exchange/exchange.py
TIER = {"T1": "T1", "T2": "T2", "T6demo": "T6"}  # exchange.py name -> bs.sudo tier()

# (exchange.py tier, run, why it is here)
EXCHANGES = [
    ("T1", 0, "the first recorded T1 exchange"),
    ("T1", 3, "Alice's public value ends in 6 misfires"),
    ("T2", 3, "Bob's public value ends in 8 misfires"),
    ("T6demo", 0, "the first recorded T6 demo exchange (n = 100, long toll)"),
]

DIE = {(1, 12): "d12", (1, 6): "d6", (0, 9): "d10"}


class Recorder:
    """Wraps exchange.py's random.Random and keeps each face, by kind of die."""
    def __init__(self, rng):
        self.rng = rng
        self.faces = {"d12": [], "d6": [], "d10": []}

    def randint(self, a, b):
        v = self.rng.randint(a, b)
        self.faces[DIE[(a, b)]].append(v)
        return v


def recorded_keys(tier, runs):
    """The dice of both parties' keys for the given runs of exchange.py's tier."""
    rng = random.Random(SEED[tier])
    out = {}
    for i in range(max(runs) + 1):
        pair = []
        for _ in range(2):                      # Alice, then Bob, as exchange.py builds them
            rec = Recorder(rng)
            KG.build(rec)
            pair.append(rec.faces)
        if i in runs:
            out[i] = pair
    return out


def compact(text):
    """Put each list of numbers on one line (as collect_vectors.mjs does to its JSON)."""
    one_line = lambda m: "[" + ", ".join(m.group(0)[1:-1].split()).replace(",,", ",") + "]"
    return re.sub(r"\[[-0-9,\s]*\]", one_line, text)


def reg(trits):
    return "".join(".WR"[t] for t in trits)


def main():
    vectors = []
    for tier in SEED:
        runs = [r for t, r, _ in EXCHANGES if t == tier]
        keys = recorded_keys(tier, runs)
        for t, r, why in EXCHANGES:
            if t != tier:
                continue
            a, b = keys[r]
            source = (f"proofs/key_exchange/bs/exchange/exchange.py {tier} seed {SEED[tier]}, "
                      f"run {r}: {why}")
            vectors.append(dict(name=f"exchange_{TIER[tier]}_run{r}", kind="exchange",
                                tier=TIER[tier], source=source, dice_a=a, dice_b=b))
    n1, n2 = 18, 35
    p1 = [2] * n1; p1[2] = 1                    # T1 p: all red except a white at hole k = 2
    pm1 = [2] * n1; pm1[0] = 1; pm1[2] = 1      # p - 1
    pp1 = [2] * n1; pp1[0] = 0; pp1[1] = 0; pp1[2] = 2   # p + 1 (a non-canonical 1)
    one = [1] + [0] * (n1 - 1)
    def vec(name, kind, tier, source, **inputs):
        return dict(name=name, kind=kind, tier=tier, **inputs, source=source)
    vectors += [
        vec("multiply_T1_all_red_nudge2", "multiply", "T1", "SPEC §8 worst case",
            a=reg([2] * n1), b=reg([2] * n1), nudge=2),
        vec("multiply_T2_all_red_nudge2", "multiply", "T2", "SPEC §8 worst case",
            a=reg([2] * n2), b=reg([2] * n2), nudge=2),
        vec("tidy_T1_p", "tidy", "T1", "SPEC B5: p tidies to the empty register", x=reg(p1)),
        vec("tidy_T1_p_plus_1", "tidy", "T1", "SPEC B5: p + 1 tidies to 1", x=reg(pp1)),
        vec("check_T1_zero", "check", "T1", "SPEC B8: reject 0", received=reg([0] * n1)),
        vec("check_T1_one", "check", "T1", "SPEC B8: reject 1", received=reg(one)),
        vec("check_T1_p_minus_1", "check", "T1", "SPEC B8: reject p - 1", received=reg(pm1)),
        vec("check_T1_p_plus_1", "check", "T1", "SPEC B8: reject p + 1", received=reg(pp1)),
        vec("check_T1_three", "check", "T1", "SPEC B8: accept g = 3, base 9",
            received=reg([0, 1] + [0] * (n1 - 2))),
        vec("call_T1_trailing_misfires", "call", "T1",
            "SPEC §3.1: every hole is called, even after a run of misfires",
            x=reg([2, 1, 0, 1, 2] + [0] * 13)),
        vec("call_T1_all_misfires", "call", "T1", "SPEC §3.1: an empty register is n misfires",
            x=reg([0] * n1)),
    ]
    doc = dict(note="Inputs of bs_vectors.json. Written by make_inputs.py; "
                    "regen.sh adds the outputs from bs.sudo.",
               registers="'.WR' strings, hole 0 first: '.' empty, 'W' white, 'R' red (SPEC §3)",
               dice="faces by kind of die, in the order they are thrown (SPEC §4.2): "
                    "d12 hole die, d6 (growth and Sub/Cruiser), d10 (the row cup: five dice "
                    "thrown at the start of each row, taken in rainbow order, one per hole "
                    "pair; a zero face is thrown again and comes just before that die's "
                    "final face)",
               vectors=vectors)
    with open(os.path.join(HERE, "inputs.json"), "w") as fh:
        fh.write(compact(json.dumps(doc, indent=1)) + "\n")
    print("wrote inputs.json:", len(vectors), "vectors")


if __name__ == "__main__":
    main()
