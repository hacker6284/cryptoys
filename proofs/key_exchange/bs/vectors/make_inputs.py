"""Write inputs.json: the inputs of the BS known-answer vectors (bs_vectors.json).

The outputs are not computed here: regen.sh runs the sudoc JS build of
primitives/key_exchange/bs/bs.sudo over these inputs. check_oracle.py then
cross-checks every output against the Python reference and pow().

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
    """Put each list of numbers on one line (as JSON.stringify output is post-processed in collect_vectors.mjs)."""
    return re.sub(r"\[[-0-9,\s]*\]", lambda m: "[" + ", ".join(m.group(0)[1:-1].split()).replace(",,", ",") + "]", text)


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
            vectors.append(dict(name=f"exchange_{TIER[tier]}_run{r}", kind="exchange", tier=TIER[tier],
                                source=f"proofs/key_exchange/bs/exchange/exchange.py {tier} seed {SEED[tier]}, run {r}: {why}",
                                dice_a=a, dice_b=b))
    n1, n2 = 18, 35
    p1 = [2] * n1; p1[2] = 1                    # T1 p: all red except a white at hole k = 2
    pm1 = [2] * n1; pm1[0] = 1; pm1[2] = 1      # p - 1
    pp1 = [2] * n1; pp1[0] = 0; pp1[1] = 0; pp1[2] = 2   # p + 1 (a non-canonical 1)
    one = [1] + [0] * (n1 - 1)
    vectors += [
        dict(name="multiply_T1_all_red_nudge2", kind="multiply", tier="T1", a=reg([2] * n1), b=reg([2] * n1), nudge=2,
             source="SPEC §8 worst case"),
        dict(name="multiply_T2_all_red_nudge2", kind="multiply", tier="T2", a=reg([2] * n2), b=reg([2] * n2), nudge=2,
             source="SPEC §8 worst case"),
        dict(name="tidy_T1_p", kind="tidy", tier="T1", x=reg(p1), source="SPEC B5: p tidies to the empty register"),
        dict(name="tidy_T1_p_plus_1", kind="tidy", tier="T1", x=reg(pp1), source="SPEC B5: p + 1 tidies to 1"),
        dict(name="check_T1_zero", kind="check", tier="T1", received=reg([0] * n1), source="SPEC B8: reject 0"),
        dict(name="check_T1_one", kind="check", tier="T1", received=reg(one), source="SPEC B8: reject 1"),
        dict(name="check_T1_p_minus_1", kind="check", tier="T1", received=reg(pm1), source="SPEC B8: reject p - 1"),
        dict(name="check_T1_p_plus_1", kind="check", tier="T1", received=reg(pp1), source="SPEC B8: reject p + 1"),
        dict(name="check_T1_three", kind="check", tier="T1", received=reg([0, 1] + [0] * (n1 - 2)),
             source="SPEC B8: accept g = 3, base 9"),
        dict(name="call_T1_trailing_misfires", kind="call", tier="T1", x=reg([2, 1, 0, 1, 2] + [0] * 13),
             source="SPEC §3.1: every hole is called, even after a run of misfires"),
        dict(name="call_T1_all_misfires", kind="call", tier="T1", x=reg([0] * n1),
             source="SPEC §3.1: an empty register is n misfires"),
    ]
    doc = dict(note="Inputs of bs_vectors.json. Written by make_inputs.py; regen.sh adds the outputs from bs.sudo.",
               registers="'.WR' strings, hole 0 first: '.' empty, 'W' white, 'R' red (SPEC §3)",
               dice="faces by kind of die, in the order BUILD reads them (SPEC §4.2): d12 hole die, d6 (growth and Sub/Cruiser), d10 (one per hole pair; 0 is thrown again)",
               vectors=vectors)
    with open(os.path.join(HERE, "inputs.json"), "w") as fh:
        fh.write(compact(json.dumps(doc, indent=1)) + "\n")
    print("wrote inputs.json:", len(vectors), "vectors")


if __name__ == "__main__":
    main()
