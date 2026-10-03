#!/usr/bin/env python3
"""No-paper move counts per person (public walk + validation + shared walk, control markers included),
3 random keys per option, every run checked against PARI.  Assumed 1 move/s for hours."""
import random, json, statistics as st
import ecbs_physical as PH
plan = {"Toy": [('three', 1), ('pegs', 19)],
        "Hobby": [('three', 2), ('pegs', 54), ('pegs', 55), ('six', 1)],
        "Serious": [('three', 6), ('three', 7), ('pegs', 162), ('pegs', 173), ('pegs', 175), ('pegs', 200), ('six', 2)]}
out = {}; rnd = random.Random(31337)
for name, runs in plan.items():
    base = None
    for enc, p in runs:
        res = []
        while len(res) < 3:
            try: r = PH.run(name, enc, p, rnd)
            except ArithmeticError: continue
            assert all(r['ok']) and r['leaks'] == 0
            res.append(r)
        mv = [r['moves'] + r['ctrl'] for r in res]; val = st.mean(r['val'] for r in res)
        m = st.mean(mv); base = base or m
        out[f"{name}_{enc}{p}"] = dict(moves=mv, mean=m, validation=val)
        print(f"{name:8s} {enc:6s} {p:4d}: per person {m/1e6:7.3f} M moves (runs {[round(x/1e6, 2) for x in mv]}), "
              f"validation {val/1e6:.2f} M; x{m/base:.3f} vs first option; {m/3600:,.0f} h @ 1 move/s", flush=True)
json.dump(out, open("ecbs_physical_costs.json", "w"), indent=1)
