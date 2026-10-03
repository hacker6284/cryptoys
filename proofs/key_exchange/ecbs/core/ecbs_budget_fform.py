#!/usr/bin/env python3
"""Grid budget (ecbs_budget.budget, unchanged bookkeeping) applied to the MEASURED band peaks of ecbs_fform
(pegs-only keys chosen for the key-limited tiers), spec schedule vs F-form + lazy-y validation."""
import json, sys
sys.dont_write_bytecode = True
from ecbs_budget import budget
W = {}
for f in ("ecbs_fform_Demo_Toy_Hobby.json", "ecbs_fform_Serious.json"): W.update(json.load(open(f)))
out = {}
for key, v in W.items():
    if not isinstance(v, dict) or 'bands' not in v: continue
    name, enc_p, kind, lab = key.split('_', 3); p = int(enc_p[4:])
    tw = 'trace WALK' in lab
    b = budget(name, 'pegs', p, kind, max(v['bands'].get('public walk', 0), v['bands'].get('shared walk', 0)),
               v['bands'].get('validation', 0), v['tally'], tw)
    out[key] = dict(b, moves=v['moves'])
    if b['total'] is None:
        print(f"{name:7s} pegs {p:3d} {kind:6s} [{lab:26s}] bands {b['bands']}: {b['note']}; moves/person {v['moves']/1e6:.4f} M"); continue
    print(f"{name:7s} pegs {p:3d} {kind:6s} [{lab:26s}] bands {b['bands']}; control need {b['need']} of {b['avail']} holes; "
          f"=> workspace {b['work']} + key {b['key']} = {b['total']} grids{'' if b['fits'] else ' (CONTROL DOES NOT FIT)'}; moves/person {v['moves']/1e6:.4f} M")
json.dump(out, open("ecbs_budget_fform.json", "w"), indent=1)
