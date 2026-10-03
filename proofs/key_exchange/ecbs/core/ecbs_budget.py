#!/usr/bin/env python3
"""Grid and control-hole budget for the lane + workbench layout, from MEASURED band peaks and tallies
(ecbs_workbench.json).  Nothing here is simulated; it is bookkeeping over measured numbers.
Layout (TOYMASTER_IDEAS H1/D1, re-verified in ecbs_workbench.py):
  Demo:   target grid = five 2-wide lanes; lane 1 = workbench (20 holes: base + 19-hole cube strip);
          lanes 2-5 = 8 register slots (4 rows x 2, last hole empty) + 16 control holes (rows 9-10).
  Toy:    8-wide lanes; a grid = 3 bands (rows A-I, 3 x 8 less the last hole) + 28 control holes
          (columns 9-10 and row J); workbench = one whole grid.
  Hobby:  double grid (20 wide, 2 grids butted side by side) = 3 bands (3 x 20 less the last hole) + row J (20).
          workbench = one double grid.
  Serious: double grid = 1 band (rows A-I, 9 x 20 less the last hole) + row J (20); workbench = 3 double grids.
Control items: colour-flip tally (measured max), one script-marker row (projective: 12 lines + cube X, Y, Z = 15;
  chord: 5 lines + cube x, y = 7; validation reuses the same row), inversion ladder (n-1), trace ladder (n),
  parking hole (fleet keys, W1 cursor) or coordinate rails (20, grid-hole keys), protocol phase (3)."""
import json, math
W = json.load(open("ecbs_workbench.json"))
N = {"Demo": 7, "Toy": 23, "Hobby": 59, "Serious": 179}
def chain_len(m): return len(bin(m)) - 3

def budget(name, enc, p, kind, bands_walk, bands_val, tally, trace_walk=False):
    n = N[name]
    items = {"tally": tally, "script row": 15 if kind == 'proj' else 7, "inversion ladder": chain_len(n - 1),
             "trace ladder": 0 if trace_walk else chain_len(n), "protocol phase": 3}
    if enc == 'three': items["parking hole (W1)"] = 1
    keygrids = p if enc in ('three', 'six') else -(-p // 100)
    rails_in_key = enc == 'pegs' and (p % 100) and (p % 100) <= 80
    if enc != 'three' and not rails_in_key: items["coordinate rails"] = 20
    need = sum(items.values()); bands = max(bands_walk, bands_val)
    if name == "Demo":
        slots = 8
        if bands > slots:
            return dict(items=items, need=need, avail=16, bands=bands, work=None, key=1, total=None,
                        extra_control_grids=0, rails_in_key=False, note="does not fit: more than 8 register slots")
        avail = 16 + 8 * (slots - bands) - (8 if trace_walk else 0)   # free slots; one is the trace-walk ruler
        work = 1; total = 2
    elif name == "Toy":
        reg_grids = -(-bands // 3); work = 1 + reg_grids; avail = 28 * work; total = work + keygrids
    elif name == "Hobby":
        reg_dg = -(-bands // 3); work = 2 * (1 + reg_dg); avail = 20 * (1 + reg_dg); total = work + keygrids
    else:
        reg_dg = bands; work = 2 * (3 + reg_dg); avail = 20 * (3 + reg_dg); total = work + keygrids
    extra = 0
    while need > avail and name != "Demo":                       # add a control grid (100 holes) if the spare holes are short
        extra += 1; avail += 100
    return dict(items=items, need=need, avail=avail, bands=bands, work=work + extra, key=keygrids,
                total=total + extra, extra_control_grids=extra, rails_in_key=bool(rails_in_key),
                fits=need <= avail)

def main():
    out = {}
    for key, v in W.items():
        if key in ('geometry', 'w1'): continue
        name, label = key.split('_', 1)
        parts = label.split(); enc, p, kind = parts[0], int(parts[1]), parts[2]
        tw = '+trace-walk' in label
        b = budget(name, enc, p, kind, max(v['bands'].get('public walk', 0), v['bands'].get('shared walk', 0)),
                   v['bands'].get('validation', 0), v['tally'], tw)
        out[key] = b
        if b['total'] is None:
            print(f"{name:7s} {label:26s} bands {b['bands']}: {b['note']}; moves/person {v['moves']/1e6:.3f} M"); continue
        print(f"{name:7s} {label:26s} bands {b['bands']}; control need {b['need']} of {b['avail']} holes "
              f"({', '.join(f'{k} {x}' for k, x in b['items'].items() if x)}); rails in key grid: {b['rails_in_key']}; "
              f"=> workspace {b['work']} + key {b['key']} = {b['total']} grids{'' if b['fits'] else ' (CONTROL DOES NOT FIT)'}; moves/person {v['moves']/1e6:.3f} M")
    json.dump(out, open("ecbs_budget.json", "w"), indent=1)

if __name__ == "__main__":
    main()
