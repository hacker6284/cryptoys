"""v3 bookkeeping over measured numbers: grid counts at 7 and 9 bands (ecbs_budget.budget, read-only),
the control-row layout need vs row-J holes, the 'call all four bands at once' schedule (negative
control), and the base point's share of each person's moves (from card_sim_v3_*.json)."""
import sys, os, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import homes as H, homes_v3 as V
os.chdir(H.ECBS)
import ecbs_budget as Bu, ecbs_exchange as X
os.chdir(HERE)
CELLS = {'Toy': 16, 'Hobby': 51, 'Serious': 162}
out = {}
for name in ('Toy', 'Hobby', 'Serious'):
    runs = json.load(open(f'card_sim_v3_{name}.json'))[name]
    c = runs[0]['control']; T = X.Tier(name)
    need = V.SCRIPT + V.PHASE + V.CALLING + len(c['ladder']) + 1 + max(r['control']['tally_max'] for r in runs)
    g = {b: Bu.budget(name, 'pegs', CELLS[name], 'proj', b, b, c['tally_max']) for b in (7, 9)}
    tot = [r['moves'][w] for r in runs for w in 'AB']
    Pm = [r['moves_by_phase'][w]['base point'] for r in runs for w in 'AB']
    ph = {}
    for r in runs:
        for w in 'AB':
            for k, v in r['moves_by_phase'][w].items(): ph.setdefault(k, []).append(v)
    ctrl = [r['ctrl'][w] for r in runs for w in 'AB']
    out[name] = dict(
        runs=len(runs), people=len(tot),
        moves_per_person_mean=round(sum(tot) / len(tot)), moves_min=min(tot), moves_max=max(tot),
        moves_by_phase_mean={k: round(sum(v) / len(v)) for k, v in ph.items()},
        check_share_mean=round(sum(ph['curve test'] + ph['make certificate'] + ph['rebuild theirs']) / sum(tot), 4),
        base_point_moves=Pm[0], base_point_share_mean=round(sum(Pm) / sum(tot), 4),
        control_moves_mean=round(sum(ctrl) / len(ctrl)), ladder_build_once=runs[0]['ladder_build_once'],
        calls_per_person=runs[0]['calls']['A'], calls_expected_4n=4 * T.n,
        control_row=dict(holes=c['row_holes'], need=need, layout=f"script 0-14, phase 15, calling 16, ladder 17-{16 + len(c['ladder'])}, "
                         f"parking {c['park_hole']}, tally {c['tally_first']}-{c['tally_first'] + c['tally_max'] - 1}",
                         highest_hole_used=max(r['control']['highest_hole_used'] for r in runs)),
        grids={b: dict(workspace=g[b]['work'], key=g[b]['key'], total=g[b]['total']) for b in (7, 9)})
    # negative control: both C and A published together; the receiver still holds its own C and A
    hb = V.HB3(name, T.n, T.k)
    for h in ('across', 'up', 'base across', 'base up'): hb.put(h, ['W'] + ['.'] * (T.n - 1))
    empty = [h for h, v in hb.home.items() if v is None]
    out[name]['all_four_at_once'] = dict(empty_homes=len(empty), bands_to_receive=4, fits=len(empty) >= 4)
for name in out: print(name, json.dumps(out[name], indent=1))
json.dump(out, open(os.path.join(HERE, 'extras_v3.json'), 'w'), indent=1)
