"""Re-verify every witness printed in search.log / search2.log from scratch and write
witnesses.json (target, version, positions, deck, output weight). Prints card names.
usage: python3 witnesses.py > witnesses.log
"""
import re, json, ast
from pathlib import Path
from common import *
import search as S   # reuses TARGETS / apply_cycle (search's __main__ block does not run on import)

out = []
for log in ('search.log', 'search2.log'):
    p = Path(__file__).with_name(log)
    if not p.exists(): continue
    lines = p.read_text().splitlines()
    for a, b in zip(lines, lines[1:]):
        m = re.match(r'(v\d .*?)\s+min out=\s*(\d+)', a)
        if not m or 'positions=' not in b: continue
        name, w = m.group(1).strip(), int(m.group(2))
        pos = ast.literal_eval(re.search(r'positions=(\[.*?\])', b).group(1))
        deck = ast.literal_eval(re.search(r'deck=(\[.*\])', b).group(1))
        F = S.TARGETS[name][0]()
        w2 = wt(F(deck), F(S.apply_cycle(deck, pos)))
        assert w2 == w and sorted(deck) == list(range(52)), (name, w, w2)
        out.append(dict(target=name, positions=pos, out_weight=w, in_weight=len(pos), deck=deck))
        print(f'{name:36s} in={len(pos)} out={w}  positions {pos} cards {[NAMES[deck[i]] for i in pos]}')
        print(f'    {show(deck)}')
# trail logs: re-verify the per-round weight profile of every reported trail
import ddport
from dd_v8 import expand_keys, compose
KS = expand_keys(FIXED_KEY)
for log in sorted(Path(__file__).parent.glob('trail_v*_*.log')):
    lines = log.read_text().splitlines()
    head = lines[0]; v = int(re.search(r'# v(\d)', head).group(1))
    if 'full encrypt' in head:
        steps = [lambda x: compose(x, KS[0])] + [lambda x, k=KS[r]: ddport.full_round(x, k, v) for r in range(1, 6)] \
                + [lambda x: ddport.final_round(x, KS[6], v)]
    else:
        R = int(re.search(r'(\d) keyed rounds', head).group(1))
        steps = [lambda x, k=KS[r]: ddport.full_round(x, k, v) for r in range(1, R + 1)]
    for a, b in zip(lines, lines[1:]):
        m = re.match(r'rounds alive as a swap: (\d+)/(\d+); per-round weights (\[.*?\]); swap \((\d+),(\d+)\)', a)
        if not m: continue
        ws = ast.literal_eval(m.group(3)); i, j = int(m.group(4)), int(m.group(5))
        deck = ast.literal_eval(re.search(r'deck=(\[.*\])', b).group(1))
        x, y, got = deck, swap(deck, i, j), []
        for f in steps:
            x, y = f(x), f(y); got.append(wt(x, y))
            if got[-1] != 2: break
        assert got == ws, (log.name, ws, got)
        if int(m.group(1)) == int(m.group(2)) or int(m.group(1)) >= 4:
            out.append(dict(target=f'{log.name}: {head[2:]}', positions=[i, j], per_round_weights=ws, deck=deck))
            print(f'{log.name}: alive {m.group(1)}/{m.group(2)} weights {ws} swap ({i},{j}) cards {NAMES[deck[i]]},{NAMES[deck[j]]}')
            print(f'    {show(deck)}')
Path(__file__).with_name('witnesses.json').write_text(json.dumps(out, indent=1))
print(f'{len(out)} witnesses re-verified')
