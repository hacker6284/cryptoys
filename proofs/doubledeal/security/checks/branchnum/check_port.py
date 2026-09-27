"""Check the v9 port layers used here against the repo's known-answer vectors."""
import json
from pathlib import Path
from common import P, lay_cm, scoop_cm
V = json.load(open(Path(__file__).resolve().parents[3] / 'vectors/doubledeal_vectors.json'))['vectors']
ok = bad = 0
for x in V:
    k = x['kind']
    if k == 'encrypt': got, want = P.encrypt(x['message'], x['key'], 9), x['cipher']
    elif k == 'mix_columns': got, want = P.mix_columns(x['input'], 9), x['output']
    elif k == 'unkeyed_full': got, want = P.mix_columns(P.stem(x['input'], 9), 9), x['output']
    elif k == 'sum_ranks':
        inp = x['input']
        if isinstance(inp[0], list): got, want = P.sum_ranks(inp, 9), x['output']
        else: got, want = scoop_cm(P.sum_ranks(lay_cm(inp), 9)), x['output']
    else: continue
    if got == want: ok += 1
    else: bad += 1; print('MISMATCH', x['name'])
print(f'v9 port vs repo vectors: {ok} ok, {bad} mismatch')
assert bad == 0
