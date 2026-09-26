import json, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import dd_v8 as dd
V = json.load(open('' + __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'doubledeal_v8_vectors.json') + ''))['vectors']
ok = bad = 0
for v in V:
    k = v['kind']
    if k == 'encrypt': got, exp = dd.encrypt(v['message'], v['key']), v['cipher']
    elif k == 'passkey': got, exp = dd.passkey(v['input']), v['output']
    elif k == 'expand_keys': got, exp = dd.expand_keys(v['k0']), v['keys']
    elif k == 'counter_deck': got, exp = dd.counter_deck(v['nonce'], v['index']), v['deck']
    elif k == 'mix_columns': got, exp = dd.mix_columns(v['input']), v['output']
    elif k == 'sum_ranks': got, exp = dd.scoop_cm(dd.sum_ranks(dd.lay_cm(v['input']))), v['output']
    elif k == 'shift_rows': got, exp = dd.scoop_cm(dd.shift_rows(dd.lay_cm(v['input']))), v['output']
    elif k == 'unkeyed_full': got, exp = dd.unkeyed_full(v['input']), v['output']
    elif k == 'compose': got, exp = dd.compose(v['message'], v['key']), v['output']
    elif k == 'ctr_encrypt': got, exp = dd.ctr_encrypt(v['blocks'], v['key'], v['nonce']), v['output']
    else: print('skip', v['name']); continue
    if got == exp: ok += 1
    else: bad += 1; print('MISMATCH', v['name'])
    if k == 'encrypt': assert dd.decrypt(got, v['key']) == v['message']
    if k == 'passkey': assert dd.passkey_inv(got) == v['input']
print(f'{ok} ok, {bad} mismatch')
