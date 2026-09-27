"""Check dd_v8.py (Python port of the frozen v8 sudo) against the frozen v8 vectors.

Also fails if the vectors' sudo_sha256 is not the frozen v8 sudo (the frozen file must not drift).
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dd_v8 as dd  # noqa: E402

VECTORS = HERE.parent / "vectors" / "doubledeal_v8_vectors.json"
V8_SUDO = HERE.parents[3] / "primitives" / "cipher" / "doubledeal" / "v8" / "doubledeal_v8.sudo"


def evaluate(v):
    k = v['kind']
    if k == 'encrypt':
        return dd.encrypt(v['message'], v['key']), v['cipher']
    if k == 'passkey':
        return dd.passkey(v['input']), v['output']
    if k == 'expand_keys':
        return dd.expand_keys(v['k0']), v['keys']
    if k == 'counter_deck':
        return dd.counter_deck(v['nonce'], v['index']), v['deck']
    if k == 'mix_columns':
        return dd.mix_columns(v['input']), v['output']
    if k == 'sum_ranks':
        return dd.scoop_cm(dd.sum_ranks(dd.lay_cm(v['input']))), v['output']
    if k == 'shift_rows':
        return dd.scoop_cm(dd.shift_rows(dd.lay_cm(v['input']))), v['output']
    if k == 'unkeyed_full':
        return dd.unkeyed_full(v['input']), v['output']
    if k == 'compose':
        return dd.compose(v['message'], v['key']), v['output']
    if k == 'ctr_encrypt':
        return dd.ctr_encrypt(v['blocks'], v['key'], v['nonce']), v['output']
    return None


def main():
    doc = json.loads(VECTORS.read_text())
    sha = hashlib.sha256(V8_SUDO.read_bytes()).hexdigest()
    if doc['sudo_sha256'] != sha:
        print(f"sudo_sha256 mismatch: json={doc['sudo_sha256']} {V8_SUDO.name}={sha}")
        sys.exit(1)
    ok = bad = 0
    for v in doc['vectors']:
        res = evaluate(v)
        if res is None:
            print('skip', v['name'])
            continue
        got, exp = res
        if got == exp:
            ok += 1
        else:
            bad += 1
            print('MISMATCH', v['name'])
        if v['kind'] == 'encrypt':
            assert dd.decrypt(got, v['key']) == v['message']
        if v['kind'] == 'passkey':
            assert dd.passkey_inv(got) == v['input']
    print(f'{ok} ok, {bad} mismatch')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
