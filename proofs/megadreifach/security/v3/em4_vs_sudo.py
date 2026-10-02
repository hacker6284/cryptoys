"""MegaDreifach v3: the study's fast engine em4 against the sudoc JS build of the normative sudo.

This is not a check of the spec. The sudo (primitives/hash/megadreifach/v3/megadreifach.sudo) is the
spec; this script only tests that the fast engine the SPEC v3 §8 statistics were computed with,
study/mdw4_lib.em4 with kind ZP3F0E and m = 26, computes the same function. Whether em4 stays in
tree is an open question for the maintainer.

For seeded random (h, deal) pairs (uniform legal h; uniform deals, plus deals with each King held),
it compares compose(h, em4(h, deal)) encoded as the 29-byte digest with HashDeckBodyFrom(deal, h)
of the sudoc JS build ($MD3_OUT, default /tmp/megadreifach-v3), through sudo_body_from.mjs.

    sudoc build --target js -o /tmp/megadreifach-v3 primitives/hash/megadreifach/v3/megadreifach.sudo
    MD3_OUT=/tmp/megadreifach-v3 python3 proofs/megadreifach/security/v3/em4_vs_sudo.py [--check]

Without --check it prints its report and writes logs/em4_vs_sudo.log. With --check it never writes:
it prints "OK <log>" if a fresh run reproduces the committed log, else "STALE <log>" and exits 1.
Exit status is 1 on any mismatch. Run by tools/generate-demos.sh with --check.
"""
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'study'))
import mdfix_lib as L  # noqa: E402  (imports ../v2/engine.py, which imports m9_search)
import mdw4_lib as Z  # noqa: E402

eng = L.eng
ref = eng.ref
LOG = os.path.join(HERE, 'logs', 'em4_vs_sudo.log')
SEED = 20261002
N_UNIFORM = 60


def cases():
    rng = random.Random(SEED)
    out = []
    for i in range(N_UNIFORM + 4):
        h = L.uniform_st(rng)
        d = list(range(52))
        rng.shuffle(d)
        if i >= N_UNIFORM:                      # the held card 52 is K♣, K♥, K♠, K♦
            king = 48 + i - N_UNIFORM
            a = d.index(king)
            d[a], d[51] = d[51], d[a]
        out.append((h, d))
    return out


def main():
    check = '--check' in sys.argv[1:]
    cs = cases()
    items = []
    fast = []
    for h, d in cs:
        hp = eng.as_tuple_pos(eng.from_st(h))
        e = eng.as_tuple_pos(eng.from_st(Z.em4('ZP3F0E', 26, h, d)))
        fast.append(bytes(ref.to_bytes(ref.compose(hp, e))).hex())
        items.append({'deal': d, 'h': {'cp': list(hp[0]), 'co': list(hp[1]), 'ep': list(hp[2]), 'eo': list(hp[3])}})
    js = os.path.join(HERE, 'sudo_body_from.mjs')
    res = subprocess.run(['node', js], input=json.dumps(items), capture_output=True, text=True, check=True)
    sudo = res.stdout.split()
    assert len(sudo) == len(fast), (len(sudo), len(fast))
    same = sum(a == b for a, b in zip(fast, sudo))
    kings = sum(a == b for a, b in zip(fast[N_UNIFORM:], sudo[N_UNIFORM:]))
    lines = [
        'em4_vs_sudo: study fast engine mdw4_lib.em4 (ZP3F0E, m = 26) vs HashDeckBodyFrom of the sudoc JS build '
        'of v3/megadreifach.sudo (normative). Not a check of the spec.',
        f'seed {SEED}: {N_UNIFORM} uniform (h, deal) pairs + 4 with K♣/K♥/K♠/K♦ held',
        f'equal digests: {same}/{len(fast)} (King held: {kings}/4)',
        f'first digest {sudo[0]}',
        f'last digest  {sudo[-1]}',
    ]
    text = '\n'.join(lines) + '\n'
    rel = os.path.relpath(LOG, os.path.join(HERE, '..', '..', '..', '..'))
    if same != len(fast):
        sys.stdout.write(text)
        print('em4_vs_sudo: MISMATCH')
        sys.exit(1)
    if check:
        old = open(LOG, encoding='utf-8').read() if os.path.exists(LOG) else ''
        if old == text:
            print(f'OK {rel}')
        else:
            print(f'STALE {rel}')
            sys.exit(1)
    else:
        sys.stdout.write(text)
        with open(LOG, 'w', encoding='utf-8') as f:
            f.write(text)


if __name__ == '__main__':
    main()
