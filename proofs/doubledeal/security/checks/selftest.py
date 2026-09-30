"""Check the v8/v9/v10/v11/v12 Python port: v12 against the current vectors, v11, v10 and v9
against their frozen vectors, v8 against frozen dd_v8.py. Then rerun analysis scripts: the
frozen-v10 SumRanks checks (exit status only), the GridCycle cross-checks (byte-compared with
their committed logs), and the v12-linear exact 4-card toy check (toy_link.py, byte-compared
with toy_link.log; it checks the toy, not the Lean)."""
import random, sys, ddport as P, dd_v8 as V8
from ddport import REPO
from dd_v8 import lay_cm, scoop_cm
def check(v):
    n = 0
    for vec in P.vectors(v):
        k = vec['kind']
        if k == 'encrypt': got, exp = P.encrypt(vec['message'], vec['key'], v), vec['cipher']
        elif k == 'mix_columns': got, exp = P.mix_columns(vec['input'], v), vec['output']
        elif k == 'sum_ranks': got, exp = scoop_cm(P.sum_ranks(lay_cm(vec['input']), v)), vec['output']
        elif k == 'unkeyed_full': got, exp = P.mix_columns(P.stem(vec['input'], v), v), vec['output']
        elif k == 'passkey' and v >= 12: got, exp = P.passkey(vec['input'], v), vec['output']
        elif k == 'expand_keys' and v >= 12: got, exp = P.expand_keys_v(vec['k0'], v), vec['keys']
        else: continue
        if got != exp: print(f'MISMATCH v{v}', vec['name']); sys.exit(1)
        n += 1
    print(f'v{v} port matches', n, 'vectors')
check(12)
check(11)
check(10)
check(9)
rng = random.Random(10)
for _ in range(50):
    m = list(range(52)); rng.shuffle(m)
    g = lay_cm(m)
    assert P.inv_sum_ranks_v10(P.sum_ranks_v10(g)) == g, f"v10 inv SumRanks fails on deck {m}"
print('v10 inv SumRanks undoes SumRanks on 50 random decks')
rng = random.Random(11)
for _ in range(200):
    m = list(range(52)); rng.shuffle(m)
    assert P.inv_mix_columns_v11(P.mix_columns(m, 11)) == m, f"v11 inverse GridCycle fails on deck {m}"
print('v11 inverse GridCycle undoes GridCycle on 200 random decks')
rng = random.Random(12)
for _ in range(300):
    m = list(range(52)); rng.shuffle(m)
    assert P.passkey_inv(P.passkey(m, 12), 12) == m and P.passkey(P.passkey_inv(m, 12), 12) == m, \
        f"v12 PassKey inverse fails on deck {m}"
print('v12 PassKey inverse is two-sided on 300 random decks')
rng = random.Random(1)
for _ in range(300):
    m = list(range(52)); rng.shuffle(m); k = list(range(52)); rng.shuffle(k)
    assert P.encrypt(m, k, 8) == V8.encrypt(m, k), f"v8 port != dd_v8.py for m={m}, k={k}"
print('v8 port == frozen dd_v8.py on 300 random (m,k)')
# Frozen-v10 analysis checks (need numpy and gcc; ~4 s). They read the frozen v10 vectors, so they
# break loudly here instead of silently when the live vectors move.
import subprocess
AN = REPO / 'proofs/doubledeal/analysis/v10-sumranks'
for script in (AN / 'check_cand.py', AN / 'sbox-search/verify.py'):
    r = subprocess.run([sys.executable, str(script)], cwd=script.parent, capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout, r.stderr); print('FAIL', script.relative_to(REPO)); sys.exit(1)
    print(script.relative_to(REPO), 'ok:', r.stdout.strip().splitlines()[-1][:120])
# GridCycle analysis cross-checks (need cc; ~10 s): the independent Python models against the
# C tools, byte-compared with their committed logs.
GC = REPO / 'proofs/doubledeal/analysis/v10-gridcycle'
r = subprocess.run(['sh', str(GC / 'build.sh')], capture_output=True, text=True)
if r.returncode != 0:
    print(r.stdout, r.stderr); print('FAIL', (GC / 'build.sh').relative_to(REPO)); sys.exit(1)
for script, log in (('candcheck.py', 'candcheck.log'), ('p5check.py', 'p5/check.log'), ('p6check.py', 'p6/check.log')):
    r = subprocess.run([sys.executable, script], cwd=GC, capture_output=True, text=True)
    if r.returncode != 0 or r.stdout != (GC / log).read_text():
        print(r.stdout, r.stderr); print('FAIL', (GC / script).relative_to(REPO), 'vs', log); sys.exit(1)
    print((GC / script).relative_to(REPO), '==', log)
# M8a exact 4-card toy check of the Linear identities (pure Python; ~6 s), byte-compared with
# its committed log.
LIN = REPO / 'proofs/doubledeal/analysis/v12-linear'
r = subprocess.run([sys.executable, 'toy_link.py'], cwd=LIN, capture_output=True, text=True)
if r.returncode != 0 or r.stdout != (LIN / 'toy_link.log').read_text():
    print(r.stdout, r.stderr)
    print('FAIL', (LIN / 'toy_link.py').relative_to(REPO), 'vs toy_link.log'); sys.exit(1)
print((LIN / 'toy_link.py').relative_to(REPO), '== toy_link.log')
