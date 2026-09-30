"""'Pair off the whites' checksum (casting out twos) for BS multiplications.
Every hole value is 3^i = odd, so a register is odd  <=>  it has an odd number of WHITE pegs (reds count
as two).  Checks:  (1) before folding: the strip has odd whites  <=>  A and B both have odd whites
(a nudge multiplies by 3 or 9, which is odd: no change).  (2) folding: each lifted WHITE flips the
parity, lifted reds don't (lifting d*3^h and laying d*toll*3^(h-n) subtracts d*3^(h-n)*p, p odd).
We verify the checks hold on correct runs and measure how often a single wrong peg is caught."""
import os
os.chdir(os.path.dirname(os.path.abspath(__file__)))          # every path below is relative to this directory
import json, random
import bspegs as P, bsref as R
PAR = json.load(open("params.json")); rng = random.Random(3)
odd = lambda reg: sum(x == 'W' for x in reg) % 2 == 1
def checked_mul(F, A, B, nudge=0, inject=None):
    strip = F.empty(2*F.n + 3)
    for i, b in enumerate(B):
        if b != '.': P.lay(strip, A, i + nudge, 1 if b == 'W' else 2)
    if inject == 'lay':                                   # one wrong peg while laying
        i = rng.randrange(2*F.n); strip[i] = rng.choice([c for c in '.WR' if c != strip[i]])
    ok1 = odd(strip) == (odd(A) and odd(B))
    before = odd(strip); flips = 0; n = F.n; h = len(strip) - 1
    while h >= n:
        c = strip[h]
        if c == '.': h -= 1; continue
        strip[h] = '.'; flips += c == 'W'
        for _ in range(1 if c == 'W' else 2):
            for j, t in F.toll_pegs: P.drop(strip, h - n + j, t)
    if inject == 'fold':
        i = rng.randrange(n); strip[i] = rng.choice([c for c in '.WR' if c != strip[i]])
    ok2 = odd(strip[:n]) == (before ^ (flips % 2 == 1))
    return strip[:n], ok1, ok2
for tier in ("T1", "T2", "T6demo"):
    d = PAR[tier]; n = d['n']; p = int(d['p']); toll = R.enc(int(d['c']), n)
    while toll[-1] == '.': toll.pop()
    F = P.Field(n, toll); res = {}
    for mode in (None, 'lay', 'fold'):
        caught = good = 0; T = 300
        for _ in range(T):
            a, b = rng.randrange(3**n), rng.randrange(3**n)
            r, ok1, ok2 = checked_mul(F, R.enc(a, n), R.enc(b, n), rng.choice([0, 1, 2]), mode)
            good += ok1 and ok2; caught += not (ok1 and ok2)
        res[str(mode)] = f"checks pass {good}/{T}" if mode is None else f"error caught {caught}/{T}"
    print(tier, json.dumps(res))
