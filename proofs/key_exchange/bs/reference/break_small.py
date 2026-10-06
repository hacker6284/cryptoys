"""Honesty demo: the toy tiers fall to textbook generic attacks in seconds.
T1: baby-step/giant-step in Python.  T2: Pollard rho in C (break_t2.c).  Eve recovers e mod q from a
public key built from a dice-built ships+pegs key grid and then computes the shared secret."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent                        # every path below is built from this directory
sys.path.insert(0, str(HERE.parent / "ships-pegs"))
import keygrid as KG
KEY = lambda rng: [KG.board_string(rng)]                    # one ships+pegs key grid (BS SPEC §4.2-§4.3)
import json, random, subprocess, time, math
import bsref as R
PAR = json.load(open(HERE / "params.json")); rng = random.Random(99)
def bsgs(g, h, p, q):
    m = math.isqrt(q) + 1; table = {}; x = 1
    for j in range(m): table.setdefault(x, j); x = x * g % p
    f = pow(g, -m, p); y = h
    for i in range(m):
        if y in table: return i*m + table[y]
        y = y * f % p
for tier in ("T1", "T2"):
    p, q = int(PAR[tier]['p']), int(PAR[tier]['q'])
    fa = KEY(rng); fb = KEY(rng)
    ea, eb = R.exponent(fa), R.exponent(fb); A, B = pow(3, ea, p), pow(3, eb, p)
    t = time.time()
    if tier == "T1": x = bsgs(3, A, p, q); how = "BSGS (Python)"
    else:
        o = subprocess.run([str(HERE / "break_t2"), str(p), str(q), str(A)], capture_output=True, text=True).stdout.split()
        x = int(o[0]); how = f"Pollard rho (C, {int(o[1]):,} Floyd iterations)"
    K_eve = pow(pow(B, 2, p), x, p); K_true = pow(3, 2*ea*eb, p)
    print(f"{tier}: q ~ 2^{math.log2(q):.1f}; {how}: recovered e_A mod q in {time.time()-t:.2f}s; "
          f"e_A mod q correct: {x == ea % q}; Eve's K == real K: {K_eve == K_true}")
