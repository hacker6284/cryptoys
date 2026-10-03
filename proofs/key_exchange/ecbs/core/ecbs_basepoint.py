#!/usr/bin/env python3
"""Base point, curve constants and chains by RULE (no printed reference), re-verified in Crypto's own
peg harness (ecbs_pegs.Board, PARI-checked).  Rules (TOYMASTER_IDEAS F3, F4, F5):
  x = one white peg in hole 1; rhs = cube(x) + mirrored(x*x) + white peg in hole 0   ("y^2 = x^3 - x^2 + 1")
  root strip: y = rhs^((3^n+1)/4); its base-3 digits are red, empty, red, empty, ..., red, white (n-1 digits);
     walk it like a key: start empty; at each digit cube y (skip while empty), then multiply by rhs^2 (red)
     or rhs (white).
  if y*y != rhs, slide x's peg one hole on and repeat.
  P = walk white, red, white, red over (x, y)  (tau^3 - tau^2 + tau - 1 = 5 on this curve)
  halving ladder for the Itoh-Tsujii chain (from n-1) and the trace chain (from n):
     lay m white pegs; pair them off; a leftover peg = red rung, none = white rung; keep one per pair; repeat
     until one peg is left; read the rungs from the last one: white = double, red = double then +1."""
import json, hashlib
from ecbs_pegs import Board
from ecbs_ref import TIERS, pari
import ecbs_exchange as X

def trits(e):
    d = []
    while e: d.append(e % 3); e //= 3
    return d[::-1]

def ladder(m):
    rungs = []
    while m > 1:
        rungs.append('R' if m % 2 else 'W'); m //= 2
    return ''.join(reversed(rungs))

def it_program(m): return ''.join('R' if b == '1' else 'W' for b in bin(m)[3:])

def root_strip(Bd, rhs):
    n = Bd.n; strip = ['R', '.'] * ((n - 3) // 2) + ['R', 'W']
    assert len(strip) == n - 1
    r2 = Bd.mul(rhs, rhs); y = None
    for d in strip:
        if y is not None: y = Bd.cube(y)
        if d == '.': continue
        f = r2 if d == 'R' else rhs
        y = Bd.copy(f) if y is None else Bd.mul(y, f)
    return y, strip

def main():
    out = {}
    for name, (n, k, _) in TIERS.items():
        T = X.Tier(name); R = T.R; Bd = Board(n, k)
        e = (3 ** n + 1) // 4; tr = trits(e)
        pat = ''.join('.WR'[t] for t in tr); want = 'R.' * ((n - 3) // 2) + 'RW'
        j = 1; tries = []
        while True:
            m0 = Bd.moves
            x = ['.'] * n; x[j] = 'W'
            rhs = Bd.cube_keep(x); x2 = Bd.mul(x, x); Bd.add_into(rhs, x2, mirror=True); Bd.drop(rhs, 0, 'W')
            y, strip = root_strip(Bd, rhs)
            ok = Bd.mul(y, y) == rhs
            tries.append((j, ok, Bd.moves - m0))
            if ok: break
            j += 1
        m1 = Bd.moves
        P, mstrip = X.cofactor_strip(T, (x, y))
        good = P is not None and R.pt(P) == T.Pref and R.pt(P) == R.mul(5, R.pt((x, y))) and len(R.mul(T.l, R.pt(P))) == 1
        lad = {m: (ladder(m), it_program(m)) for m in (n - 1, n)}
        sx, sy = ''.join(P[0]), ''.join(P[1])
        digest = hashlib.sha256((sx + '|' + sy).encode()).hexdigest()[:16]
        print(f"{name}: x^{n} = x^{k} + 1")
        print(f"  root-strip digits of (3^n+1)/4 = {pat[:24]}{'...' if len(pat) > 24 else ''} (n-1 = {len(pat)} digits); "
              f"equals 'red, empty' repeated then 'red, white': {pat == want}")
        print(f"  tries: " + "; ".join(f"hole {jj}: y*y = rhs {okk} ({mv:,} moves)" for jj, okk, mv in tries))
        print(f"  P = white-red-white-red strip over (x, y): {mstrip:,} moves; equals 5(x,y) and has order l (PARI): {good}")
        print(f"  halving ladder from n-1 = {n-1}: {lad[n-1][0]} (Itoh-Tsujii program {lad[n-1][1]}: {lad[n-1][0] == lad[n-1][1]}); "
              f"from n = {n}: {lad[n][0]} (trace-chain program {lad[n][1]}: {lad[n][0] == lad[n][1]})")
        if n <= 23: print(f"  test vector P: x = {sx}  y = {sy}  (hole 0 first)")
        else: print(f"  test vector P: x = {sx[:30]}...  y = {sy[:30]}...  sha256(x|y)[:16] = {digest}")
        out[name] = dict(hole=j, root_digits_ok=pat == want, tries=tries, strip_moves=mstrip, P_ok=good,
                         ladder={str(m): v for m, v in lad.items()}, Px=sx, Py=sy, sha=digest)
    json.dump(out, open("ecbs_basepoint.json", "w"), indent=1)

if __name__ == "__main__":
    main()
