# PLAYER_CARD_v2: evidence and spec fixes (scratch; nothing committed)

Code: `homes.py` (fixed-home board, each card rule written literally), `card_sim.py` (full exchanges vs PARI),
`soundness.py` (field level + peg level), `extras.py` (keypad, root strip, per-op costs, sparse search).
Outputs: `card_sim_{Toy,Hobby,Serious}.txt/json`, `soundness_{field,peg}_*.json`, `extras.json`.

## Band homes (literal board, keys of 16 / 51 / 162 pegs-only cells, 2 trace + 2 certificate exchanges per tier)
- Every exchange matches PARI: public points = kP, the shared keys agree and equal the reference, and the base point by rule = P.
- Peak is 7 homes at every tier. It stays 7 even counting a band as occupied while its pegs are being lifted.
  Workbench grids stay at 5 / 9 / 22.
- No clash: a result never lands in an occupied home (asserted). Every fold drop lands in [0, e) inside the
  3-band workbench; the highest hole used is 66/72, 174/180, 534/540.
- Script row per add, taken from the literal walk: 3 cubes, then run 1, rise 1, gap 5, bottom 1, new X 2, new Y 2 = 15.

## Check costs (moves per person, measured)
| | Toy | Hobby | Serious |
|---|---|---|---|
| curve test + trace check | 46.4k | 0.391 M | 3.91–3.95 M |
| certificate (make + check, incl. C's curve test) | 14.7k | 0.091 M | 0.74 M |
| base point by rule (once per game) | 23,352 | 105,699 | 734,782 |

## Soundness (field level: honest / kP+GF(3) point / random curve point / the 4 order-5 points)
- Toy (5000 trials per class), Hobby (3000), Serious (1000): the trace check accepted every subgroup point
  and rejected every non-subgroup point. The certificate: every honest point was accepted, 0 forged
  non-subgroup keys were accepted, and every (tau-1) image of an arbitrary curve point landed in the subgroup.
  The ladder inversion was never wrong.
- Peg level (30 / 15 / 6 per class, plus the 4 order-5 points): same verdicts.

## Spec fixes for re-land
See the parent report.
