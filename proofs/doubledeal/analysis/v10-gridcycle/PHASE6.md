# Phase 6: anti-resync tweaks to rule 1

Analysis only. No change to the spec or to `main`; the rule choice is Zachary's. Heavy runs are outside
CI (`run_phase6.sh`, about 45 minutes on 8 cores). No bit-security claims.

## Why

PHASE5 showed where rule 1 loses average spread. Its ghost-finger targets are `start + Σ step(card)`, and a sum ignores order. So after the second swapped position both walks aim at the same targets again and often merge (49% of later placements for adjacent swaps). Rule 1's mean spread is 31.3, against 32.8 for v10.

Each tweak below makes the finger's path depend on order, using only things the decryptor sees at that moment: finger, marker, the card just recovered, and the blocker on the target. Every tweak keeps rule 1's blocked scan unchanged (row = marker + suit(blocker), start column = T.col + rank(blocker), first free seat to the right, drop a row if full, marker +1).

| id | name | change to rule 1 |
|---|---|---|
| 60 | **A** row-dependent step | column move = rank(card) + current finger row (mod 13); row move = suit |
| 61 | **A′** | column move = rank(card) × (finger row + 1) (mod 13) |
| 62 | **B** blocker nudges the finger | after a blocked placement the next step starts at T + step(blocker) instead of T; unblocked placements unchanged |
| 63 | **C** marker in the step | row move = suit(card) + marker (mod 4); marker advances on each block as in rule 1 |
| 64 | **A+B** | both (a combo, run for completeness) |

Code: `cand.c` (`target_of` and the case 60–64 block), `p3small.c` (small grids), `p5.c` (spread; includes `cand.c`).

## 1. Invertibility: all five are invertible

**Argument.** Rule 1 is invertible because every choice the walk makes depends only on things the decryptor already has at that step. The five tweaks keep that property:

- **A and A′** use the finger row, which the decryptor tracks.
- **B** uses the blocker. The blocker sits on T, and T is already ticked in the decryptor's table, so it can read it.
- **C** uses the marker, which the decryptor keeps too.

The decryptor replays the walk:

1. Compute the target from the finger (and the marker for C) and the card it just recovered.
2. If the target isn't ticked yet, the next card is on the target.
3. Otherwise, read the blocker, run the same scan over the unticked seats, read the card, advance the marker, and move the finger (T, or T + step(blocker) for B).

Each step is forced, so the map is a bijection.

**Evidence:**

- **Small grids, exhaustive** (`p6/small_injectivity.log`): on 2×3, 3×2, 2×4, 4×2 and 3×3, all n! decks give distinct outputs for v10, rule 1 and all of 60–64.
- **100k round trip** (`p6/cost.log`, `cand stats`: the inverse is a replay with ticked seats): 0 failures for every variant.
- **Independent Python** (`p6check.py`, `p6/check.log`): a separate encryptor and decryptor written from the rule text. Over 2 000 decks per variant: 0 output mismatches against `cand.c` and 0 round-trip failures. `candcheck.py` still matches the repo's `ddport` for v10 (`p6/candcheck.log`).

## 2–4. Comparison

Survival (as PHASE2) is value-pair swap survival at 200 000 decks per pair. The v10, rule 1 and rule 2 rows are the Phase 2 logs, produced by the same `cand.c` code path, which is unchanged for those ids. Spread (as PHASE5) uses all 1326 swaps × 20 000 decks, with baselines re-run using the same binary. Minima from sampling or hill-climbing are upper bounds.

### Survival and cost

| rule | worst pair, 95% CI | pairs > 1/64 | 3-cycle screen max / refined max | worst full round (v10 SumRanks) | seats per blocked placement mean / p90 / max | extra mental work vs rule 1 |
|---|---|---|---|---|---|---|
| v10 | 0.262 (K♣↔K♦) | 1311 | 0.086 (refined) | 1.4e-3 | 6.05 / 15 / 52 | n/a |
| rule 1 (33) | 0.0062 [0.0059, 0.0066] ≈ 1/161 | 0 | 0.0018 / 2.4e-4 | 1.0e-4 | 7.01 / 19 / 52 | baseline |
| rule 2 (30) | 0.0119 [0.0114, 0.0124] ≈ 1/84 | 0 | 0.0022 / 8.6e-4 | 1.6e-4 | 6.98 / 19 / 52 | one less add per block |
| **A (60)** | 0.0059 [0.0055, 0.0062] ≈ 1/170 | 0 | 0.0018 / 1.9e-4 | 1.1e-4 | 6.92 / 19 / 52 | +1 small add (finger row 0–3) on **every** step (51/deal) |
| A′ (61) | 0.0061 [0.0057, 0.0064] ≈ 1/164 | 0 | 0.0015 / 2.3e-4 | 7.8e-5 | 6.88 / 19 / 52 | a multiply mod 13 on every step |
| **B (62)** | **0.0049 [0.0046, 0.0052] ≈ 1/205** | 0 | 0.0015 / 2.5e-4 | 1.0e-4 | 7.03 / 20 / 52 | +1 row add (mod 4) **only on blocked placements** (~25/deal); the finger's new column is the scan-start column you already computed |
| C (63) | 0.0058 [0.0055, 0.0061] ≈ 1/172 | 0 | 0.0015 / 2.1e-4 | 1.1e-4 | 7.00 / 19 / 52 | +1 add (marker) on every step |
| A+B (64) | 0.0047 [0.0044, 0.0050] ≈ 1/212 | 0 | 0.0015 / 2.6e-4 | 9.3e-5 | 6.93 / 19 / 52 | A's and B's costs |

### Spread (diffusion)

| rule | mean / median | share spread = 2 / ≤ 4 / ≤ 8 | i<40: p1 / mean / share ≤ 4 | i<20: p1 / mean / share ≤ 4 | far apart (i<20, gap>16): sampled min / climb min / share = 2 | adjacent-swap merge (gap 1) | mean, gap ≤ 4 (i<40) | 3-cycle mean / share ≤ 4 |
|---|---|---|---|---|---|---|---|---|
| v10 | 32.76 / 35 | 0.0435 / 0.0535 / 0.0756 | 2 / 34.21 / 0.0280 | 17 / 41.24 / 0.0038 | 2 / 2 / 0.0042 | 0.28 | 27.51 | 38.16 / 0.0088 |
| rule 1 | 31.33 / 32 | 0.00506 / 0.0137 / 0.0406 | 9 / 32.61 / 0.0018 | 17 / 38.46 / 0.00051 | 22 / 16 / 0 | 0.49 | 20.98 | 37.68 / 0.00071 |
| rule 2 | 31.12 / 32 | 0.00538 / 0.0143 / 0.0418 | 9 / 32.39 / 0.0022 | 16 / 38.17 / 0.00078 | 18 / 12 / 0 | 0.51 | 20.55 | 37.55 / 0.00072 |
| **A** | 33.50 / 35 | 0.00369 / 0.0102 / 0.0325 | 12 / 34.87 / 0.00075 | 24 / 41.27 / 0.00032 | **24 / 18 / 0** | 0.15 | 28.08 | 38.72 / 0.00061 |
| A′ | **34.11** / 36 | **0.00341 / 0.0093 / 0.0304** | 12 / **35.51 / 0.00030** | 28 / 42.08 / 0.00010 | 22 / 18 / 0 | 0.09 | 30.36 | 38.78 / 0.00061 |
| **B** | 33.93 / 36 | 0.00354 / 0.0096 / 0.0317 | 12 / 35.32 / 0.00065 | 26 / 41.83 / 0.00036 | 2 / 2 / 0.00003 | 0.22 | 28.92 | 38.73 / 0.00064 |
| C | 33.32 / 35 | 0.00500 / 0.0132 / 0.0379 | 10 / 34.70 / 0.0017 | 22 / 41.11 / 0.00046 | 4 / 4 / 0 | 0.34 | 26.65 | 38.52 / 0.00067 |
| A+B | **34.11** / 36 | 0.00353 / 0.0094 / 0.0305 | 12 / 35.50 / 0.00050 | 30 / 42.09 / 0.00025 | 2 / 2 / 0.00003 | 0.09 | 30.63 | 38.67 / 0.00062 |

Merge rates for all gap classes are in `p6/merge_*.log`; per-i and (i, j) bucket tables are in `p6/dist_*.log`.

**One-pass ceiling.** A swap at `(i, j)` can change at most `52 − i` outputs, so no rule of this shape can average more than 35.33. The uniform one-pass reference from PHASE5 (everything after step `i` re-seated at random) averages 34.4. A′ and A+B reach 34.11 and B 33.93, so they are close to that reference. None exceeds it, as expected.

**The minimum is still 2, and branch analogue 4, for every variant.** This is the PHASE5 one-pass floor, proven on paper (the tail swap is also `hammingDist_gridW_swap_tail` in Lean, for any free-seat chooser): a swap of the last two positions always gives spread 2, and no tweak of the finger can change that.

## Which ones clear the bar

The bar: decryptable; worst pair ≤ 1/64; low-spread shares near rule 1's; mean spread above v10's 32.8; hand cost near rule 1's.

| | decryptable | worst ≤ 1/64 | low-spread shares vs rule 1 | mean > 32.8 | hand cost near rule 1 | verdict |
|---|---|---|---|---|---|---|
| A | yes | yes (1/170) | better on all three | 33.50 | +1 small add per step | **clears** |
| A′ | yes | yes (1/164) | best | 34.11 | a multiply mod 13 per step | clears numerically; **hand cost is not near rule 1** |
| B | yes | yes (1/205, best of the singles) | better on all three overall; loses the far-apart floor (spread-2 share 3e-5 there, against 0 for rule 1 and 0.004 for v10) | 33.93 | +1 mod-4 add per block only | **clears** |
| C | yes | yes (1/172) | about equal (0.00500 / 0.0132 / 0.0379) | 33.32 | +1 add per step | clears, but the weakest of the four; also loses most of the far-apart floor (min 4) |
| A+B | yes | yes (1/212) | better | 34.11 | A + B | clears; costs more than either single; loses the far-apart floor |

Why B and C lose the far-apart floor: in rule 1, the targets between the two swapped positions are all shifted by the same nonzero offset, which prevents spread 2 when the positions are far apart. B's nudges (and C's marker) change the finger by occupancy-dependent amounts, so that shift can be cancelled and the walk can re-merge exactly. It is rare (3 in 100 000 far-apart swaps for B), but the observed floor is gone. A and A′ only add a finger-row term to the column move, which keeps the shift and the floor.

## Walkthrough: B (blocker nudges the finger), including decryption

This is `p6/walkthrough.log` (seed 1; `python3 p6walk.py 1 16`). Seats are r(row)c(col). A card's step is +suit rows (♣0 ♥1 ♠2 ♦3) and +rank columns, mod 4 / mod 13.

```
 8 5S: f r2c1 + 3S -> target r0c4 free -> sits there; finger r0c4
 9 3D: f r0c4 + 5S -> target r2c9 TAKEN by JS; scan row t0+S=2 from col 9+11=7 -> r2c7 (1 seat checked);
       marker 0->1; NUDGE: finger = target + JS = r0c7
10 QH: f r0c7 + 3D -> target r3c10 free -> sits there; finger r3c10
...
15 4D: f r0c11 + 2C -> target r0c0 TAKEN by 8C; scan row t1+C=1 from col 0+8=8 -> r1c8 (1 seat checked);
       marker 1->2; NUDGE: finger = target + 8C = r0c8
```

Up to the nudge, step 9 is exactly rule 1:

- the blocker J♠ sends 3♦ to row marker + ♠ = 2, scanning from column 9 + J = 7;
- 3♦ sits on the first free seat, r2c7;
- the marker moves on.

The only new move is where the finger goes. Rule 1 leaves it on the target r2c9. B moves it by J♠'s step: rows +2 (r2 → r0), and columns to the same column 7 you just scanned from. So the finger lands on r0c7, and the next card (Q♥) steps from there: r0c7 + 3♦ → r3c10.

**Decryption of the same table** (same log):

```
 9 f r0c4 + 5S -> r2c9 already ticked (blocker JS): scan row 2 from col 7 over UNticked seats -> r2c7 = 3D;
   marker 0->1; finger r0c7
10 f r0c7 + 3D -> r3c10 not ticked -> card QH; finger r3c10
15 f r0c11 + 2C -> r0c0 already ticked (blocker 8C): scan row 1 from col 8 over UNticked seats -> r1c8 = 4D;
   marker 1->2; finger r0c8
```

The decryptor finds r2c9 already ticked, so a blocked placement happened here. It reads the blocker J♠ from the table and runs the same scan over unticked seats, giving r2c7 and so 3♦. It then applies the same nudge (finger r0c7) and continues. The full 52-card round trip in the script returns the original deck.

**Extra hand work compared with rule 1:** on a blocked placement, add the blocker's suit to the target row (mod 4) to get the finger's row. The finger's column is the scan-start column you already computed. Unblocked placements are unchanged. Seats checked per blocked placement: 7.03 / p90 20 / max 52 (rule 1: 7.01 / 19 / 52).

## Recommendation (proposal only; Zachary decides)

- **B ("blocker nudges the finger") is the cheapest tweak that clears the bar.** On the hand-cost criterion I'd propose it:
  - mean spread 33.93 against v10's 32.8, with low-spread shares below rule 1's;
  - worst pair 1/205, better than rule 1's 1/161;
  - its only extra work is one mod-4 add on blocked placements, using a column you already have.
  - Its cost: rule 1's far-apart floor becomes an observed "almost never" (3e-5) rather than "never seen". That is still about 140× below v10 in that slice.
- **A (row-dependent step) is the alternative if keeping the far-apart floor matters more than hand cost.** It clears the bar (mean 33.50, worst 1/170) and keeps the floor (sampled 24, climbed 18), but adds one small addition on every step.
- A′ and A+B score highest on spread (34.11) but cost more by hand. C is the weakest. Plain rule 1 remains the fallback if neither B nor A is wanted.

## Files

- `cand.c` (variants 60–64 added; ids 0/30/33 unchanged), `p3small.c` (60–64 added), `p5.c` (unchanged; includes `cand.c`).
- `p6check.py`: independent Python encryptor and decryptor, compared against `cand.c`.
- `p6walk.py`: walkthrough with decryption.
- `run_phase6.sh`: reproduces everything in `p6/`:
  - `small_injectivity.log`, `cost.log`, `check.log`, `candcheck.log`, `walkthrough.log`;
  - `full_summary.log` (raw `scr_*.txt`, `full_*_*.txt` regenerated, not committed);
  - `cyc3_*.log`, `cyc3_summary.log`;
  - `round_summary.log` (raw `round_*_*.txt` regenerated, not committed);
  - `dist_*.log`, `spcyc3_*.log`, `climbfar_*.log`, `climbsummary.log`, `merge_*.log`.
