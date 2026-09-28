# Phase 5: diffusion ("branch-number-style spread") of GridCycle alone

Analysis only. No change to the spec or to `main`; the choice of rule is Zachary's. Heavy runs are
outside CI (`run_phase5.sh`, about 5 minutes on 12 cores). No bit-security claims.

Rules compared (the same code as Phase 2, `cand.c`; v10 there is checked against `gc.h`):

- **v10**: finger moves to where the card landed; overflow uses the marker row.
- **rule 1** (id 33): ghost finger, and the blocker sends you. Row = marker + suit(blocker), start column = T.col + rank(blocker), first free seat to the right, drop a row if full, marker +1.
- **rule 2** (id 30): ghost finger, row = marker + suit(blocker), scan starts at the target column.

## Metric

AES MixColumns is linear, so its strength is measured by diffusion: branch number 5, i.e. active input bytes + active output bytes ≥ 5. GridCycle is a permutation of 52 card positions, so the natural small input change is a **transposition**. Take a deck `d`, swap walk positions `i < j` to get `d'`, and count

    spread(d, i, j) = #{ k in 0..51 : GC(d)[k] != GC(d')[k] }

Here `k` is the output index: seat = row·13 + col, row-major, which is the spec's output order. The input has 2 active positions, so the branch-number analogue is `2 + min spread`.

Two facts hold for any permutation layer:

- **spread ≥ 2 always.** Two different arrangements of the same 52 cards can't differ in fewer than 2 positions.
- **spread = 2 exactly when the swap "survives".** Spread 2 means the walk is unchanged and the two cards simply trade seats, which is the Phase 1/2 survival event `GC(τd) = τGC(d)`. So spread 0 never happens; **the survival case is spread = 2**, not 0.

The logs also record the "excess" (positions where `GC(d')` differs from `τGC(d)`). It is 0 exactly in the survival cases, and it reproduces the survival frequencies: rule 1 gives 0.00506 against Phase 2's mean pair survival of 0.0051, and v10 gives 0.0435 against Phase 1's 0.0434.

## Headline table

All 1326 swaps of each of 20 000 random decks (26.5 M cases per rule). Minima from random sampling and hill-climbing are **upper bounds** on the true minimum.

| | v10 | rule 1 (33) | rule 2 (30) | ideal random layer |
|---|---|---|---|---|
| **min spread** (branch analogue 2 + min) | **2** (4), proven, e.g. swap (50,51) | **2** (4), proven | **2** (4), proven | 42 observed in 2 M samples |
| p1 / p10 / median | 2 / 12 / 35 | 4 / 14 / 32 | 4 / 14 / 32 | 48 / 50 / 51 |
| mean | **32.76** | 31.33 | 31.12 | 51.00 |
| P(spread = 2) = survival | 0.0435 | **0.00506** | 0.00538 | ≈ 0 |
| P(spread ≤ 4) | 0.0535 | **0.0137** | 0.0143 | 0 |
| P(spread ≤ 8) | 0.0756 | **0.0406** | 0.0418 | 0 |
| **swaps with i < 40**: p1 / mean / P(=2) / P(≤4) | 2 / 34.21 / 0.0239 / 0.0280 | 9 / 32.61 / 0.00041 / 0.0018 | 9 / 32.39 / 0.00047 / 0.0022 | |
| **swaps with i < 20**: p1 / mean / P(=2) / P(≤4) | 17 / 41.24 / 0.0032 / 0.0038 | 17 / 38.46 / 0.00002 / 0.00051 | 16 / 38.17 / 0.00002 / 0.00078 | |
| i < 20 and gap j−i > 16: sampled min / p1 / mean | **2** / 21 / 42.34 | **22** / 31 / 42.19 | **18** / 31 / 42.05 | |
| same, targeted hill-climb min (upper bound) | 2 | **16** | **12** | |
| i < 40 and gap ≤ 4: p1 / mean / P(≤4) | 2 / 27.51 / 0.032 | 4 / 20.98 / 0.014 | 4 / 20.55 / 0.017 | |
| 3-cycles of positions (2 M random): min / p1 / mean / P(≤4) | 2 / 5 / 38.16 / 0.0088 | 2 / 11 / 37.68 / 0.00071 | 2 / 11 / 37.55 / 0.00072 | |

A single 3-cycle can also reach spread 2: one of the three moved cards happens to land on the same seat in both walks.

Hill-climbing for low spread among swaps with small `i` (`p5/climbsummary.log`, 8 restarts × 20 000 moves) found:

- **v10:** spread 2 for i < 1, < 3, < 5, < 10.
- **rule 1:** 3 for i < 1, < 3, < 5; 2 for i < 10.
- **rule 2:** 3 for i < 1; 2 for i < 3.

Random sampling had already found spread 2 for rule 1 at i = 1 and i = 3. So all three rules reach spread 2 from almost the very first position; for rule 1 and rule 2 it is roughly one case in 10⁵.

## How spread depends on the positions (the one-pass floor)

Mean spread by the first swapped position `i` (averaged over j > i), with the sampled minimum:

| i | v10 min / mean | rule 1 min / mean | rule 2 min / mean | ideal one-pass layer mean |
|---|---|---|---|---|
| 0 | 2 / 49.79 | 3 / 45.77 | 3 / 45.34 | 51.01 |
| 5 | 2 / 45.06 | 2 / 41.65 | 2 / 41.31 | 46.01 |
| 10 | 2 / 40.03 | 2 / 37.42 | 2 / 37.16 | 41.03 |
| 20 | 2 / 29.50 | 2 / 28.66 | 2 / 28.49 | 31.03 |
| 30 | 2 / 18.37 | 2 / 19.49 | 2 / 19.39 | 21.05 |
| 40 | 2 / 7.50 | 2 / 9.94 | 2 / 9.89 | 11.08 |
| 45 | 2 / 3.76 | 2 / 5.31 | 2 / 5.28 | 6.16 |
| 49 | 2 / 2.15 | 2 / 2.33 | 2 / 2.33 | 2.50 |
| 50 | 2 / 2.00 | 2 / 2.00 | 2 / 2.00 | 2.00 |

The "ideal one-pass layer" is a reference with the same one-pass structure: steps 0..i keep their seats, and every later card gets an independent uniform seat among the seats left. Averaged over all 1326 swaps it gives 34.4. That is the ceiling for any rule of this shape: v10 reaches 32.8, rule 1 31.3 and rule 2 31.1. A fully random layer would give 51.0.

The full 13×13 table of (i, j) buckets (min / mean) is in `p5/dist_*.log`. For the ghost-finger rules the spread depends mainly on the **gap** `j − i`, not only on `i`. For v10 it depends on `i` and hardly on `j`.

## What can be proven

1. **All three rules: min spread = 2 exactly, so the branch analogue is exactly 4, and no one-pass walk can do better.**
   - The seat of step `k` is determined by `d[0..k-1]`, so a swap at `(i, j)` leaves steps `0..i` on their seats; only steps `i..51` can change. That caps spread at `52 − i`.
   - For `(i, j) = (50, 51)`, step 50's seat is fixed and step 51 takes the only seat left. The walk is identical, and spread = 2 for **every** deck under every rule of this family (measured: 1.00000 for all three).
   - So the MixColumns-style minimum can't separate the rules. Only the distribution can. This is the Phase 2 "last positions" floor, now proven rather than measured.
2. **A swap always changes at least the two swapped cards' placements.**
   - Seat `seat[i]` holds `d[i]` in one output and `d[j]` in the other.
   - The card `d[i]` sits somewhere else in the second output, and that position held something else in the first.
   - That is the bound `≥ 2`. No bound above 2 holds for every swap: spread-2 witnesses exist even at i = 1 (rule 1) and i = 0 (v10).
3. **Ghost-finger rules (1 and 2): targets re-synchronise after the second swapped position.**
   - With the ghost finger, target `T_k = start + Σ_{m<k} step(d[m])`, independent of occupancy. A sum doesn't depend on order, so for every `k > j` the two walks aim at **the same target**.
   - For `i < k ≤ j` the targets differ by the fixed offset `Δ = step(d[j]) − step(d[i])`. `Δ ≠ 0` because `(suit, rank mod 13)` is a bijection from the 52 cards onto Z₄ × Z₁₃.
   - So after `j` the walks can differ only through which seats are occupied (and the marker), and they often merge back. Measured (`p5/merge.log`): fraction of steps after `j` that land on the same seat in both walks, for swaps with i < 40 and j < 50:

     | | gap 1 | gap 2–4 | gap 5–16 | gap > 16 |
     |---|---|---|---|---|
     | v10 | 0.28 | 0.13 | 0.07 | 0.04 |
     | rule 1 | 0.49 | 0.36 | 0.22 | 0.09 |
     | rule 2 | 0.51 | 0.37 | 0.24 | 0.10 |

   - This explains both sides of the ghost finger's profile:
     - **Weak at close swaps.** An adjacent swap moves only one target, and the walks re-merge half the time. Mean spread at gap ≤ 4 is 21.0 for rule 1 against 27.5 for v10.
     - **Weak early on average.** The mean at i = 10 is 37.4 against v10's 40.0.
     - **Strong at far swaps.** Every target in between is shifted, so spread-2 cases vanish. For i < 20 and gap > 16: sampled min 22 (rule 1) and 18 (rule 2) against 2 for v10; targeted search reached 16 and 12. These are observed floors, **not** proven bounds.
   - I don't have a proof of any bound above 2 for the far-gap region.

## Verdict (proposal only)

**Rule 1 against rule 2.** Rule 1 is at least as good as rule 2 on every diffusion statistic here:

- mean higher at every first position `i` (by 0 to 0.43);
- fewer cases at spread = 2, ≤ 4 and ≤ 8 overall and in every restricted slice;
- higher sampled and hill-climbed far-gap minimum (22 / 16 against 18 / 12);
- 3-cycles essentially equal.

The only places rule 1 shows a lower number are noise-level:

- sampled minimum 2 against 3 at i = 1 and i = 3, where rule 2 also reaches 2 under hill-climbing at i < 3;
- a spread-2 frequency 1e-5 higher at three single positions, a handful of cases each.

**No diffusion measure found here where rule 1 is worse than rule 2.**

**Both ghost rules against v10.** The trade is real:

- **v10 better:** higher mean spread for early swaps (i < ~25) and at small gaps, and a higher overall mean and median (32.8 / 35 against 31.3 / 32).
- **Ghost rules better:** far fewer tiny-spread cases (spread = 2 falls from 4.3% to 0.5%, ≤ 4 from 5.3% to 1.4%), a far-gap floor where v10 has none, and better late swaps (i > ~25).

The ghost finger's order-invariant targets are the cause of both sides. On a MixColumns-style "worst case" view, the ghost rules are better. On an "average spread" view, v10 is slightly better.

**Branch-number analogue.** It is exactly 4 (2 in + 2 out) for every rule of this one-pass family, provably, and no rule of this shape can separate itself on that minimum. MixColumns reaches 5, the maximum for its 4-byte columns. Nothing here corresponds to an MDS guarantee.

## Files

- `p5.c` (binary `p5sim`), modes:
  - `dist`: histograms, per-i, per-(i,j) buckets, restricted slices;
  - `climb`: hill-climb over decks, optional minimum gap;
  - `cyc3`: 3-cycles;
  - `merge`: re-synchronisation after `j`;
  - `ideal`: random and one-pass reference layers;
  - `x`: dump for cross-check.
- `p5check.py`: independent Python implementation of v10, rule 1 and rule 2 from the rule text. All 1326 spreads of 20 decks per rule are identical to `p5sim` (`p5/check.log`).
- `run_phase5.sh`: reproduces every log in `p5/`:
  - `dist_{0,33,30}.log`
  - `cyc3_*.log`
  - `climb_*_k*.log`, `climbfar_*.log`, `climbsummary.log` (decks for every hill-climb result)
  - `merge.log`
  - `ideal.log`
  - `check.log`
