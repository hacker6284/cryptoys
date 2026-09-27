# v10 SumRanks alone as an S-box: difference search (empirical, not a proof)

**Kind:** analysis. Monte Carlo measurements plus exact enumerations under a stated uniformity argument. Nothing here
is a theorem, a bound or a security claim. Scope: **SumRanks alone** (SPEC §3.3), **uniformly random decks**, mostly
**value (relabelling) differences**. Low-weight families are covered exhaustively, and hill-climbs were run on top.
Position differences are included for completeness.

The S-box model is `sbox.c`, a C port for speed. `verify.py` checks it against the repo's reference port
(`../../../security/checks/ddport.py`). It matches the v10 `sum_ranks` vector, all 6 v10 encrypt vectors (used as
the SumRanks inside `ddport.encrypt`) and `ddport.sum_ranks_v10` on 20,000 random grids. `repro.py` runs directly
on `ddport`. `logs/verify.log` also records `../check_cand.py` (W5c 6/6).

## Bottom line

* **Does anything beat 1/64?** Only the 51 exact symmetries (the v10Sym group: shift every rank by a, and/or
  XOR every suit label by x). They pass SumRanks with probability 1 by construction; the iff theorem says so, and
  20M/20M decks confirm it. Leave them out and **nothing reaches 1/64**. The worst difference is a **3-cycle of three
  cards of the same suit, at exactly 9/1105 ≈ 1/123**. That is 1.9× below 1/64.
* **Does anything beat the old 1/221?** **Yes: every same-suit 3-cycle (1/123, about 1.8× worse than 1/221).**
  Nothing else does. 4-cycles, double swaps, same-rank moves, suit maps on subsets, rotations, block moves and every
  position difference all come in at or below 1/221. The same-suit swap is still exactly 1/221.
* For every value difference with measurable survival, **the most common output difference was the input
  difference itself**, so the differential-probability estimate (b) equals same-difference survival (a). For the rest,
  no output difference turned up more than 4 times in 2M. For position differences,
  (b) is at most ≈ 1/1460.
* Linear-style check: no correlation above noise (max |corr| 0.004 at N = 1M; noise sd 0.001) between row/column
  suit counts, rank sums or weighted rank sums before and after.

## Definitions (which number is which)

* **Value difference** τ (a card relabelling): deck' = τ∘deck. This is the kind that passes Compose (the keyed
  step) unchanged, so it matters for the cipher. It survives with output difference τ_out when
  SumRanks(deck') = τ_out∘SumRanks(deck). τ_out is unique because the cards are distinct.
* **Position difference** π: deck'[cell] = deck[π(cell)]. Output difference π_out is defined by
  SumRanks(deck')[cell] = SumRanks(deck)[π_out(cell)].
* **(a) same-diff survival** = P[output difference = input difference]. **(b) best output diff** = the count of the most
  common output difference over N random decks (every output difference is hashed and bucketed).
* The 95% CIs are Wilson intervals. "Exact" values are computed by enumeration, not sampling (`exact.py`).

## Ranked table (20M random decks per row, `final.py` → `logs/final_table.md`)

| # | difference | class | (a) same-diff survival: hits / 20M, 95% CI | exact | (b) best output diff | vs 1/64 | vs 1/221 |
|---|---|---|---|---|---|---|---|
| 1 | rank+1 on every card (any of the 51 v10Sym elements) | exact symmetry (proved) | 20,000,000 (= 1) | 1 | 1 (= input) | above | above |
| 2 | **3-cycle of three same-suit cards**, e.g. A♣→2♣→3♣ | same-suit 3-cycle | 162,525 = 1/123 [0.00809, 0.00817] | **9/1105 = 1/122.8** | same (= input) | below (1.9×) | **above (1.8×)** |
| 3 | same-suit swap, e.g. 2♣↔7♣ (old worst) | swap | 90,072 = 1/222 [0.00447, 0.00453] | 1/221 | same | below | equal |
| 4 | same-suit 4-cycle A♣→2♣→3♣→4♣ | 4-cycle | 55,888 = 1/358 | 761/270725 = 1/356 | same | below | below |
| 5 | two swaps of same-suit pairs, unequal rank gaps, e.g. (A♣ 2♣)(A♥ 3♥) | double swap | 51,205 = 1/391 | 691/270725 = 1/392 | same | below | below |
| 6 | two swaps with *equal* gaps (the "cancelling" design), e.g. (A♣ 2♣)(5♣ 6♣) | double swap | (2M run: 4,624 / 2M) | 621/270725 = 1/436 | same | below | below |
| 7 | 3-cycle of three same-rank cards, e.g. 2♣→2♥→2♠ | same-rank 3-cycle | 23,698 = 1/844 | 1/850 | same | below | below |
| 8 | GF(4) suit map on one rank (2♣↔2♦, 2♥↔2♠) | subset relabelling | 2,898 = 1/6901 | 3/20825 = 1/6942 | same | below | below |
| 9 | position swap of cells (1,2)↔(3,6) (best position swap) | position | 0 | – | 13,673 = 1/1463 (a different output diff) | below | below |
| 10 | position swap of cells (0,0)↔(1,0) | position | 6,859 = 1/2916 | – | 7,030 = 1/2845 | below | below |
| 11 | rotate every row left by 1 | position | 1,672 = 1/11962 | – | 1,744 | below | below |

Other results, all well below 1/221 (2M decks each, `logs/battery_2M.log`): rank shift within one suit (13-cycle)
6.6e-5. Rank shift on two suits 3.4e-5. Global rank ×2 or rank negation ≈ 4e-5. Global label ×w or a global swap of
two suits: 0 in 2M. The label map on 2 or 6 ranks: ≤ 1e-6. Mixed-suit/rank swaps and 3-cycles: ≤ 2.6e-5. Position
3-cycles in a row, a column or across both: ≤ 5.5e-6 same / ≤ 1.3e-5 best-out. Single-row and single-column rotations:
≤ 8.7e-5 (best-out, rotating row 0). All-column rotation, row swap, column swap and block move: ≤ 4.5e-6. A same-suit
6-cycle: 6.5e-4.

Exhaustive scans. Survival does not change when you compose with a symmetry or conjugate by one, and the
symmetries move any card to A♣, so each scan covers its whole family:
* all value 3-cycles (2550 reps at 200k decks each): the 132 above 1/221 are exactly the same-suit 3-cycles.
  Nothing else is above 1/221, and nothing is above 1/64 (`logs/scan_c3.log`)
* all value double swaps (62,475 reps at 20k decks each): nothing is above 1/221 (`logs/scan_ds.log`). Exact values
  for all 21 same-suit gap classes are in `logs/exact_ds.log`: 1/392 or 1/436.
* all 1326 position swaps (200k decks each, best-out ≤ 8.5e-4) and all 44,200 position 3-cycles (10k decks each,
  best-out ≤ 4/10k) (`logs/scan_pt.log`, `logs/scan_pc3.log`)
* hill-climb over value permutations moving ≤ 8 cards (64 climbs × 1000 steps). Every climb that got anywhere
  landed on a same-suit 3-cycle. Position hill-climb (≤ 6 cells) topped out at position swaps ≤ 9e-4
  (`logs/hill_V.log`, `logs/hill_P.log`).

## Mechanism (plain words)

SumRanks reads 17 totals: 4 row totals and 13 column totals. **Row totals see only ranks**: the sum of
(13 − k)·rank along the row. **Column totals see only suits**: the GF(4)-weighted suit value of the previous column
XOR the column's own suit XOR. A value difference passes exactly when none of the 17 totals it reads changes. When
that happens every card lands in the same place, so the output difference is the input difference. When a total does
change, cards land in deck-dependent places and the output difference scatters. That is why (b) = (a) in
practice.

1. **Symmetries (probability 1).** Add the same amount to every rank and every full row total moves by
   a·(13+12+…+1) = 91a ≡ 0 mod 13. XOR the same x into every suit label and every column total moves by
   x·(0 ⊕ 1 ⊕ w ⊕ w²) ⊕ (x⊕x⊕x⊕x) = 0. These are the only changes invisible on every deck (proved:
   `sumRanksV10_commutes_iff`). They "beat" 1/64 by design, and SumRanks alone does nothing about them. Through a whole
   round (GridCycle included), 0 of 1M decks survive (`logs/round_check.log`).
2. **Same-suit 3-cycle (1/123, the real worst).** Suits don't change, so all 13 column totals are blind to it. Only
   the rows can notice. Each row that holds a moved card gives one equation mod 13: sum of (13−k)·(rank change) = 0.
   * A lone moved card in a row passes only if it sits in column 0, where the weight 13 ≡ 0 (1 in 13).
   * A swap in one row can never balance: its two changes are +d and −d at different weights.
   * Three cards in one row can balance. Their changes add to 0, and 1 in 11 placements cancels.
   
   So the 3-cycle is the sweet spot:
   * all three in one row, balanced: 12/2550 ≈ 0.0047
   * two in a row balanced, with the third in some row's column 0: ≈ 0.0033
   * all three in column 0: ≈ 0.0002
   
   Total: 9/1105. Moving more cards adds equations and lowers the rate (4-cycle 1/356, double swaps 1/392 to 1/436).
   The "balanced" double swaps with equal gaps are the *worst* of the double swaps at 1/436, because a fixed
   difference can't choose where its cards land.
3. **Suit-side differences are weaker.** A single suit change in a column always shows in that column's own suit
   XOR. Cancelling it needs a matching card in a set row of the neighbouring column, or all four cards of a rank in
   one column. So same-rank moves top out at 1/850.
4. **Position differences** get smeared by the rank-driven row turns, so no output difference concentrates. The
   best is ≈ 1/1460.

**Minimal reproducer** (`repro.py`, uses the repo's reference Python port, not `sbox.c`). Put A♣, 3♣, 2♣ in row 0,
columns 1, 2, 3 (deck positions 4, 8, 12, column-major) and fill the rest at random. Then the difference
A♣→2♣→3♣ passes SumRanks **every time** (2000/2000). Row 1's turn moves by 12·(+1) + 11·(−2) + 10·(+1) = 0, and no
suit changed. Over fully random decks the rate is 9/1105. rank+1 on every card passes 2000/2000.

## Context: a whole round, not SumRanks alone (`round_check.py`, 1M decks, uses `../cand.c`)

The unkeyed round is SumRanks, then ShiftRows, then GridCycle. Relabellings commute with Compose.

| difference | whole-round survival |
|---|---|
| v10Sym elements | 0 / 1M |
| same-suit 3-cycles | 43 to 83 / 1M (≈ 1/15,000) |
| same-suit swap 2♣↔7♣ | 483 / 1M (≈ 1/2,070, the per-round worst of these) |
| K♣↔K♦ | 0 |

## Caveats / not covered

* The parity comparison is loose. The AES S-box works on bytes with 255 XOR differences. Here the difference space
  is all permutations of 52 cards, and SumRanks has 51 exact symmetries by design. By a literal reading of the
  per-layer rule, SumRanks alone fails on those. By itself it can't approach an S-box on them, and it relies on
  GridCycle to break them.
* Only permutation differences: low-weight families exhaustively (value 3-cycles and double swaps, position swaps
  and 3-cycles), plus hand-built structured ones (global and subset suit maps, rank maps, row/column rotations,
  block moves) and hill-climbs (≤ 8 value / ≤ 6 position cells). A high-weight difference outside these families
  could in principle do better. The algebra above argues against it heuristically: each extra card adds an equation.
* (b) is the most common output difference among N samples. It can only see output differences with probability of
  roughly 10/N or more. The position 3-cycle scan used 10k decks, so it resolves only ≳ 1e-3.
* The exact values rest on one argument: each grid SumRanks reads from is a bijective image of the input, so it is
  uniform when the input is. That holds only when positions are random. In the cipher, the key-dependent Compose before SumRanks
  is what this random-deck model stands in for. With a chosen, unwhitened input you could always place cards so a difference passes.
* One layer, one round. No multi-round trails, keyed effects or key schedule. The linear check covers only simple
  count features.

## Files

`sbox.c` / `sb.py` (C S-box, survey, ctypes wrapper). `verify.py` (model checks). `battery.py` (analytic
candidates). `scan.py` (exhaustive scans). `hillclimb.py`. `exact.py`, `exact_ds.py` (exact probabilities).
`final.py` (the 20M table). `linear.py`. `round_check.py` (uses `../cport.py` / `../cand.c`). `repro.py`. `logs/`
(all outputs). Needs numpy and gcc. `sb.py` compiles `build/libsbox.so` (gitignored) on first import. Every
run uses fixed seeds, so rerunning reproduces the logs. Run times on 8 cores: `battery.py` ~2 min, `final.py`
~3 min, `scan.py ds` ~5 min. Run with `PYTHONDONTWRITEBYTECODE=1` to keep `__pycache__` out of the tree.
