# Phase 4 — "C sends itself" (Zachary's curiosity variant)

Analysis only. No change to the spec or to `main`; any algorithm change is Zachary's decision.
Heavy checks run outside CI (`run_phase4.sh`, about 40 s). No bit-security claims.

## The variants

All four keep everything from rule 1 (Phase 2, cand id 33) except the scan used when the target is taken.
Card `c`: suit `c/13` (♣ 0, ♥ 1, ♠ 2, ♦ 3), rank `c%13+1`. `T` = target, `C` = card being placed, `B` = blocker already on `T`, `t` = marker.

| id | finger for the next step | blocked C: scan row | scan start column |
|---|---|---|---|
| rule 1 (33) | ghost (stays on T) | t + suit(**B**) | T.col + rank(**B**) |
| **50** (asked) | ghost (stays on T) | t + suit(**C**) | T.col + rank(**C**) |
| 51 | where C landed (no ghost) | t + suit(C) | T.col + rank(C) |
| 52 | ghost | t + suit(C) | T.col + rank(B) |
| 53 | ghost | t + suit(B) | T.col + rank(C) |

In every case the scan takes the first empty seat to the right (wrapping within the row), drops to the next row if the row is full, and then the marker moves on by one suit.

**How 50 differs from rule 1, in plain words.** In rule 1 the card that's already sitting on the target says where the newcomer goes. In 50 the newcomer picks its own seat from its own suit and rank. The rest of the walk doesn't change: same ghost finger, same next step by C, same marker.

## Verdict: all four variants are non-invertible (information is lost)

Step 2 (strength measurements) therefore doesn't apply, and no strength numbers are reported for 50–53.

### Why (the argument)

For a blocked placement in rule 1, the decryptor already knows everything the scan depends on: `T` (from the walk so far), the marker, and the blocker `B` (it's on `T` in the table). So it can re-run the scan, land on exactly one seat, and read C from that seat. Every step is forced, which makes the map a bijection. Phases 1–3 checked this exhaustively on small grids.

In 50–53 the scan depends on C, and the decryptor doesn't know C yet. The most it can do is test each unvisited seat `s`: "if the card on `s` had been placed here, would its own scan have taken it to `s`?" Call that condition `s = scan(t + suit(G[s]), T.col + rank(G[s]))`. It is a fixed-point condition, and nothing forces it to have only one solution. Often two or more unvisited cards each satisfy it. If only one of them led to a valid walk, the decryptor could still manage by backtracking. The witnesses below show that this isn't what happens: two different decks can give exactly the same table, so no decryptor, however clever, can tell them apart.

The traced 52-card witness (`p4/trace.log`, checked independently in Python) shows the mechanism.

Variant 50: deck A and deck B differ only by swapping 4♠ (walk position 39) and 4♣ (walk position 43).
```
deck A                                                        deck B
39 4S target (1,12) blk JH; row 1 from col 3 -> (1,5)          39 4C target (1,12) blk JH; row 3 from col 3 -> (3,5)
40 5S target (3,3)  blk QH; row 2 from col 8 -> (2,8)          40 5S target (1,3)  blk 8D; row 2 from col 8 -> (2,8)
41 AS target (1,8)  blk 9H; row 3 from col 9 -> (3,10)         41 AS target (3,8)  blk TD; row 3 from col 9 -> (3,10)
42 3H target (3,9)  blk 7S; row 3 from col 12 -> (3,0)         42 3H target (1,9)  blk KD; row 3 from col 12 -> (3,0)
43 4C target (0,12) blk TS; row 3 from col 3 -> (3,5)          43 4S target (2,12) blk 4H; row 1 from col 3 -> (1,5)
44 6H target (0,3)  free                                       44 6H target (0,3)  free
```
The two 4s have the same rank, so they move the finger by the same number of columns. All the targets from step 40 to step 43 therefore have the same columns in both decks; only the rows differ. Each of those targets is blocked in both decks, and a blocked card's seat depends only on the marker, its own suit, its own rank and `T.col`. The blocker and `T.row` don't enter. So in both decks each card lands on the same seat. At the end, 4♠ is on (1,5) and 4♣ on (3,5) in both decks, and from step 44 on the walks are identical. The suit difference between the two 4s only changed target rows, and the self-scan then threw that difference away.

A second witness type is the endgame: swapping the last two cards. At step 50 there are two empty seats, and each of the two cards' own scans takes it to a different one of them. The 51st card then fills whatever seat is left over. Rule 1 avoids this case because the blocker, not the card, chooses the seat.

### Evidence

**Small-grid exhaustive check** (`p3small.c`, extended with 50–53; R×C grid, card suit = c/C, rank = c%C+1). Values are distinct outputs out of n! decks:

| grid (n!) | v10 (0) | rule 1 (33) | 50 | 51 | 52 | 53 |
|---|---|---|---|---|---|---|
| 2×3 (720) | 720 | 720 | 450 | 452 | 511 | 520 |
| 3×2 (720) | 720 | 720 | 465 | 435 | 503 | 574 |
| 2×4 (40320) | 40320 | 40320 | 20382 | 20525 | 26081 | 24608 |
| 4×2 (40320) | 40320 | 40320 | 21716 | 20419 | 23605 | 30476 |
| 3×3 (362880) | 362880 | 362880 | 167985 | 167773 | 200067 | 222418 |

v10 and rule 1 are injective on every grid. 50–53 are non-injective on every grid, with roughly half the decks colliding; explicit colliding pairs are in `p4/small_injectivity.log`.

**Full-size one-swap collisions** (`p4sim V collide 2000 7`: all 1326 swaps of each of 2000 random decks). Every stored witness is re-checked by the independent Python code in `p4trace.py`: 14/14 confirmed.

| variant | collisions / 2.65M swaps | decks with a colliding one-swap neighbour | same, restricted to swaps at walk positions < 48 |
|---|---|---|---|
| 50 | 1980 | 67.5% | 14.6% |
| 51 | 2395 | 72.2% | 27.6% |
| 52 | 787 | 33.6% | 4.7% |
| 53 | 1341 | 49.2% | 16.2% |

For comparison, Phase 3's bump variants were at 19–24%.

**Best decryptor: exhaustive depth-first search** (`p4sim V decrypt`).
- At a free target the card on `T` is forced.
- At a blocked target it tries every unvisited seat whose card would self-scan onto that seat.
- This search is complete: it finds every deck that produces the given table.

On 100k decks, searching for up to 2 solutions:

| variant | tables with a unique preimage (recovered) | tables with ≥ 2 preimages | candidates per blocked step on the true path |
|---|---|---|---|
| 50 | 0.41% (all recovered) | **99.59%** | 1.83 |
| 51 | 0.27% | 99.73% | 1.83 |
| 52 | 1.03% | 98.97% | 1.62 |
| 53 | 0.88% | 99.12% | 1.69 |

Full preimage counts on 10k decks (search not capped; `p4/count_summary.log`), i.e. how many decks share one table:

| variant | median | p90 | max | geometric mean |
|---|---|---|---|---|
| 50 | 37 | 143 | 2322 | 35 |
| 51 | 116 | 1032 | 85817 | 120 |
| 52 | 19 | 57 | 318 | 18 |
| 53 | 18 | 53 | 435 | 17 |

**Table feasibility.** Trying candidates by hand isn't the obstacle:
- a blocked step has about 1.8 self-consistent candidates on average;
- the full search averages about 140 nodes per deck.

The obstacle is that the search ends with dozens of equally valid decks (median 37 for variant 50), and nothing in the table picks out the right one. No amount of decryptor effort fixes that.

The mixed variants 52 and 53 leak less, because half of the scan still comes from the known blocker, but they are still non-injective on every small grid and on about 99% of full tables. Dropping the ghost finger (51) makes it worse.

## Comparison

| rule | invertible | worst value-pair survival (bar ≤ 1/64) | pairs > 1/64 | 3-cycle max | full-round worst | seats checked per blocked placement (mean / p90 / max) |
|---|---|---|---|---|---|---|
| v10 GC | yes | 0.262 (K♣↔K♦) | 1311 / 1326 | 0.086 | 1.4e-3 | 6.05 / 15 / 52 |
| rule 1 (33) | yes | 0.0062 [0.0059, 0.0066] ≈ 1/161 | 0 | 2.4e-4 | 1.0e-4 | 7.0 / 20 / 52 |
| rule 2 (30) | yes | 0.0119 [0.0114, 0.0124] ≈ 1/84 | 0 | 8.6e-4 | 1.6e-4 | 7.0 / 19 / 52 |
| **50** C sends itself | **no**: 99.6% of tables have ≥ 2 preimages (median 37) | n/a | n/a | n/a | n/a | n/a |
| 51 (no ghost) | no: 99.7% (median 116) | n/a | n/a | n/a | n/a | n/a |
| 52 (row C, col B) | no: 99.0% (median 19) | n/a | n/a | n/a | n/a | n/a |
| 53 (row B, col C) | no: 99.1% (median 18) | n/a | n/a | n/a | n/a | n/a |

Rows for v10, rule 1 and rule 2 are copied from README/PHASE2.

**Scan column vs next target column.** In variant 50 the scan's start column `T.col + rank(C)` is exactly the next target's column, because the ghost finger stays on `T` and the next step moves it by rank(C). So a blocked card tends to sit in the same column as the next target, just in a different row. Strength wasn't measured because the variant isn't a permutation, so this report doesn't quantify how much that correlation shows up. The witness above does show the same structure feeding the information loss: the scan never looks at `T.row`, so whatever sets target rows (the suit of the previous card) can be erased.

## Recommendation (proposal only)

Keep rule 1 ("blocker sends you") as the Phase 2 candidate. Rule 1 is invertible precisely because the seat is chosen by something the decryptor can already see. Any variant that lets the incoming card choose its own seat breaks this, whether it controls the row, the column or both.

## Files

- `p3small.c`: small-grid exhaustive injectivity; variants 50–53 added.
- `p4.c` (binary `p4sim`): 52-card variants; `collide` and `decrypt` modes.
- `p4trace.py`: independent Python re-implementation; re-checks all witnesses and prints the traces.
- `run_phase4.sh`: reproduces everything into `p4/`.
- `p4/`:
  - `small_injectivity.log`
  - `collide_5{0..3}.log`
  - `trace.log`
  - `decrypt.log`
  - `count5{0..3}.log` (regenerated by `run_phase4.sh`, not committed; summarised in `count_summary.log`)
  - `count_summary.log`
