# DoubleDeal v10 GridCycle, Phase 2: a cheap overflow rule under the 1/64 bar (analysis only)

**Kind:** analysis and proposals. Nothing here changes the spec or `main`; the algorithm decision is
Zachary's. No bit-security claims. Metric and methodology as in [README.md](README.md) (Phase 1):
worst-case single-swap (value-pair) survival of GridCycle alone, `s(τ) = P_d[GC(τd) = τGC(d)]`,
uniform decks, 95% Wilson intervals. The bar is ≤ 1/64 = 0.0156.

Tool: `cand.c` (one C file; each candidate is a "chooser" that picks the next seat from things the
inverse also knows). `candcheck.py` checks its v10 GridCycle and v10 stem (SumRanks + ShiftRows)
against the repo port `ddport` (2000 decks, 0 mismatches). Screens use 3000 decks per pair; the
finalists got 200 000 decks per pair, all 44 200 3-cycles at 4000 decks (top 10 refined at 200 000),
one v10 round at 400 000 decks per same-suit pair, and a 100 000-deck decrypt round trip.

## Result in one line

Two small changes, both only on a **blocked** placement (a free target is handled exactly as in
v10), bring the worst pair from **0.262 to 0.0062 (1/161)** at **+16% seat checks** (7.0 vs 6.05
per blocked placement) and two small additions per blocked placement:

1. **Finger stays on the target ("ghost finger").** The next step starts from the target seat,
   even when the card had to sit elsewhere.
2. **The blocker sends you.** The card already sitting on the target (the *blocker*) picks the
   scan: row = marker + blocker's suit, start column = target column + blocker's rank; take the
   first free seat to the right; advance the marker.

## Shortlist (ranked)

| rank | candidate (cand.c id) | worst pair, 95% CI | pairs > 1/64 | worst 3-cycle | worst full round (v10 SumRanks) | seats checked per blocked placement: mean / p90 / p99 / max | extra mental work per blocked placement | round trip (100k) |
|---|---|---|---|---|---|---|---|---|
| **1** | **ghost finger + blocker sends you** (33) | **0.0062** (2♣↔K♣) [0.0059, 0.0066] ≈ 1/161 | **0** | screen max 0.0018; refined max 2.4e-4 (3♠ 6♠ 7♠) | **1.0e-4** [7.6e-5, 1.4e-4] | 7.0 / 20 / 45 / 52 | read blocker; row +suit (mod 4), column +rank (mod 13) | 0 failures |
| 2 | ghost finger + blocker picks the row (30) | 0.0119 (K♣↔K♠) [0.0114, 0.0124] ≈ 1/84 | 0 | screen max 0.0022; refined max 8.6e-4 (4♥ 4♦ 4♠) | 1.6e-4 [1.3e-4, 2.1e-4] | 7.0 / 19 / 45 / 52 | read blocker; row +suit (mod 4) only | 0 failures |
| 3 | ghost finger + hop by the blocker's step, then scan (31) | 0.0073 (A♣↔K♣) [0.0069, 0.0077] ≈ 1/137 | 0 | screen max 0.0075 at N=400 (refined ≤ 2e-4) | 1.0e-4 [7.6e-5, 1.4e-4] | 7.7 / 20 / 46 / 53 | read blocker, full step, check, then scan | 0 failures |
| ref | v10 | 0.262 (K♣↔K♦) | 1311 | 0.086 | 1.40e-3 | 6.05 / 15 / 47 / 52 | none | 0 failures |
| ref | Phase-1 option C (7) | 0.0137 | 0 | – | 3.0e-4 | 47.8 / 63+ / 63+ / 676 | count up to 13 free seats | 0 failures |

(Worst pairs and pair counts: 200 000 decks per pair. Round: 400 000 decks per same-suit pair,
the only pairs v10 SumRanks lets through; the worst of 312 pairs with ~40 hits carries some
upward selection bias. "Seats checked" = seats looked at during the scan, the same proxy as Phase 1;
the normal step is unchanged and not counted.)

Survival across all pairs for #1 is almost flat: every one of the 1326 pairs lies in
[0.0045, 0.0062] (mean 0.0051). Pairs containing K♣ are slightly higher (mean 0.0057, max 0.0062)
because K♣'s zero step always blocks; this does not need its own fix.

3-cycles (`p2/cyc3b_*.log`): all 44 200 3-cycles at 4000 decks each, then the screen's top 10 at
200 000. #1: mean 0.0002, screen max 0.0018 (7 hits in 4000), refined max 2.4e-4. #2: screen max 0.0022,
refined max 8.6e-4 (same-rank 3-cycles, e.g. 4♥ 4♦ 4♠). A 3-cycle at the 1/64 bar would show about 62
hits in 4000 decks, so none is anywhere near it. (#3 had only the coarse 400-deck screen.)

## Why it works (and where the rest comes from)

In v10 a swapped pair re-synchronises: once both walks put the next card on the same seat, they
are identical again, and late in the walk a scan from nearby columns nearly always lands on the
same seat. So survival hardly decays with the distance between the two swapped cards
(`p2/gap_0.log`: 0.115 at gap 1, still 0.070 at gap 8).

With the ghost finger, the two walks' fingers differ by `step(a) − step(b)` (never zero for
distinct cards) for **every** placement between the two swapped cards, and only re-align after
both have been placed. Each of those placements must coincide by luck; the blocker (a different
card in the two walks) scatters the scan so the luck is rare. Survival now decays geometrically
with the gap (`p2/gap_33.log`: 0.081, 0.032, 0.013, 0.005, …), and 71% of what is left comes from
the last four walk positions, i.e. the one-pass floor region (`(50, 51)` still always survives;
every pair ≥ 1/1326). The ghost alone is not enough (id 20: worst 1/20), nor is the blocker alone
(id 35, no ghost: worst 1/55, mean 0.010); together they give 1/161.

## Everything screened (3000 decks per pair, `p2/screen_summary.log`)

| id | idea | worst (screen) | pairs > 1/64 | mean |
|---|---|---|---|---|
| 0 | v10 | 0.264 | 1302 | 0.044 |
| 20 | ghost finger only (idea 2: change where the normal step starts) | 0.051 | 436 | 0.015 |
| 21 | ghost + scan the target's own row, no marker | 0.085 | 197 | 0.010 |
| 22 | ghost + option A (row = marker + suit of the placed card) (idea 4) | 0.033 | 84 | 0.006 |
| 23 | ghost + one hop by the blocker's step, then v10 scan | 0.019 | 51 | 0.012 |
| 24 | hop, no ghost | 0.070 | 1326 | 0.037 |
| 25 | ghost + up to two hops, then v10 scan | 0.019 | 57 | 0.012 |
| 26 | ghost + hop, then row = marker + suit of placed card | 0.018 | 9 | 0.006 |
| 27 | ghost + hop, then scan the hop seat's row | 0.023 | 1 | 0.006 |
| 28 | ghost + hop, then row = marker + suit of the hop-seat blocker | 0.009 | 0 | 0.005 |
| 29 | as 27 with two hops | 0.016 | 1 | 0.006 |
| **30** | ghost + row = marker + blocker's suit, start at target column | 0.015 | 0 | 0.0055 |
| **31** | ghost + hop, then row = marker + blocker's suit from hop column | 0.009 | 0 | 0.0049 |
| **33** | **ghost + row = marker + blocker's suit, start column = target + blocker's rank** | 0.010 | 0 | 0.0051 |
| 35 | 33 without the ghost | 0.018 | 5 | 0.010 |

Not pursued, with reasons:

* **"Bump the occupant"** (idea 1): the blocker rule already uses the occupant's card; bumping
  moves cards already placed, which makes the inverse harder to follow at the table. Not needed.
* **Making K♣ a non-zero step** (idea 2): with #1, K♣ pairs are at most 0.0062, only slightly above
  the rest; not needed.
* **A second pass** (idea 3): the only way to go below the one-pass floor (1/1326 per pair, and
  71% of #1's residual is in the last four positions), but it roughly doubles GridCycle's hand
  work. #1 is already 2.5× under the bar, so a second pass is not recommended now; not measured.

## How a person does the recommended rule (#1) at the table

Setup is as in v10: clear the 4×13 table, marker chip on ♣, suits count ♣ ♥ ♠ ♦ (0 1 2 3).

1. Put the first card at row 2, column 0 (the A♠ home seat). Put your finger there.
2. For every next card, step from your finger by the card you just placed: down by its suit
   (♣ 0, ♥ 1, ♠ 2, ♦ 3 rows, wrapping from the bottom row to the top), right by its rank
   (A 1 … Q 12, K 13 = no move; wrapping from column 12 to column 0). **Move your finger to that
   target seat and keep it there**, whatever happens next.
3. If the target seat is empty, put the new card there. (Exactly as in v10.)
4. If the target seat is taken, look at the card sitting there, the **blocker**:
   * **Row:** start at the marker's suit row and count on by the blocker's suit (♣ +0, ♥ +1, ♠ +2,
     ♦ +3, wrapping ♦ → ♣).
   * **Column:** from the target's column, count right by the blocker's rank (like a normal step).
   * From that seat, go right along that row (wrapping) to the first empty seat and put the new card
     there. If that row is full, drop to the next row down and go right from the same column.
   * Move the marker chip on by one suit.
5. Go back to step 2. The next step starts from your **finger** (the target seat), not from where
   the card ended up.

In short: "a free seat takes the card; a taken seat's owner sends you — its suit from the marker's
row, its rank from your column — to the first gap on the right; your finger stays where you were
aimed."

**Decrypting** (inverse GridCycle): lay the packet row-major as in v10 and walk with visited marks.
Take the card at row 2, column 0; finger there. Step from the finger by the card you just took; move
the finger to the target. If the target is unvisited, take its card. If it is visited, its card is
the blocker (it is still lying there): same row and column rule, first **unvisited** seat to the
right, take that card, move the marker on. The next step again starts from the finger. This is
exactly the forward walk with "empty" read as "unvisited", which is why it inverts (checked on
100 000 decks for every candidate, 0 failures).

For #2 (the simpler fallback): identical, except the column part of step 4 is dropped: scan the
row (marker + blocker's suit) starting at the target's own column. One mod-4 addition per blocked
placement instead of two additions; worst pair 1/84, still under the bar.

## Files (Phase 2)

| file | what |
|---|---|
| `cand.c` | candidate choosers; modes `value`, `stats` (cost + inverse round trip), `cyc3`, `round`, `gap`, `x` (dump) |
| `candcheck.py` | cand.c v10 GridCycle and stem == ddport |
| `p2/scr_*.txt`, `p2/screen_summary.log` | 3000-deck screens |
| `p2/full_{30,31,33}_*.txt`, `p2/full_summary.log` | 200 000 decks per pair |
| `p2/cyc3_*.log` (N=400), `p2/cyc3b_*.log` (N=4000, refined 200 000) | 3-cycles |
| `p2/round_*`, `p2/round_summary.log` | one v10 round, same-suit pairs, 400 000 decks |
| `p2/cost.log` | seats checked (mean, p50/p90/p99, max), overflows, round-trip check |
| `p2/gap_0.log`, `p2/gap_33.log` | survival by distance between the swapped walk positions |
| `run_phase2.sh` | reproduces all of the above (not CI; roughly 1 CPU-hour) |
