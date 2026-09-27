# v10 SumRanks experiments (empirical log; analysis only, not a proof)

> **Copied from a local scratch log** that was written while choosing the v10 SumRanks. It is kept verbatim below this banner, except for this note. Only the files needed for the W family (the section that led to v10 = W5c) were copied here; files it mentions that are not in this folder (`exp1.*`, `measure*.{py,log,json}`, `allpairs.json`, `allpairs_SR.*`, `sronly.*`, `*.npy`) stayed in scratch, and the v9-candidate originals are in [`../../../deprecated/doubledeal-v9/candidates/`](../../../deprecated/doubledeal-v9/candidates/). "Local scratch, nothing is pushed" in the first paragraph described the scratch folder, not this copy. Every number is a Monte Carlo measurement or a heuristic product formula. **None is a proof and none is a security claim.** "AES parity" below means a per-layer swap-survival target (≤ 1/64) chosen for these experiments, not a security property. **Superseded worst case:** the "SumRanks-only worst 1/221" figures below cover two-card swaps only. The wider search in [`sbox-search/`](sbox-search/) found that a same-suit 3-cycle passes SumRanks alone with probability exactly 9/1105 ≈ 1/123. That is still below 1/64, and nothing except the 51 exact `v10Sym` symmetries exceeds 1/64.


This folder is a local scratch area only. Nothing here is pushed or touches the spec, Generated/ or any shared branch. The base code is `proofs/deprecated/doubledeal-v9/candidates/` from PR #86, with new variants added to `cand.c` (C) and `candidates.py` (Python). `check_cand.py` passes: the v9 variant matches the 6 frozen vectors, C == Python, and decrypt(encrypt) = id on 600 cases across 10 variants.

## Geometry (checked in dd_v9.py)

- The deck is laid column-major into a grid of **4 rows × 13 columns**.
- SumRanks has two steps. The row step rotates each 13-card row left by Σrank mod 13, using **rank only**. The column step then rotates each 4-card column down by Σ(rank+suit) mod 4.
- For a uniform deck, a given other card is in the same 4-card column with probability 3/51 and in the same 13-card row with probability 12/51.

## Experiment 1: which swaps survive in v9 (`exp1.py`, output in `exp1.log`)

**Hits traced:** all recorded hits for K♣↔Q♥ (14 at F6, 20 at F4) plus fresh F3 hits (up to 400 per pair) for several pairs.

| Pair (hits) | All layers commute in every round | Same **column** at the SumRanks input in every round | Same **row** in every round |
| --- | --- | --- | --- |
| K♣↔Q♥, F6 (14) | 14/14 | **0/14** | **14/14** |
| K♣↔Q♥, F4 (20) | 20/20 | 0/20 | 20/20 |
| K♣↔Q♥, F3 (400) | 400/400 | 0/400 | 400/400 |
| Q♣↔J♥, F3 (151) | 151/151 | 0 | 151/151 |
| A♥↔K♥, F3 (111) | 111/111 | 0 | 111/111 |
| K♠↔Q♦, F3 (51) | 51/51 | 0 | 51/51 |
| A♣↔K♣, F3 (114) | 114/114 | 0 | 114/114 |
| K♣↔K♦ (same rank), F3 (20) | 20/20 | 0 at the input; **20/20 in the same column after the row step** | 0/20 |

Per round, on uniform decks (400,000 decks each):
- P(same row) = 0.235 and P(same column) = 0.059 for every pair.
- For equal-w4 pairs such as K♣↔Q♥, P(SumRanks+ShiftRows ok) equals P(same row) exactly: 0.2347 against 0.2347.
- For same-rank pairs it is about 0.059, which is being in the same column after the row step.
- For pairs with different rank and different w4 (A♣↔2♣) it is 0.
- The per-round survival rates are: K♣↔Q♥ 1/23, Q♣↔J♥ 1/35, A♥↔K♥ 1/46, K♠↔Q♦ 1/64, K♣↔K♦ 1/57.

**H2 is false for the K♣↔Q♥ class.** No hit had the two cards in the same column. Every hit had them in the same **row** in **every** round. The blind spot is the symmetric *row* sum, which cannot see a swap inside one row (12/51). The column step lets the pair through because K♣ and Q♥ have equal (rank+suit) **mod 4** (13 ≡ 1).

H2's picture is right for the other class, same-rank pairs: the row step can't see them, and they survive by sitting in the same column when the column step runs (3/51).

(3/51)^6 = 4.1e-8 matching the measured 3.5e-8 is a coincidence. The actual mechanism is (12/51)^6 × P_G^5 = 1.7e-4 × 0.184^5 = 3.5e-8, where P_G is the GridCycle survival.

**H1 is partly right.** K♣ and Q♥ both have rank+suit = 13, but v9 only uses rank+suit **mod 4**. What matters is equality mod 4: A♥↔K♥ (2 and 14) and K♠↔Q♦ also survive at 12/51. The mod-13 collision only becomes the weakness once rows weigh rank+suit (see PW2 below).

## Experiments 2 and 3: new SumRanks variants

GridCycle is unchanged (v9) in all of them. Every variant is still a cipher (decrypt checked).

- **SP (Experiment 2).**
  - Row step as v9 (rank only).
  - The column step uses **rank only**: rotate each column down by Σrank mod 4.
  - Then **SuitProduct**: map suits to 1..4 (♣1 ♥2 ♠3 ♦4), take p = Π(suit+1) mod 5 (always nonzero), and rotate the column down by p mod 4, the same action as the column step.
  - It is invertible because a column's product does not change when the column is rotated.
  - A product in Z5* is a cyclic group of order 4, so p is the same thing as a sum of discrete logs mod 4. It is another symmetric column function, so it cannot see same-column swaps.
- **PW (Experiment 3, order-sensitive).**
  - Rows are chained: in the order 1, 2, 3, 0, row i rotates by Σ_c (c+1)·rank(row i−1)[c] mod 13, reading the row above as it currently is.
  - Columns are chained the same way: in the order 1..12, 0, column j rotates by Σ_r (r+1)·(rank+suit)(column j−1) mod 4.
  - Undo in reverse order.
- **PW2** is the fix for PW's weakness.
  - Rows are chained and position-weighted as in PW, but weigh **rank+suit** (mod 13).
  - Columns use v9's own-column rotation by **Σsuit mod 4**. Any two cards the rows can't tell apart have different suits, and a suit difference is never 0 mod 4.
- **PW3** is PW2 followed by one chained column pass: column j rotates by (Σ_r (r+1)·(rank + 4·suit)(column j−1) mod 13) mod 4.

The table is produced with the same method and seeds as CANDIDATES.md (`measure.py 1 11 <variant>`).
- **Worst pair:** found by the all-pairs scan at n = 20,000 per pair, then re-measured at 400,000.
- **Exact rates:** F2 1e6, F3 4e6, F4 1.6e7 pairs with real keys. Zero-hit cells give the 95% upper bound (3/n).
- **F6 extrap.:** `extrap.py`. **F6 formula:** P_S^6 (P_round/P_S)^5.
- **All-pairs columns:** from `allpairs.py` (`allpairs.log`). The last column sums the F6 formula over all 1326 pairs.

| Variant | Worst pair, per round | F2 / F3 / F4 (worst pair) | F6 extrap. | F6 formula (worst) | K♣↔Q♥ per round; F2 / F3 / F4 | v8 K♣↔K♦ per round; F2 | Pairs with P_round ≥ 1e-2 | Σ over pairs of F6 formula |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| v9 | K♣↔Q♥ 1/23 | 1.02e-2 / 4.14e-4 / 1.82e-5 | 3.2e-8 (F6 measured 3.5e-8) | 3.3e-8 | 1/23; as left | 1.7e-2; 1.0e-3 | 117 | 6.3e-8 |
| R2 | K♣↔K♦ 1/64 | 9.08e-4 / 1.38e-5 / 1.25e-7 (2 hits) | 1.9e-11 | 5.4e-11 | 1/97; 6.4e-4 / 7.8e-6 / 1.3e-7 (2 hits) | 1.6e-2; 9.4e-4 | 4 | 2.1e-10 |
| GR2 | K♣↔K♠ 1/59 | 1.03e-3 / 1.55e-5 / 3.13e-7 (5 hits) | 9.0e-11 | 7.9e-11 | 1/6250; 1.1e-5 / <7.5e-7 / <1.9e-7 | 6.6e-3; 3.8e-4 | 4 | 1.2e-10 |
| **SP** | A♥↔K♥ 1/46 | 4.99e-3 / 1.09e-4 / 2.19e-6 (35 hits) | 9.7e-10 | 1.2e-9 | 1/381; 4.4e-5 / <7.5e-7 / <1.9e-7 | 1.7e-2; 9.9e-4 | 31 | 3.4e-9 |
| **PW** | K♣↔K♠ **1/16** | 1.58e-2 / 9.76e-4 / 5.74e-5 | **2.1e-7** | 2.3e-7 | 1/428; 7e-6 (7 hits) / <7.5e-7 / <1.9e-7 | 1.6e-2; 9.5e-4 | 30 | 4.0e-7 |
| **PW2** | K♣↔Q♥ 1/78 | 7.95e-4 / 1.20e-5 / 1.88e-7 (3 hits) | 4.4e-11 | 2.1e-11 | 1/78; as left | 1.7e-3; 3e-6 (3 hits) | 1 | 5.0e-11 |
| **PW3** | 8♣↔5♦ 1/559 | 4.7e-5 / 2.5e-7 (1 hit) / <1.9e-7 | 3.8e-14 (2 points, unreliable) | 5.2e-16 | 1/718; 4e-6 (4 hits) / <7.5e-7 / <1.9e-7 | 7.5e-5; <3e-6 | 0 | 6.6e-15 |

v9Sym: the full round commuted 0/1,020,000 times for every variant, and v9Sym(0,1) at F2 gave 0/1e6.

**Reading the table**
- **SP** mostly moves the problem. Row symmetry is still there, and now the column steps let through pairs with the same suit and rank ≡ mod 4 (A♥↔K♥, A♣↔K♣) at 12/51. The worst pair is 1/46 per round, the F6 formula is about 1e-9 (roughly 30× below v9), and there are more exposed pairs overall (810 pass SumRanks sometimes, against v9's 390).
  - K♣↔Q♥ is not zero (P_S 0.0145). The two column rotations add up to one rotation by (Σrank + Πsuit) mod 4, so their shifts can cancel.
- **PW is worse than v9.** A 4-card column rotation has only 4 outcomes, and position weights mod 4 cannot be distinct units. A same-rank swap with a suit difference of 2 (♣↔♠) is invisible whenever (r+1)·2 ≡ 0 mod 4. So K♣↔K♠ survives SumRanks 25% of the time, which is 1/16 per round.
- **PW2** removes the row blind spot. A position-weighted row sum sees any swap of two cards whose row values differ, wherever they sit. What remains is H2's same-column blind spot, for the 78 pairs with equal rank+suit mod 13; K♣↔Q♥ is one of them (the H1 collision). They get through at 3/51, giving 1/78 per round and an F6 formula of about 2e-11, which is on par with R2 and GR2. The F4 figure rests on 3 hits.
- **PW3** also chains a position-weighted column pass. The worst pair found is 1/559 per round and the F6 formula is about 5e-16. The low hit counts matter here:
  - F3 had 1 hit and F4 had 0, so the F6 extrapolation is **not meaningful**. Only the per-round scan and the formula support that figure.
  - The worst-pair scan has a resolution of 5e-5 per pair, and taking the maximum of 1326 noisy estimates biases it upward.
  - It is still far above 1/52!.
- **Common thread.** Every invertible "rotate by a function of the cards" layer that computes its rotation from the same row or column must use a function that doesn't change when that line is rotated. Symmetric sums and products are the easy choice, and they are exactly what hides swaps inside a line.
  - Chaining (reading the neighbouring row or column, Feistel-style) lets the function depend on position, which is what PW2 and PW3 exploit.
  - The mod-4 column rotation stays the weak spot, because any change survives a 4-outcome choice about 1/4 of the time.
- **Hand feel.** PW2 and PW3 need a position-weighted sum of 13 cards mod 13 for every row (weights 1..13). That is much heavier by hand than v9, and one position always has weight 13 ≡ 0.
- **GridCycle** is unchanged in all variants, and its survival (0.03–0.25 per pair) is now the dominant per-round factor in PW3.

## Files

| File | What |
| --- | --- |
| `exp1.py`, `exp1.log`, `exp1.json` | Experiment 1 (hit tracing, per-round probabilities) |
| `cand.c`, `candidates.py`, `cport.py`, `check_cand.py` | Variants: bits 16 SP, 32 PW, 64 PW2, 128 PW3 (plus the CANDIDATES.md ones) |
| `measure.py` | `python3 measure.py 1 11 SP,PW` etc. (a third argument selects variants) |
| `measure_SP_PW.log/.json`, `measure_PW2.log/.json`, `measure_PW3.log/.json` | Runs for the new variants. `measure.json` is the #86 run for v9, A3, R2, G, GR2 and B4 (same seeds). |
| `extrap.py`, `extrap.log` | F6 extrapolation (least squares over the non-zero F2–F4 points) |
| `allpairs.py`, `allpairs.log`, `allpairs.json` | All-pairs per-round survival per variant |

## Follow-up: repeated SumRanks passes (SR2, SR3; SR4 for the SumRanks-only test)

**Variants.** SR2 runs v9 SumRanks twice per round (row step, column step, row step, column step). SR3 runs it three times. All other layers are unchanged from v9. Each pass is inverted in reverse order. `check_cand.py` passes: decrypt(encrypt) = id on 720 cases across 12 variants.

**Scripts and logs**
- `srpairs.py` / `srpairs.log`: fixed pairs, 400,000 decks each, the same decks for every variant.
- `measure.py 1 11 SR2,SR3` / `measure_SR2_SR3.log`: same seeds and method as the earlier table.
- `allpairs.py` (run with `VARS=SR2,SR3`) / `allpairs_SR.log`.
- `extrap.py` / `extrap_SR.log`.
- `sronly.py` + `srcount.c` / `sronly.log`: SumRanks-only survival for 1 to 4 passes. Stage 1 runs all 1326 pairs × 200,000 decks. Stage 2 re-measures the top 5 per variant at 4e6 decks with fresh seeds.

**Per-round survival** (P_S = SumRanks+ShiftRows commutes, which is SumRanks-only because ShiftRows always commutes; P_round = P_S and GridCycle both commute):

| Pair | v9 P_S / per round | SR2 P_S / per round | SR3 P_S / per round |
| --- | --- | --- | --- |
| K♣↔Q♥ | 0.2346 / 1/24 | **0.0583** / 1/95 | 0.0147 / 1/368 |
| A♥↔K♥ | 0.2359 / 1/46 | 0.0582 / 1/186 | 0.0143 / 1/731 |
| K♣↔K♦ | 0.0586 / 1/59 | 0.0045 / 1/771 | 0.0003 / 1/10,526 (38 hits) |

- Your prediction holds: for K♣↔Q♥, SR2's SumRanks survival is 0.0583 ≈ 0.235 × 0.25 = 0.0588.
- The reason: after one pass the two cards still share a row, and the next pass needs them in the same row again. Their two columns rotate independently, so that happens 1/4 of the time.
- Each extra pass multiplies equal-w4 pairs by 1/4. It multiplies same-rank pairs by about 1/13.
- P_G does not change, and P_round ≈ P_S × P_G.

**Whole cipher.** Hand cost counts the cards read into a mental sum:
- One SumRanks pass = 104 (4 rows × 13 cards, plus 13 columns × 4 cards).
- GridCycle ≈ 104 (52 placements × 2 small adds).
- A full round = SumRanks + GridCycle. The final round = SumRanks only.
- PassKey key generation (1 per round, counting and rotation rather than sums) is not included.

For the "v9, R rounds" rows, the worst-pair and all-pairs figures come from the v9 per-pair P_S and P_round in `allpairs.json`, via F_R = P_S^R P_G^(R−1), where P_G is the GridCycle survival given that SumRanks already commuted. They are formulas only; nothing was measured beyond F6.

| Design | Mental sums (whole cipher) | Keys | Worst pair per round | Worst pair F2 / F3 / F4 (hits) | Worst-pair F-final, formula | Worst-pair F-final, extrap. | Σ over all pairs, formula |
| --- | --- | --- | --- | --- | --- | --- | --- |
| v9, 6 rounds | 1144 | 7 | K♣↔Q♥ 1/24 | 10184 / 1654 / 292 | 3.3e-8 | 3.2e-8 (measured 3.5e-8, 14 hits) | 6.3e-8 |
| v9, 7 rounds | 1352 | 8 | " | – | 1.4e-9 | 1.4e-9 | 2.0e-9 |
| v9, 8 rounds | 1560 | 9 | " | – | 5.8e-11 | 5.7e-11 | 7.1e-11 |
| v9, 9 rounds | **1768** | 10 | " | – | 2.5e-12 | 2.4e-12 | 2.7e-12 |
| v9, 12 rounds | **2392** | 13 | " | – | 1.9e-16 | 1.8e-16 | 1.9e-16 |
| SR2, 6 rounds | **1768** | 7 | K♣↔Q♥ 1/95 | 639 / 18 / 4 | 7.6e-12 | 6.9e-11 (rests on 4 F4 hits; F4 is ~3.5× above the formula) | 1.4e-11 |
| SR3, 6 rounds | **2392** | 7 | K♣↔Q♥ 1/378 | 48 / 0 / 0 | 1.9e-15 | not measurable (F3 and F4 had 0 hits) | 3.5e-15 |

**SumRanks-only against the AES S-box** (max differential probability 4/256 = 1/64 = 0.0156). This is an analogy: swap survival of one relabelling is not the same quantity as differential probability.

| Passes | Pairs > 0 | Pairs > 1/64 | Worst pair, re-measured at 4e6 decks (95% interval) |
| --- | --- | --- | --- |
| 1 (v9) | 390 | 390 | 0.2361 ± 0.0004 = 1/4.2 |
| 2 (SR2) | 403 | 312 | 0.0589 ± 0.0002 = 1/17 |
| 3 (SR3) | 390 | **0** | **0.0148 ± 0.0001 = 1/68** |
| 4 (SR4) | 390 | 0 | 0.0037 ± 0.0001 = 1/271 |

**SR3 is the first variant with its worst pair at or below 1/64.** The margin is small: 0.0148 against 0.0156, which is exactly 12/51 × (1/4)^2 = 0.0147. That is resolved by the interval, but it is only about 6% below the benchmark. All 312 equal-w4 pairs are statistically tied, so the name of the "worst pair" is noise; only the value matters.

**Extra passes against extra rounds.**
- An extra SumRanks pass costs 104 sums and cuts the worst per-round rate by about 4×.
- An extra v9 round costs about 208 sums (plus one more PassKey key) and cuts it by about 24×. That is about 4.9× per 104 sums.
- So at equal hand work, extra rounds come out slightly ahead on the formula: v9 at 9 rounds 2.5e-12 against SR2 7.6e-12; v9 at 12 rounds 1.9e-16 against SR3 1.9e-15. SR2's own measured extrapolation (6.9e-11) is worse still, but it rests on 4 hits.
- Passes do have advantages: they need no extra key schedule, they hit same-rank pairs harder (×1/13 per pass), and SR3 reaches per-layer parity with the AES S-box (1/68 vs 1/64), which extra rounds never do (a v9 layer stays at 1/4.2).
- Neither approach removes the structural symmetry. Rates fall geometrically in either case, and SR3 at 6 rounds (~2e-15) is still enormously above 1/52!.

## Follow-up: index-weighted SumRanks (W family) and the GF(4) suit sum (W5)

**Variants** (`cand.c` `sum_ranks_w`, mirrored in `candidates.py`; `check_cand.py`: decrypt(encrypt) = id on 1500 cases across 25 variants, v9 still matches the 6 frozen vectors). All W rows are chained Feistel-style: rows in order 1,2,3,0, row i rotates left by the index-weighted sum Σ_k (k+1)·v(row i−1 [k]) mod 13 (weights 1..13, so the 13th card has weight 0). v = rank, except W2 (rank + suit).
- W1: W rows, then the v9 column step. W2: rank+suit rows, v9 column step.
- W3: W rows, then chained columns (order 1..12,0): column j rotates down by (Σ_r (4−r)(suit+1) of column j−1 mod 5) mod 4. W4: W3 plus the column's own Σ suit (rotation-invariant).
- **W5**: W rows, then chained GF(4) columns. Suits as GF(4) labels ♣=0 (00), ♦=1 (01), ♥=w (10), ♠=w² (11); w² = w+1, addition = XOR. Value of column j−1 = 0·s(row 0) ⊕ 1·s(row 1) ⊕ w·s(row 2) ⊕ w²·s(row 3); columns in order 1..12,0, column j rotates down by that 2-bit label. Invertible because column j−1 is final when column j moves (decrypt runs the order backwards).
- **W5b**: as W5 with s replaced by s ⊕ (rank mod 4).
- **W5c**: as W5, with the label XORed with column j's own unweighted GF(4) suit sum (XOR of its 4 labels; that doesn't change under rotation, so it stays invertible). This is the W4 trick.
- x2 = the whole W step applied twice.

**Why W5 alone fails.** GF(4) has only three non-zero elements, so four distinct row weights force one weight to be 0. The top-row card of every column is invisible to the column step. A same-rank pair (invisible to the rank rows) survives whenever the two cards sit in different columns, both in row 0: (48/51)·(1/16) = 0.0588, exactly what was measured. W5b doesn't help, because a same-rank pair's difference is still just the suit difference. W5c's own-column XOR has weight 1 on every row, so it catches the row-0 case: same-rank pairs drop to **0 hits in 200k decks per pair**.

**Blind spots per step** (by construction, confirmed by `blindclass.py` / `blindclass.log`):
- Rank rows (W1, W3–W5c) are blind to same-rank pairs (78). Apart from that, they miss only residual coincidences, about 1/220 on other pairs (the weight-0 13th position and mod-13 collisions).
- GF(4) columns (W5, W5c) are blind to same-suit pairs (312). Any in-column swap of two different suits is always visible. W5's only other miss is the row-0 case above.
- So no pair is blind to both steps in W5/W5c. What's left is the same-suit pairs at the row step's ~1/220 residual rate. W2 is fully blind (P = 1) to the 78 pairs with equal rank+suit (e.g. T♠↔9♦), because both of its steps weigh rank+suit.

**Table.** SumRanks-only: `sronly2.py` / `sronly2_all.log` (all 1326 pairs × 200k decks; the top 5 re-measured at 4e6 with fresh seeds). Full-round: `VARS=v9,SR3,PW2,PW3,W1,…,W5cx2 OUT=allpairs_W.json python3 allpairs.py 100000 > allpairs_W.log` (100k decks/pair). F6 = the product formula P_S^6 (P_round/P_S)^5 for the worst pair, and the sum over pairs. Hand cost uses the earlier convention (one add = 1; an index-weighted sum by the running-total trick T+=v, U+=T = 2 per card; a GF(4) multiply by w or w² = 1 lookup; each XOR = 1), 6 SumRanks passes + 5 GridCycles at 104 each, PassKey excluded.

| Variant | SumRanks pass cost | Whole cipher | SR-only worst (4e6, 95%) | Pairs > 1/64 | Surviving pair classes (SR-only) | Worst per round (pair) | Worst-pair F6 formula | Σ pairs F6 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| v9 | 104 | 1144 | 0.2361 = 1/4.2 | 390 | equal w13/w4 | 4.3e-2 (K♣↔Q♥) | 3.6e-8 | 7.0e-8 |
| SR3 | 312 | 2392 | 0.0148 = 1/68 | 0 | same 390 | 2.5e-3 (K♣↔Q♥) | 1.5e-15 | 4.2e-15 |
| PW2 | 156 | 1456 | 0.0589 = 1/17 | 78 | all | 1.3e-2 (K♣↔Q♥) | 1.8e-11 | 5.6e-11 |
| PW3 | 260 | 2080 | 0.0287 = 1/35 | 13 | all | 2.3e-3 (K♣↔T♦) | 1.7e-15 | 7.8e-15 |
| W1 | 156 | 1456 | 0.0590 = 1/17 | 78 | all (same-rank 1/17) | 1.7e-2 (K♣↔K♦) | 8.7e-11 | 5.8e-10 |
| W2 | 156 | 1456 | **1.0** (T♠↔9♦) | 78 | all; 78 always | 1.8e-1 (K♣↔Q♥) | 1.9e-4 | 3.5e-4 |
| W3 | 208 | 1768 | 0.0159 = 1/63 | 41 | all | 4.3e-3 (K♣↔K♥) | 2.3e-14 | 1.1e-13 |
| W4 | 260 | 2080 | 0.0062 = 1/160 | 0 | all | 1.8e-3 (K♣↔K♥) | 1.1e-16 | 1.2e-15 |
| W5 | 156 | 1456 | 0.0588 = 1/17 | 78 | same-rank, same-suit | 1.7e-2 (K♣↔K♦) | 7.6e-11 | 3.2e-10 |
| W5b | 208 (+52 rank→label) | 1768 | 0.0591 = 1/17 | 78 | same-rank + 312 others | 1.7e-2 (K♣↔K♦) | 7.2e-11 | 3.3e-10 |
| **W5c** | **208** | **1768** | **0.0045 = 1/221** | **0** | **same-suit only** | 1.4e-3 (Q♣↔K♣) | 2.1e-17 | 4.8e-16 |
| W5x2 | 312 | 2392 | 0.0053 = 1/190 | 0 | same-rank, same-suit | 1.5e-3 (K♣↔K♥) | 3.6e-17 | 3.0e-16 |
| W5cx2 | 416 | 3016 | 0.0001 = 1/7300 | 0 | same-suit only | 8e-5 (3♣↔4♣, 8 hits) | 7.9e-25 (unreliable) | 1.8e-24 |

W5c pass cost: 104 (weighted rows) + 13 × (2 lookups + 2 XORs for the weighted label + 3 XORs for the own-column sum + 1 XOR to combine) = 208. For comparison, v9 at 9 rounds also costs 1768 (worst-pair formula 2.5e-12; its layers stay at 1/4.2).

**Recommendation.** W5c is the lightest variant that meets per-layer AES parity: SumRanks-only worst 1/221, 0 pairs above 1/64, 208 per pass, 1768 per encryption. W4 also passes (1/160), but costs 260 per pass and leaves every class partly alive. W5c's only survivors are same-suit pairs, which get through at the row step's ~1/220 residual rate. It kills same-rank pairs outright (0 hits), and at equal hand cost its 6-round formula (2.1e-17) is far below v9 at 9 rounds (2.5e-12). W5 as specified fails because of the forced weight 0 (1/17, the same as W1), and W5b doesn't fix it. W5x2 passes, but costs 1.5× W5c for a similar number. GridCycle is unchanged and is now the larger per-round factor, and these are formula figures, not measured F2–F4 rates.
