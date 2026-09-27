# DoubleDeal: is there an AES-style branch number? (measurement + proposal, analysis only)

Scope. Everything here is an empirical measurement on the Python port or a proof *sketch*, except
the floor and GridCycle tail statements of §4, which are proved in Lean (PR #84).
Nothing here is a security or bit-security claim, and nothing proposes a change to the cipher.
Where a search did not find something, that is reported as "not found by this search", not as
"does not exist".

## Setup

* Port: `../ddport.py` (v8 = frozen `dd_v8.py`; v9 adds A2 + B3). `../selftest.py` (run in CI)
  checks v9 against the repo vectors (`encrypt`, `mix_columns`, `unkeyed_full`, `sum_ranks`) and
  the v8 path against the frozen `dd_v8.py`; `dd_v8.py` passes its own `check_vectors.py` (29/29). `measure.py`
  also asserts ddport's v8 GridCycle equals the frozen `dd_v8.mix_columns` on every deck it uses.
* Spec note: v9 SumRanks rotates **rows by (sum of rank) mod 13** and **columns by
  (sum of rank + suit) mod 4** (SPEC §3.3), as in the port.
* The notion measured is the **differential (pair) branch number over seat weight**; there is no
  linear analogue because no layer has linear structure.
  Weight of a difference = number of seats where two decks differ. Two distinct decks differ in
  at least 2 seats, so for any bijection F on decks, `wt_in + wt_out >= 4`. **4 is the trivial
  floor**; the question is whether any layer beats it. (AES's scale is different: a byte can change
  value in place, so weight 1 exists there; here every layer only moves cards.)
* Layers (deck -> deck): `GC` = GridCycle (`mix_columns`); `SR` = lay_cm, SumRanks, scoop_cm;
  `SRGC` = GridCycle ∘ ShiftRows ∘ SumRanks (the unkeyed full round); `SRGC_noSh` = GridCycle ∘
  SumRanks with no ShiftRows (literally "SumRanks then GridCycle"); `RK` = a full round with one
  fixed key (`FIXED_KEY` = shuffle with seed 20260927). Compose is a fixed seat permutation, so
  `RK` has exactly the same weight as `SRGC` on every pair (asserted on all 2.65M pairs).

## 1. Distributions (all 1326 swaps, 1000 random decks per version: `measure.log`)

| layer | ver | min | P(w=2) | P(w<=8) | P(w<=16) | mean |
|---|---|---|---|---|---|---|
| GC        | v8 | 2 | 11.99% | 15.3% | 23.2% | 29.35 |
| GC        | v9 | 2 |  4.30% |  7.5% | 14.4% | 32.78 |
| SR        | v8 | 2 | 10.15% | 28.0% | 28.0% | 34.34 |
| SR        | v9 | 2 |  5.90% | 28.0% | 28.0% | 34.59 |
| SRGC = RK | v8 | 2 | 1.30%  | 1.67% | 2.81% | 46.84 |
| SRGC = RK | v9 | 2 | 0.261% | 0.444% | 1.09% | 47.98 |
| SRGC_noSh | v8 | 2 | 1.27%  | 2.07% | 4.34% | 45.56 |
| SRGC_noSh | v9 | 2 | 0.273% | 0.791% | 2.75% | 46.46 |

(For comparison, two independent random decks differ in 51 seats on average.) Full histograms
are in `measure.log`. SR takes only the weights {2, 8} or >= 26 on swaps (see §3.2), which is why
its P(w<=8) equals its P(w<=16).

**Minimum observed: 2 for every layer and combination, in both versions.** Random sampling finds
it; no adversarial search is needed. So the branch number (min of `wt_in + wt_out`) is
**exactly 4, the trivial floor**, for GC, SR, SR->GC and one keyed round, in v8 and v9.

Other difference weights (`search.py`, hill climbing, `search.log`): for 3-cycles (in = 3) the
minimum output weight is 2 for GC, SRGC and RK (in+out = 5). For SR, minimum found 3 (hill
climbing; 2 not excluded), so in+out = 6 found. None of this improves on the swap minimum.

## 2. Adversarial / targeted search (`search.log`, `search2.log`, `trail_*.log`)

Every witness below is re-verified from scratch by `witnesses.py`, which writes `witnesses.json`
(full decks and positions). Selected examples, with decks written as card names in seat order:

* v9 one keyed round, weight 2 -> 2: swap seats (17, 21) = 8D, 4D, deck
  `QD KD 5D 6H 8S JH 3D TH 3H 3S JS 5C QC 2S 3C JD 7D 8D 4H 7H 7C 4D TD 4S JC 9S 2H AH 9D QH 2D TS KC AS 4C 6D AD 8H 8C 6S 9H 5H 2C AC 7S TC QS KH 6C 9C 5S KS`
  with key `FIXED_KEY`.
* v9 GC, the walk-card-0 case (p = 0): swap seats (0, 6) = K♣, K♠ (weight 2), deck
  `KC 9C 2D KD AH 4D KS QS 7H 3S QC 8H QH 5H 3H 8C 2H QD 5S 3C 6C TH TD 6S 2S AS 6D JH 7C 4H 6H KH 4C 5C JD 7D 9S JS 5D 8S 9D JC AC 9H 4S 8D 2C 3D AD TS 7S TC`.
* v9 SR, cross-row and different-rank class, minimum found 26 (= the proven-looking floor, §3.2):
  swap seats (19, 40) = J♣, 4♦, deck
  `9S 5C 4S TH 6S KD 9H 8H AD KH 3H 4C KC QD 2H 2S 5S 7H AH JC 6D TD TS 9C KS 5D 3S 6C 3D 8C JD JH 7D 7S AS JS 4H 3C QH 2C 4D 9D AC QS QC 8S 5H 7C TC 8D 6H 2D`.
* Several keyed rounds (real PassKey keys K1..Kr of `FIXED_KEY`), with the difference still a
  single swap after every round:
  - v8: 2, 3, 4 and 5 rounds, and **the whole v8 encrypt** (swap in, swap out; J♦/J♣, a same-rank
    pair, which is the known v8 relabelling weakness showing up as a difference trail).
  - v9: 2 and 3 rounds by plain hill climbing. Plain hill climbing stalled at weight 43 for
    4 rounds, 5 rounds and full encrypt, but the guided trail search (`trail_search.py`, whose
    objective counts how many rounds the swap survives) found **4-round swap-only trails in v9**
    (3 of 8 runs, in 600 s each; e.g. Q♣/J♥, Q♥/K♣, J♠/J♣), see `trail_v9_4.log`.
    5 rounds / full encrypt: not found (§2a).
  These are existence results for one fixed key, found with the key in hand. They are not a
  key-recovery or distinguishing attack, and a random permutation of decks also has about
  1326²/2 swap->swap pairs, which could not be *found* efficiently there. The
  information content is how cheaply such pairs are found, and the per-round probabilities below.

§2a (v9, 5 rounds / full encrypt). The guided search (4 processes x 1200 s per target) did
**not** find a 5-round swap-only trail. The best trail survived 4 of 5 rounds (Q♥/K♣, weights
2,2,2,2 then 51). On the whole v9 encrypt, the best pairs stay a swap through whitening plus full
rounds K1..K4, then break at K5 (weights 49-51). So, for this key and budget, the longest
swap-only trail found in v9 is **4 keyed rounds**; in v8 it is the whole cipher. "Not found"
here is a statement about the search, not a bound.

Early swaps in the walk (GC, both swapped walk indices <= Q): min weight 3 for Q = 1 (both
versions) and for Q = 2 in v8; min 2 for every other Q. For walk cards (0, 1) the bound 3 is
forced: the seat sequence to seat 2 depends only on the first two cards, and it differs for every
ordered pair (`seat2` is injective except K♣/K♠, and for that pair the K♣ self-overflow sends the
third seat to (1,0) vs (0,1)).

### Multi-round persistence (`multiround.log`, 3000 decks x 1326 swaps per version)

| | P(w1 = 2) | P(w2 = 2 given w1 = 2) | P(w3 = 2 given w2 = 2) |
|---|---|---|---|
| v8 | 1.29e-2 | 1.05e-1 | 1.45e-1 |
| v9 | 2.61e-3 | 1.17e-2 | 0 / 122 (none observed) |

The conditionals are far above the one-round rate, so the rounds are **not** independent here.
The reason is structural: while the difference stays a swap, the same two card *values* keep
being exchanged. In v9, **every** pair that survived even one round as a swap was either same-rank
(22%) or a ≡ b (mod 4) with different ranks (78%). Those are exactly the pairs for which SumRanks
can return weight 2 (§3.2); they make up only 390 of the 1326 value pairs. In v8, same-rank pairs
dominate increasingly (63% after round 1, 98% after round 3). I give no extrapolation to 6 rounds
and no bit figures.

## 3. Structure behind the low-weight cases

### 3.1 GridCycle (`structural.py` [1],[2], `structural.log`)

* **Walk card 0 is always at output 26**: `GC(d)[26] = d[0]` (start seat (2,0), row-major 26).
  More generally, if the first swapped walk index is p, seats s_0..s_{p-1} and their cards are
  unchanged, so `wt <= 52 - p`. These are upper bounds. They explain why late swaps have little
  room to spread, but they do not force weight 2 on their own.
* **Tail lemma (universal).** For *every* deck, swapping walk cards 50 and 51 gives output weight
  exactly 2: seats s_0..s_50 depend only on cards 0..49, and s_51 is the one seat left, whatever
  card 50's step says. Checked on 20000 decks per version, and proved in Lean for every deck (`mixColumns_swap_tail`, §4).
* **Characterisation.** For a swap of walk indices p < q: `wt = 2 <=> the seat sequence is
  unchanged` (held on all 265 200 swaps checked). Distinct cards have distinct step offsets
  (suit mod 4, rank mod 13), so the two walks can only leave seat p (and seat q, unless q = 51) for
  the same next seat through an overflow. Observed mechanisms (v9, 5786 weight-2 cases):
  both overflow to the same seat at p and at q, 4667; both overflow at p and q = 51, 940; mixed
  (one steps onto a free target, the other overflows onto that same seat, which desynchronises the
  marker t), the remaining 179. v8 has the same shape, with 15582 cases.
* **Why B3 (v9) helps but does not close it.** In v8 the overflow scan ignores the target, so any
  two blocked cards overflow to the same seat. In v9 the scan starts at the blocked target's
  column `c + rank`: two **same-rank** cards give the same scan whenever both are blocked (16% of
  v9 weight-2 cases are same-rank pairs, against a 5.9% baseline). Other pairs coincide whenever no
  free seat lies between the two start columns in the marker row, which is common late in the
  walk when few seats are free. Net effect: the rate of weight-2 swaps drops from 12.0% to 4.3%.
* **K♣ always overflows** (step (0, 13 ≡ 0) targets its own seat), and **K♣/K♠ collide at the
  second seat** (`seat2_inj` in `GridCycle.lean`). That is why the p = 0 minimum-weight witness is
  a K♣/K♠ swap, and why K♣ appears in most early-walk witnesses.

### 3.2 SumRanks: exact swap classification (`structural.py` [3])

Swap the cards a, b at column-major seats i, j (rows i mod 4, j mod 4). Let w9(x) = rank + suit
≡ x + 1 (mod 4) and w8(x) = rank. Then (all 530 400 swaps checked per version, no exceptions):

| case | v9 weight | v8 weight |
|---|---|---|
| same row, colW(a) ≡ colW(b) (mod 4) [v9: a ≡ b mod 4] | 2 | 2 |
| same row, otherwise | 8 | 8 |
| different rows, same rank, same column after the row stage | 2 | 2 |
| different rows, same rank, different columns after the row stage | **8** | **2** |
| different rows, different ranks | >= 26 (random min 30, search min 26) | same |

This is the SumRanks side of the v8 -> v9 fix: in v8 every same-rank swap is invisible to SumRanks.

Why this holds (proof idea):
1. Same row: the row sum is unchanged, so the rotation is unchanged, and a, b land in columns x ≠ y
   of the same row. Column x's weight sum changes by colW(b) - colW(a) (mod 4). If that is 0, both
   columns rotate exactly as before, giving weight 2. Otherwise columns x and y each rotate by a new
   amount. The column still holds 4 distinct cards and b is new to column x, so all 4 cells differ
   in each column, giving weight 8.
2. Different rows, same rank: both row sums are unchanged. If a and b share a column after the row
   stage, that column's multiset is unchanged, giving 2. Otherwise each of the two columns gains a
   card with the same rank and a different suit, so colW changes by (suit difference) ≢ 0 (mod 4)
   in v9, giving 8, and by 0 in v8, giving 2.
3. Different rows, different ranks: the rank difference is nonzero mod 13, so rows r1 and r2 both
   rotate by a new amount. Every one of their 26 cells then differs after the row stage (distinct
   cards, or the foreign card b/a). Every column therefore differs from the original exactly in
   rows r1 and r2. If a column keeps its shift, exactly 2 cells differ. If its shift changes, a cell
   agree only if a card sits in row r1 or r2 of the column in one deck and in a different row in the
   other. The row stage keeps cards in their input row, so that card must be b (row r2 before the
   swap, row r1 after it) or a. So at most 2 cells of that column agree and at least 2 differ. That is 13 columns x 2 = **26**, and the search reaches 26.

### 3.3 One round (`structural.py` [4])

Among the SRGC weight-2 events (1349 in v9, 6782 in v8, over 400 decks), the SumRanks stage was
itself weight 2 in every case (counted in `structural.log`; GC is a bijection on decks, so in
principle a heavier SumRanks difference could map to weight 2, but none was seen). GridCycle then contributed through the double-overflow coincidence
(most cases), through q = 51 (the last walk card), or through the tail pair (50, 51). In v9 the
SumRanks classes are only "same row with a ≡ b mod 4" and "same rank, same column". This is why
only those two value relations survive a round (§2).

## 4. Can a branch-number-style bound be proven?

For every layer measured (GC, SR, SR→GC, one keyed round, for every key), the floor 4 is
attained. For v9 multi-round, this PR's searches have witnesses up to 4 rounds for one key only;
they found none at 5 rounds or for the full encrypt. A random bijection would be expected to have
about 1326²/2 ≈ 8.8e5 swap→swap pairs, so 4 is expected there too, but these searches do not
exhibit one. The separate related-plaintext search in
[PR #86](https://github.com/hacker6284/cryptoys/pull/86) found 14 K♣↔Q♥ swap→swap pairs on the
full v9 encrypt under random real keys (about 3.5e-8 per pair).

The floor and GridCycle's tightness are now proved in Lean; the characterisations T2 and T3 below
remain open.

**Proved** in `DoubleDealSecurity/BranchNumber.lean`
([PR #84](https://github.com/hacker6284/cryptoys/pull/84)): T0, T1 and seat 26, for v9 and
the frozen v8 model.

```lean
namespace DoubleDeal.Security
-- weight = Mathlib `hammingDist a b` (seats where a and b differ); `swapAt m i j` = m ∘ Equiv.swap i j

/-- (T0) Trivial floor: distinct decks differ in at least 2 seats ... -/
theorem two_le_hammingDist {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b) (h : a ≠ b) :
    2 ≤ hammingDist a b
/-- ... so any map that keeps decks and separates them has branch number ≥ 4. -/
theorem four_le_branch {F : (Fin 52 → Nat) → (Fin 52 → Nat)}
    (hdeck : ∀ m, IsDeck m → IsDeck (F m))
    (hsep : ∀ {a b : Fin 52 → Nat}, IsDeck a → IsDeck b → a ≠ b → F a ≠ F b)
    {a b : Fin 52 → Nat} (ha : IsDeck a) (hb : IsDeck b) (h : a ≠ b) :
    4 ≤ hammingDist a b + hammingDist (F a) (F b)

/-- (T1) GridCycle tail lemma: for every deck, swapping walk cards 50 and 51 moves exactly
    two output seats, so GridCycle's branch number is exactly 4. -/
theorem mixColumns_swap_tail (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist (mixColumns m) (mixColumns (swapAt m 50 51)) = 2
theorem mixColumns_tail_branch (m : Fin 52 → Nat) (hm : IsDeck m) :
    hammingDist m (swapAt m 50 51) +
      hammingDist (mixColumns m) (mixColumns (swapAt m 50 51)) = 4
/-- (T1') Walk card 0 always lands at output seat 26 (corollary of the generic
    `scoop_gridW_seat26`, for any chooser that starts at `asStart`). -/
theorem mixColumns_seat26 (m : Fin 52 → Nat) : mixColumns m 26 = m 0
-- v8 twins: v8_mixColumns_swap_tail, v8_mixColumns_tail_branch, v8_mixColumns_seat26
end DoubleDeal.Security
```

**Open** (proposed statements, not proved):

```lean
namespace DoubleDeal.Security

/-- (T2) Weight 2 iff the seat walk is unchanged. -/
theorem mixColumns_swap_two_iff (m : Fin 52 → Nat) (hm : IsDeck m) {i j : Fin 52} (hij : i ≠ j) :
    hammingDist (mixColumns m) (mixColumns (swapAt m i j)) = 2 ↔
      ∀ n : Fin 52, walkSeat (swapAt m i j) n = walkSeat m n

/-- SumRanks on decks (column-major lay/scoop), v9. -/
def sr9 (m : Fin 52 → Nat) : Fin 52 → Nat := scoopColumnMajor (sumRanksV9 (layColumnMajor m))

/-- (T3) SumRanks swap classification, v9: the weight is 2, 8, or at least 26. -/
theorem sr9_swap_weight (m : Fin 52 → Nat) (hm : IsDeck m) {i j : Fin 52} (hij : i ≠ j) :
    let w := hammingDist (sr9 m) (sr9 (swapAt m i j))
    w = 2 ∨ w = 8 ∨ 26 ≤ w
theorem sr9_swap_cross (m : Fin 52 → Nat) (hm : IsDeck m) {i j : Fin 52}
    (hrow : cmRow i ≠ cmRow j) (hrank : rank (m i) ≠ rank (m j)) :
    26 ≤ hammingDist (sr9 m) (sr9 (swapAt m i j))
/-- Only same-rank or ≡ (mod 4) value pairs can pass SumRanks as a swap (v9). -/
theorem sr9_swap_two_imp (m : Fin 52 → Nat) (hm : IsDeck m) {i j : Fin 52} (hij : i ≠ j)
    (h : hammingDist (sr9 m) (sr9 (swapAt m i j)) = 2) :
    rank (m i) = rank (m j) ∨ m i % 4 = m j % 4

end DoubleDeal.Security
```

Proof plan and effort for the open statements, reusing `Walk.lean` (`placeW`, `seatW_injective`,
`seatW_surj`, `gridW_at_seat`), the prefix lemmas of `BranchNumber.lean`, and the
`rowRotate_apply` / `colRotate_apply` / `grid_inj` lemmas in `SumRanks.lean`:

* T2: same infrastructure as T1. (⇐) comes from `gridW_at_seat`. (⇒) holds because weight 2 forces
  every other card to its old seat, and seat injectivity then gives the whole sequence. About 1-2
  days.
* T3: case split on rows and ranks, rotation arithmetic, and the column-coincidence count for the
  26 bound (the hard part: a Finset card bound summed over 13 columns). About 4-7 days,
  400-700 lines. Parametrise over `colW` to get v8 in about +1 day.
* Tightness witnesses per layer (single swaps, e.g. those in `witnesses.json`) can be checked by
  `decide!` on single layers, as the existing `mixColumns_KC_KD_fails` does; T1 already makes
  GridCycle tightness universal. I would not attempt kernel checks of the multi-round trails (the
  v8 README records that full-encrypt `decide` exceeded 14 GB).

T2 and T3 together are about 1-2 weeks. With T0/T1 they would give honest, precisely scoped
statements: "branch number 4 (trivial, tight) for GridCycle, with an exact description of when
weight 2 happens"; "SumRanks swap weights are in {2, 8} ∪ [26, 52], with exact class conditions".
None of them is a wide-trail bound.

## 5. Observations

* Every layer only moves cards, and the data-dependent amounts are sums over a row, column or
  walk prefix. A swap that leaves the relevant sums (mod 13 / mod 4), or the overflow outcome,
  unchanged is invisible beyond the two seats. The trivially tight branch number follows from that
  "sum-invariant swap" structure. It is not tied to one layer.
* In v9 the weight-2 channel through a round needs both an SR-invisible value pair (same rank, or
  a ≡ b mod 4: 390 of 1326 value pairs) and a GC overflow coincidence. Because the pair's values
  are carried along, the per-round events compound far better than independence would predict
  (P(round 2 | round 1) = 1.2e-2 vs 2.6e-3 for one round).

## Files

`common.py` (harness), `measure.py` -> `measure.log`, `structural.py` ->
`structural.log`, `search.py` -> `search.log` / `search2.log`, `multiround.py` ->
`multiround.log`, `trail_search.py` -> `trail_v9_4.log`, `trail_v9_5.log`, `trail_v9_enc.log`,
`witnesses.py` -> `witnesses.log`, `witnesses.json`.
Port check: `python3 ../selftest.py` (CI). Reproduce: `python3 measure.py 1000 2026; python3 structural.py;
python3 search.py 120 777; python3 search.py 480 991 'q<=|4 keyed|5 keyed|encrypt';
python3 multiround.py 3000 5; python3 trail_search.py 9 4 600 8 31; python3 trail_search.py 9 5 1200 4 51;
python3 trail_search.py 9 enc 1200 4 61; python3 witnesses.py`. The searches are time-budgeted, so
reruns find different (verified) witnesses.
