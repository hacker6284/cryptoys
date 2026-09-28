# DoubleDeal v10 GridCycle: AES-parity analysis (Phase 1, analysis only)

> **Phase 2** (a cheap overflow rule under the 1/64 bar: ghost finger + "the blocker sends you",
> worst pair 1/161 at +16% seat checks) is in [PHASE2.md](PHASE2.md).
> **Phase 3** ("bump the occupant"): every bump variant is non-invertible (explicit colliding decks),
> see [PHASE3.md](PHASE3.md).

**Kind:** analysis. Nothing here is a theorem, a spec change or a security claim. No bit-security
figures. The normative GridCycle is SPEC §3.5 / §4.4 and `mix_columns` in
`primitives/cipher/doubledeal/doubledeal.sudo`; the Lean model is `mixColumns` in
`proofs/doubledeal/security/DoubleDealSecurity/GridCycle.lean`. v10 changed only SumRanks, so
GridCycle is byte-for-byte the v9 layer. The fix options below are proposals for Zachary's decision;
nothing here changes the cipher.

Heavy runs stay out of CI: `run_all.sh` reproduces everything (roughly 20–30 CPU-minutes on 8 cores).
`xcheck.py` checks the C model (`gc.h`) against the repo's Python port `security/checks/ddport.py`,
which CI already checks against the v10 vectors (2000 random decks, 0 mismatches).

## 1. What GridCycle does

Input: a 52-card packet `d` (the column-major scoop after SumRanks and ShiftRows). Output: a packet,
the row-major scoop of a 4×13 grid that is filled by a **walk**:

* Card `d[0]` goes to the start seat (2, 0). So **`GC(d)[26] = d[0]` always** (proved: `mixColumns_seat26`).
* After placing card `x` at (r, c), the target seat for the next card is
  `((r + suit x) mod 4, (c + rank x) mod 13)` with GridCycle suits ♣0 ♥1 ♠2 ♦3 and rank A=1 … K=13.
  If the target is free, the next card goes there.
* Otherwise (overflow): scan the row named by the marker `t` (starts at ♣ = row 0), from the
  blocked seat's column `c*` rightward with wrap, and take the first free seat. Then advance the marker.
  If that row is full, advance the marker and scan the next row the same way.

Data dependence: the seat of card `i` is a function of cards `0..i-1` only (the step reads the
**previous** card, and the overflow reads the previous card's rank through `c*`, the marker and
the occupancy). The layer is therefore "forward-triangular":

* a difference whose first changed walk index is `p` leaves seats `0..p-1` and their cards alone, so
  the output difference weight is at most `52 − p`;
* swapping walk cards 50 and 51 **always** moves exactly two output seats (proved:
  `mixColumns_swap_tail`), because seat 50 is fixed by card 49 and seat 51 is the last free seat.

The target seat is close to a uniform random seat, so the overflow rate at walk index `i` is about
`i/52` (measured: 0.02 at i=1, 0.50 at i=26, 0.98 at i=51). **Half of all placements (25.6 of 51)
are overflows** (`structure.log`). In an overflow, the only card information used is the rank, through
`c*`. The suit is ignored.

**The known one-step K♣/K♠ collision.** K♣ steps by (0, 13 ≡ 0): its target is its own seat, so K♣
**always** overflows. As walk card 0, K♣ (from (2,0), blocked) overflows into row 0 from column 0,
giving (0,0) and advancing the marker. K♠ steps by (2,0) from (2,0) to (0,0), which is free. So both
put card 1 at (0,0); this is the only collision of `seat2` (`seat2_inj`). After that the two walks
agree until the next overflow, where their markers differ by one. For the swap of the first two
cards (K♣, K♠, … vs K♠, K♣, …) that happens at once: the third seat is (1,0) vs (0,1).

## 2. Which metric plays the role of MixColumns' guarantee

MixColumns is linear with branch number 5. A difference in one byte of a column always turns into
differences in all four bytes of that column: a sparse difference can **never** stay sparse. That is
the property the wide-trail argument uses, and it holds with probability 1.

Three candidate metrics for a 52-card permutation layer:

1. **Min branch number** (min over pairs of changed input cells + changed output cells). For any
   bijection on decks it is at least 4 (two decks differ in ≥ 2 seats). **A uniformly random
   bijection also has branch number 4** (about 1326²/2 swap→swap pairs are expected among 52!·1326
   swap pairs; see `security/checks/branchnum/NOTES.md` §4). So this metric is at its floor for every
   layer, ideal or not, and cannot tell a good diffusion layer from a bad one. GridCycle = 4 (proved).
2. **Diffusion** (distribution of output weight for a single-swap input). This is informative, but
   averaging hides the worst case.
3. **Swap survival**, the same metric used for SumRanks: for a transposition τ = (a b) of card
   values, `s(τ) = P_d[GC(τ∘d) = τ∘GC(d)]` over uniform decks, and its worst case over τ. Each card
   occurs once, so τ∘d is d with two positions swapped. `GC(τd) = τGC(d)` is exactly the event that
   the **minimal** (weight-2) difference comes out of the layer still minimal, carrying the same
   two cards. Within a single deck, "output weight 2" and "the seat walk is unchanged" and
   "commutes with τ" coincide (T2 characterisation; spot-checked: 0 mismatches in 520k checks).

**Choice: metric 3 (worst-case value-pair swap survival) as the primary metric, with metric 2
as a secondary diffusion profile.** Reasons:

* It is the probabilistic form of MixColumns' guarantee ("a minimal difference does not stay
  minimal"). The AES counterpart value is **0**.
* It is the quantity that compounds across rounds. Compose moves positions by the secret key but
  keeps card values, so a trail keeps its two card values and gets fresh, key-random positions each
  round. With independent uniform round keys, the input to each round is uniform, so the per-round
  survival of a fixed value pair multiplies exactly along a swap-only trail. That is how the v8 and v9
  breaks worked (same value pair, round after round).
* It is directly comparable with the per-layer number already used for SumRanks: worst measured
  9/1105 ≈ 1/123 (same-suit 3-cycle), proved ≤ 1/64 (PR #93).

**Proposed parity bar:** worst-case pair survival ≤ 1/64, the bar SumRanks is held to. True AES
parity (0) is **impossible for any single-pass walk layer**: whenever the two cards sit at walk
positions 50 and 51 the swap survives (tail lemma), so every pair has `s(τ) ≥ 2·50!/52! = 1/1326`.

## 3. Measurements, v10 GridCycle alone

Swap survival over all 1326 value pairs, 200 000 uniform decks per pair (`survival.c`,
`survival_value.log`; 95% Wilson intervals):

| | value |
|---|---|
| worst pair | **K♣↔K♦ 0.2620** [0.2601, 0.2640] ≈ 1/3.8 |
| next | K♣↔K♥ 0.251, K♣↔K♠ 0.250, K♣↔Q♥ 0.183, Q♣↔Q♦ 0.160, Q♣↔K♣ 0.156 |
| mean over all pairs | 0.0434 ≈ 1/23 |
| median pair / best pair | 0.031 / 0.0139 (A♣↔8♠) |
| pairs above 1/64 | **1311 of 1326** |
| by class (mean) | same rank 0.127, same suit 0.039, other 0.038 |

For comparison: SumRanks alone has worst 1/123 measured and ≤ 1/64 proved. Its worst **transposition**
is 1/221, and 0 pairs are above 1/64. GridCycle's worst pair is about 32× SumRanks' worst relabelling
of any shape (58× its worst transposition). Even GridCycle's best pair (1/72) is above SumRanks'
measured worst.

3-cycles (`cycles3.c`, `cycles3.log`): every one of the 44 200 3-cycles was screened at 400 decks, and
the screen's top 10 were re-run at 100 000 decks. Worst refined: (K♣ K♠ K♦) 0.086; the mean over all
3-cycles is 0.0076. The screen is noisy, so a 3-cycle outside the refined ten could be a little higher;
none screened above 0.11. Among the shapes checked, transpositions are the worst case, as expected:
every moved card needs its own coincidence.

Position swaps (`survival_pos.log`, the diffusion profile; `structure.log`):

* Swapping walk positions (50, 51) survives with probability **1** (proved). (49, 50) and (49, 51)
  survive at 0.85, (48, 51) at 0.76, and so on. The mean over position pairs is 0.043.
* A random position swap gives mean output weight 32.8; two independent decks differ in 51 seats on
  average. P(weight ≤ 2) = 0.043, P(≤ 8) = 0.075, P(≤ 16) = 0.144. A first changed index `i` caps the
  weight at `52 − i`.
* Seat 26 always holds input card 0. For every other index, where a card lands is close to uniform
  (largest P(seat | index) ≈ 0.039, against 1/52 = 0.019).

## 4. Worst cases and the mechanism

**K♣↔K♦ (≈ 26%).** K♣ always overflows, scanning from its own column. K♦ steps by (3, 0), to the seat
one row up in the same column. If that seat is occupied, K♦ overflows from the **same column with
the same marker**, which is exactly where K♣ goes. So the walk is unchanged whenever the seat above
K♦/K♣ is occupied at both of their placements. `mechanism.c` checks this sufficient condition over
10⁶ decks. The condition holds on 25.83% of decks with 0 exceptions (it never holds without survival),
and it accounts for 98.7% of all survivals. The rest are cases where K♣'s overflow lands exactly on
K♦'s free target and the marker desync happens not to matter later.

Paper estimate: a given seat is occupied at walk time `i` with probability about `i/51`, and the two
cards' positions are nearly independent and uniform, so the survival is about E[X·Y] = 1/4 for X, Y
uniform on [0, 1].

The general causes are:

1. **The suit is ignored in overflow.** Two blocked cards of the same rank scan the same row from
   the same column and land on the same seat. That is why same-rank pairs average 12.7%. K♣'s
   self-block makes the K♣↔K\* pairs the worst.
2. **Adjacent scan starts.** Two blocked cards whose `c*` differ by one column collide whenever the
   seat between them is occupied (Q♣↔K♣, J♣↔Q♣, …).
3. **Late-walk convergence.** Overflow happens in half the placements, and late in the walk only a
   few seats are free, so the scan outcome hardly depends on the card.

**Invariants and linear structure.** No exact symmetry: `mixColumns_commutes_iff_id` (proved) says only
the identity commutes on every deck. Without overflow the seats are prefix sums,
`(2 + Σ suit, Σ rank) mod (4, 13)`. That is linear, but overflow starts early: P(first overflow ≤ 8) = 0.53.
Seat 26 = input 0 is the only fixed point. Nothing else structural was found beyond items 1–3 and the
triangular prefix property.

## 5. At the round level (does this break the cipher? No)

One unkeyed v10 round (lay, SumRanks, ShiftRows, scoop, GridCycle), 400 000 decks per same-suit pair
(`round.c`, `round.log`). Only same-suit pairs pass v10 SumRanks: other pairs had 0 hits in 200k decks
per pair (`analysis/v10-sumranks`). Compose commutes with relabellings, so the unkeyed round equals every
keyed round for this metric.

* Mean SumRanks-stage survival 4.53e-3 (≈ 1/221, matches the SumRanks notes).
* GridCycle passes **15%** of the swaps SumRanks lets through.
* Worst round Q♣↔K♣ **1.40e-3** [1.3e-3, 1.5e-3], which matches the earlier `allpairs_W.log` 1.4e-3.

Under independent uniform round keys a swap-only trail of 5 full rounds and the final round has
probability (1.4e-3)⁵ × (1/221) ≈ 2e-17 for the worst pair. That is far too small to distinguish
v10 with any realistic amount of data, and it matches the existing heuristic product. **So this is
a per-layer parity failure, not an attack on v10.** The repo's deprecate-first rule is not triggered
by anything here, and no deprecation proposal is made.

## 6. Verdict: (b), GridCycle is far below the parity bar

GridCycle's worst swap survival is 0.262. The bar SumRanks meets is ≤ 1/64 (0.0156), and the AES
MixColumns counterpart is 0. 1311 of 1326 pairs are above 1/64. Reproducible witness: any random decks
with the pair (K♣, K♦), e.g. `./survival value 2000 1`, or `./mechanism 1000000 9` for the mechanism
count.

A positive bound for v10 GridCycle is not worth formalising: any true upper bound is ≥ 0.262.

### Fix options (proposals only; the algorithm decision is Zachary's)

All options keep the step rule, the start seat, the marker chip and row-major scoop. They change only
what happens on overflow, and each overflow still depends only on (previous card, its seat, the
occupancy, the marker). So the existing inverse ("replay with visited marks") works unchanged. The
round trip was checked for every variant: 0 failures in 100 000 decks each (`variants_cost.log`).

| option | overflow rule | GC worst pair | GC mean | pairs > 1/64 | round worst | seats inspected per overflow |
|---|---|---|---|---|---|---|
| v10 | marker row, first free from c* | 0.262 (K♣↔K♦) | 0.043 | 1311 | 1.40e-3 | 6.1 |
| **A** "suit picks the row" | row = marker + suit; first free from c* | 0.180 (Q♣↔K♣) | 0.013 | 312 | 1.54e-3 | 7.0 |
| **B** "count on one hand" | row = marker + suit; from c*, count k empty seats, k = A..5 → 1..5, 6..T → 1..5, J Q K → 1 2 3 | 0.038 (2♣↔K♣) | 0.0056 | 37 | 7.3e-4 | 17.7 |
| **B′** "count to seven" | as B with k = ((rank − 1) mod 7) + 1 | 0.021 (A♣↔8♣) | 0.0054 | 6 | 2.45e-4 | 24.7 |
| **C** "count the rank" | as B with k = rank (A=1 … K=13); counting continues into the next rows and wraps | **0.0137 (A♣↔K♣)** [0.0129, 0.0145] | 0.0052 | **0** | 3.0e-4 | 47.8 |

(GC columns: 20 000 decks per pair for A and B′, 80 000 for B and C. Round: 400 000 decks per same-suit pair.)

* **A** is the cheapest change: add the card's suit to the marker when picking the row. It removes the
  same-rank collisions, but adjacent-column collisions remain, and the round worst does not improve.
  Not recommended on its own.
* **B / B′** reuse the "count along the row" gesture, with a small count (fingers of one hand, or a
  week). Why B uses 5 rather than 4: with k = rank mod 4, A and K get the same count and start in
  adjacent columns, which measured 0.136 (variant 5). Any modulus that divides 12 has that problem.
* **C** is the only option measured under the 1/64 bar, and it cuts the worst round by 4.6×. The cost is
  about 8× the overflow scanning of v10 (≈ 1230 seat inspections per GridCycle, against ≈ 155).
* Rejected variants, measured (`variants_value.log`): scanning the blocked seat's own row (A♣↔K♣ 0.97),
  re-stepping with the same card (K♣↔K♠ 0.29), and a row-local "rank mod #free" (0.079).

Whatever the rule, a single-pass walk keeps the tail floor (every pair ≥ 1/1326, and the (50, 51)
position swap always survives). Beating that needs a second pass or a different layer. That was not
measured here.

## 7. What could be proved in Lean (if wanted), with rough effort

For the break, as the mechanism behind the numbers:

```lean
namespace DoubleDeal.Security
/-- Sufficient condition for K♣↔K♦ to commute with GridCycle on one deck: at each walk index
    n < 51 holding K♣ or K♦, the seat one row up from walkSeat m n is among the seats already
    used. (Measured to hold on 25.8% of decks.) -/
theorem mixColumns_rel_KC_KD_of_blocked (m : Fin 52 → Nat) (hm : IsDeck m)
    (h : ∀ n : Fin 51, (m n.castSucc = KC.val ∨ m n.castSucc = KD.val) →
      ∃ k ≤ n.val, walkSeat m k = upSeat (walkSeat m n.val)) :
    mixColumns (rel (swap KC KD) m) = rel (swap KC KD) (mixColumns m)

/-- Walk floor: every transposition commutes with GridCycle on at least 52!/1326 decks
    (the decks with a, b at walk positions 50, 51; from `mixColumns_swap_tail`). -/
theorem mixColumns_swap_survival_floor (a b : Fin 52) (hab : a ≠ b) :
    Nat.factorial 52 / 1326 ≤
      (Finset.univ.filter fun d : Equiv.Perm (Fin 52) =>
        mixColumns (rel (swap a b) (deckOf d)) = rel (swap a b) (mixColumns (deckOf d))).card
end DoubleDeal.Security
```

Names such as `upSeat` and `deckOf` are illustrative; the statements would be adapted to the existing
`Walk.lean` / `SumRanksDP` counting infrastructure. Estimated effort:

* the sufficient-condition lemma: 2–3 days, reusing `walkW_rel_iff`, `mixColumns_rel_iff_walk`,
  `gridW_at_seat`;
* the floor: 1–2 days, reusing T1 and the SumRanksDP deck-counting lemmas;
* a Lean **lower bound** matching the 26% (counting decks where the seat above is occupied) would
  need an occupancy-distribution argument: weeks, and not recommended.

For a fixed GridCycle, a Lean **upper** bound in the style of SumRanksDP (e.g. option C ≤ 1/64) would be a
new probabilistic argument about a data-dependent walk. The SumRanks proof was about 4 400 lines, and
this would likely be larger. Guess: several weeks, with real risk. Stating a measured bound and proving
only structural lemmas is the cheaper honest route.

## Files

| file | what |
|---|---|
| `gc.h` | C model of v10 `mix_columns` (walk), RNG |
| `xcheck.py` | C == `ddport.mix_columns` on 2000 random decks |
| `survival.c`, `agg.py` → `survival_value.log`, `survival_pos.log`, `runs/value_*`, `runs/pos_*` | per-pair swap survival (value and position) |
| `structure.c` → `structure.log` | landing distribution, overflow profile, diffusion by index |
| `cycles3.c` → `cycles3.log` | all 3-cycles (screen, then refine top 10) |
| `mechanism.c` → `mechanism.log` | K♣↔K♦ sufficient condition |
| `variants.c`, `aggm.py` → `variants_value.log`, `variants_cost.log`, `runs/var*` | overflow-rule variants (fix options), inverse round-trip check |
| `round.c`, `aggr.py` → `round.log`, `runs/round_*` | one v10 round with each variant |
| `build.sh`, `run_all.sh` | build / reproduce |
