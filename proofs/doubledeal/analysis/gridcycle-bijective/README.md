# GridCycle replacement by card-driven bijections (design exploration, analysis only)

**Kind:** analysis and proposal. Nothing here changes the spec, `main` or any other branch, and nothing here is a
security claim. The only reason to replace GridCycle would be convenience: the replacement has to make the proofs
substantially easier (invertibility, Link-2 refinement, T1 commutation / no symmetry, survival and diffusion
bounds), stay playable by hand, and not lose much strength. Being more AES-like is not a goal.

**Baseline.** This branch is cut from `origin/main`, which is still v10. The v11 GridCycle (ghost finger,
blocker-steered scan, finger nudged by the blocker's step) lives on `doubledeal-v11`. `layers.h` re-implements it
from the v11 SPEC §3.5 and `xcheck.py` checks it against that branch's `security/checks/ddport.py` (1000 decks,
0 mismatches, `logs/xcheck.log`). It reproduces the v10-gridcycle PHASE6 numbers: mean swap spread 33.93, and
6♣↔K♣ survives at 0.0046 ≈ 1/217 at 10⁶ decks (PHASE6's worst pair: 0.0049 ≈ 1/205 at 2·10⁵).

## Verdict (short)

* **One sketch is worth a prototype: PassMix-F (§3.3).** It is a PassKey-style pass over the packet: each card in
  turn cuts the hand and the key pile, and then goes on top of the key pile. There is no grid, no occupancy and no
  mental sums. Each step is a bijection, read back from the card on top of the key pile, so **both** inverses come
  from the same step lemma. v11 still has `mix ∘ invMix = id` open. Proofs follow a template that already exists
  (`PassKey.lean`, 475 lines, proves both inverses). Survival gets a **paper proof of an exact closed-form lower
  bound** for every pair, e(e−1)/2652. It is 30/2652 ≈ 1/88 for the worst pairs and matches measurement to four
  digits. Diffusion is far above the one-pass ceiling: mean spread 48.9 against v11's 33.9 and a ceiling of 35.3.
  Through one unkeyed round it complements SumRanks: **0 survivals in 66.3M pair-decks**, where v11 has a mean of
  1.35·10⁻⁵.
* **It does not make everything easier, and on one point it is weaker.**
  * Its worst single swap through the layer alone is ≈ 1/88. That is under the 1/64 bar but 2.4× worse than v11's
    ≈ 1/205–1/217. The optional edge rule (§3.4) brings it to 1/1326, at +28% cutting and one more rule clause.
  * The survival **upper** bound is still open. It needs a bound on a rare "reconvergence" term, and the natural
    lemma that would remove that term is false (§4).
  * The T1 proof and the Link-2 refinement are about the same amount of work as v11's, and v11's are already paid
    for.
  * The proved v10Sym case of the covariant conjecture relies on GridCycle's fixed seat (card 0 always lands on
    seat 26). PassMix has no fixed seat, so that argument would have to be redone.
* **The grid sketches do not help.**
  * PivotRoll (single-card reads, rows and columns turned by the card at a fixed seat) has trivial proofs but lets
    swaps through ≈ 86% of the time.
  * TwinSum (a second SumRanks-style chain) needs every SumRanks-scale proof again, including the ~3300-line
    survival counting proof. It is ≈ 2× weaker per layer than v11 and costs another ~200 mental operations.
  * Reusing SumRanks verbatim is fatal (it shares v10Sym). Reusing PassKey F verbatim is fatal too: a
    suit+rank collision lets 2♥↔A♠ through 89% of the time.

Plainly: no sketch makes the proofs *substantially* easier across the board. PassMix-F makes invertibility and
survival (lower bound, and a route to an exact value) substantially easier, and it makes the hand rules simpler.
Refinement and T1 stay about the same. Recommendation (proposal only): prototype PassMix-F (model + both inverses
+ the closed form in Lean, sudo + vectors) only if a proved survival statement for the mixing layer or the right
inverse is wanted. Otherwise keep v11. Replacing v11 purely for proof convenience is not justified until the
reconvergence term (§4) is bounded on paper, because that is the one proof that would make the switch clearly
pay.

## 1. Facts that hold for every sketch

* **F1 (survival = unchanged seat permutation).** If a layer moves cards by a seat permutation P chosen from the
  cards, then for a swap τ, `L(τd) = τL(d)` ⇔ `P(τd) = P(d)`. The reason: both sides are the same deck read
  through two seat maps, and a deck is injective. The v10-gridcycle "T2 characterisation" is the same fact.
  It is why every construction here is analysed through "which choices can change".
* **F2 (every card must be read).** Two cards that no choice ever reads swap through with probability 1. The
  17-read PivotRoll: 0.86 worst, 0.56 mean.
* **F3 (symmetry trap).** Compose is positional, so a mixing layer that commutes with a nontrivial `v10Sym`
  element makes `encrypt` v10Sym-equivariant under **every** key. SumRanks laid row-major (SRDUP) commutes with
  all 51 of them (`logs/sym.log`). Every other sketch commutes with none of the 3743 structured relabellings
  tested (suit permutation × affine rank map).
* **F4 (sum collisions).** Putting suit and rank cuts on the *same* pile adds them, so pairs with equal suit+rank
  collide. PassKey F used as the mixer lets 2♥↔A♠ through at 0.888 (`logs/surv.log`, layer PASSK).
  *Side note, not a claim:* the same property holds for F in the key schedule, so K and τK pass to τ-related
  round keys with probability ≈ 0.89 per pass for such pairs.
* **One-pass ceiling.** Walk layers (v10, v11) never touch the seats of earlier cards, so a swap at position i
  changes at most 52 − i outputs (mean ≤ 35.33). Chained rotations and passes do not have this limit.

## 2. Measurements

Swap survival: value-pair `P[L(τd) = τL(d)]` over uniform decks, all 1326 pairs × 50 000 decks (seed 3); sampled
maxima over 1326 pairs are biased upward, so the worst pairs are refined at 10⁶ decks. Spread: all 1326 position
swaps × 20 000 decks (seed 2), outputs that differ. One round: `L(stem(d))`, stem = v10 SumRanks + ShiftRows,
no key, 1326 × 50 000 (seed 4), with two pairs refined at 2·10⁶.

| layer | worst swap, layer alone | pairs > 1/64 | mean swap survival | spread mean / p1 / share ≤ 4 | one round: mean / refined pairs | hand work per layer |
|---|---|---|---|---|---|---|
| **v11 GridCycle** (reference) | 6♣↔K♣ 0.0046 ≈ **1/217** (10⁶; PHASE6: 1/205) | 0 | 1/283 | **33.93** / 5 / 0.0096 | **1.35e-5** / AS↔JS 4.7e-5, 5♥↔K♥ 5.9e-5 | 51 steps × 2 mod-adds; ~25 blocked: read blocker, 3 adds, scan ≈ 7 seats; lay by walk + row scoop |
| SumRanks v10 alone (reference) | same-suit swap exactly 1/221 (SPEC v10 §7a) | 0 | 1/942 | 46.64 / 12 / 0.0011 | — | — |
| S1 PivotRoll | 0.856 | 1326 | 0.56 | 11.98 / 2 / 0.56 | not run (fails) | 17 reads, 17 turns, lay + scoop |
| S2 TwinSum-GF | 6♠↔6♦ 0.0098 ≈ 1/102 (10⁶) | 0 | 1/774 | 46.97 / 12 / 0.0013 | 3.4e-6 / (max sampled 6e-5) | ≈ a second SumRanks: 104 mod-13 adds, ~104 GF(4) ops, 17 turns, lay + scoop |
| (TwinSum, ℤ₄ columns) | 7♥↔7♦ 0.031 | 26 | 1/600 | 46.95 | — | (zero divisors in ℤ₄) |
| **S3 PassMix-F** | **30/2652 ≈ 1/88.4**, closed form; 6♣↔6♦ 0.0113 at 10⁶ | 0 | 1/2214 | **48.91** / 8 / 0.0032 | **0 in 66.3M** / both 0 in 2·10⁶ (< 1.9e-6) | no grid; 52 cards, 1 compare each; cuts count off 433 cards (8.3 per card), ~3 wrap; no sums |
| S3e PassMix-F + edge rule | **2/2652 = 1/1326**, closed form; 3♣↔K♦ 0.00084 sampled | 0 | 1/270 612 | 49.65 / 10 / 0.0022 | 0 in 66.3M / both 0 in 2·10⁶ | 556 cards counted; one more rule clause |
| S4 PassMix-F twice | T♣↔T♠ 0.000335 ≈ 1/2985 (10⁶) | 0 | 1/70 758 | 50.99 / 48 / 3e-5 | 0 in 66.3M | 2 passes, 866 cards |
| (PassMix, no fallback) | A♦↔K♦ 0.0165; closed form 42/2652 = 1/63.1 | 3 | 1/1064 | 42.45 | — | fails the bar narrowly |
| (PassKey F reused) | 2♥↔A♠ 0.888 | 68 | 1/28 | 48.73 | — | F4 |
| ideal random layer | ≈ 0 | 0 | ≈ 0 | 51.0 | | |

All layers invert (100 000 decks each, `logs/check.log`). Spread by first swapped position (`logs/spread.log`):
v11 falls from 50.1 at i = 0 to 2.0 at i = 50 (the one-pass floor). PassMix-F is flat at ≈ 48.9 for every i, and
SumRanks-style chains stay between 40 and 49. "Min spread 2" still holds for every bijection on decks (the trivial
branch-number floor).

## 3. The sketches

In every sketch, suits are ♣0 ♥1 ♠2 ♦3 (the GridCycle order) and ranks run A=1 … K=13. "Cut k" means move k cards
from the top of a pile to its bottom, counting round the pile if it is shorter than k. The code for each sketch is
in `layers.h`, and `xcheck.py` has an independent Python version with its inverse.

### 3.1 S1 PivotRoll (the cheap end: single-card keys at fixed seats)

*Rule.* Lay the packet row-major. For rows 1, 2, 3, 0: turn row i left by the rank of the card now at
(i−1, column 0). For columns 1…12, 0: turn column j down by the suit of the card now at (row 0, j−1). Scoop
row-major.
*Hand.* 17 glances, 17 turns, lay + scoop.
*Decrypt.* Undo the columns in the order 0, 12, …, 1, then the rows in the order 0, 3, 2, 1. Each turn reads a
seat that no later step moves, so the reading is always available.
*Proofs.* Invertibility is SumRanks' chained-rotation lemma with single-cell amounts. Refinement and T1 would be
small, a few hundred lines.
*Strength.* 35 of the 52 cards are never read, so swaps survive 56% of the time on average (F2). **Rejected.** It
is included to show that "cheap reads at fixed seats" cannot meet the survival bar.

### 3.2 S2 TwinSum-GF (a second chained-rotation layer)

*Rule.* Lay the packet row-major. Rows 1, 2, 3, 0: turn row i left by `(Σ_j (13−j)·rank(x_j) + rank(x_0)) mod 13`
of the row above, as it is now. Adding rank(x₀) makes the weights sum to 1 mod 13, which breaks the rank-shift
symmetry. Columns 1…12, 0: turn column j down by `V′(left) ⊕ S(own)`. Here V′ takes the GF(4) suit labels of the
left column with weights (w², 1, w, w²), which sum to w² ≠ 0 and so break the XOR symmetry. S is the XOR of the
column's own four labels, as in SumRanks. Scoop row-major.
*Hand.* The same gestures as SumRanks (two running totals, the GF(4) card table), a second time.
*Decrypt.* As SumRanks: columns in reverse order, then rows.
*Proofs.* Invertibility and refinement reuse the SumRanks pattern (`SumRanksV10.lean` 514 lines, `SumLink.lean`
1117 lines), largely re-done for the new turn functions. T1 needs a `SumRanksV10Iff`-style characterisation
(421 lines). A survival bound would mean redoing the SumRanks DP counting proof for new constants
(`SumRanksDP/` ≈ 3300 lines).
*Strength.* Worst swap 1/102, same-rank swaps (GF(4) columns see only 4 outcomes). Mean spread 46.97.
*Verdict.* No proof gets easier and it is weaker than v11. **Not recommended.** The ℤ₄ version (column weights
1, 1, 2, 3) is worse, 1/32, because 2·2 = 0 in ℤ₄.

### 3.3 S3 PassMix-F (proposed prototype)

*Rule.* Hold the packet as the **hand**. The **key pile** starts empty. Repeat until the hand is empty: take the
top card C off the hand.
* If rank(C) is **less than** the number of cards left in the hand: cut the hand by rank(C), and cut the key pile
  by suit(C).
* Otherwise (fallback): cut the key pile by rank(C), and cut the hand by suit(C).

Then put C on top of the key pile. The key pile is the output.

*Hand.* 52 cards, each with one comparison and two cuts. The comparison is physical: can you count rank(C) cards
and still have one left? Wrap-around counting only happens on piles of fewer than 4 cards (≈ 3 cuts per pass).
There are no sums and no grid, and it is the same gesture set as PassKey. Cost: 433 cards counted off per pass
(8.3 per card, `logs/passformula.log`), against v11's 52 walk placements, ~102 mod-adds, ~25 blocked scans of
≈ 7 seats, and the row-major scoop.

*Decrypt.* Lift the top card C off the key pile (it is always the last card placed). Let n be the size of the hand
you are rebuilding. If rank(C) < n, undo the suit cut on the key pile and the rank cut on the hand; otherwise undo
the rank cut on the key pile and the suit cut on the hand. Undoing a cut moves that many cards from the bottom back
to the top. Put C on top of the hand. The branch reads only C and the pile sizes, which both sides know. A
walkthrough with decryption is in `logs/passwalk.log`.

*Proofs, what gets easier.*
* **Invertibility, both directions.** Each step is a bijection on (hand, key) states of the given sizes, and
  PassMix-F is the composition of those steps. `PassKey.lean` already proves `passKey_leftInverse` **and**
  `passKey_rightInverse` for a step of exactly this shape. v11 proves only `invMix ∘ Mix = id`;
  `Mix ∘ invMix = id` is listed as open ("needs image / seat characterization").
* **No occupancy.** Nothing plays the role of `Occ`, `occCount`, the scan lemmas, `chooseSeat?_isSome`, the
  unreachable `fail` branch, or visited-set inverse agreement.
* **Survival on paper** (§4): an exact closed-form lower bound for every pair, and equality with the measurement
  except for a rare reconvergence term.
* **Complement to SumRanks.** For swaps, SumRanks lets through only same-suit pairs (measured: 0 other-class
  survivals in 50M). PassMix-F's closed form is exactly 0 for same-suit pairs, and the measured rate is ≈ 4.5·10⁻⁷
  of reconvergence. So one unkeyed round measured 0 survivals in 66.3M pair-decks.
* **Hand refinement (S7).** The rules are two cuts and one comparison, with no finger, marker, blocker or scan.

*Proofs, what does not get easier.*
* Link-2 refinement is a new loop, about as big as `Mix.lean`. The PassKey refinement lemmas are a close template
  (`Link2/PassKey*.lean`: 2171 lines for F with inverse and transfer).
* T1 "commutes only with the identity" needs a new argument. F1 plus §4's Prop 4 are the tools, but there is no
  fixed seat to anchor it.
* The covariant conjecture's proved v10Sym case uses `mixColumns_at_AS` (card 0 always on seat 26). PassMix has no
  fixed seat. One option, **unmeasured**, is an anchor: keep the first card as the base of the key pile, outside
  the key cuts, so output[51] = input[0] always.

### 3.4 S3e PassMix-F with an edge rule

As S3, with two changes at the ends of the pass:
* While the key pile has fewer than 4 cards (the first four cards), the key pile cannot tell suits apart. So cut
  the **hand** by rank + 13·suit instead, and leave the key pile alone.
* In a fallback step while the hand has fewer than 4 cards, cut the **key pile** by rank + 13·suit and leave the
  hand alone.

The closed-form worst drops from 30/2652 to **2/2652 = 1/1326**, the same size as the one-pass tail floor. Same-rank
and same-suit swaps drop to 0 in closed form. The price is one more rule clause and 556 cards counted instead of
433 (eight cuts of up to 51 cards). Proofs are as S3.

### 3.5 S4 PassMix-F twice

Composing two passes gives a worst swap of 1/2985 (10⁶ decks), spread 50.99 (random is 51.0), and 0 one-round
survivals. Proofs are S3's plus one composition. It doubles the hand work, and the closed form no longer factorises
(measured 3.35·10⁻⁴ against (30/2652)² = 1.3·10⁻⁴).

## 4. PassMix-F on paper: what is proved, what is open

Work in position space: the hand and key hold input positions. Let A = (h_k, g_k) be the cut amounts used at steps
k = 0…51. Step k has a hand of n = 51 − k cards and a key pile of m = k cards, and act_k(C) is a function of the
card and k.

* **Prop 1 (bijection).** Each step is a bijection of (hand, key) states, and its choice is read from the top of
  the key pile afterwards. Both inverses follow (§3.3).
* **Prop 2 (the controller order is uniform).** The map deck ↦ controller sequence is a bijection. Cut amounts
  depend only on the controllers and the pile sizes, so replaying the hand's cursor from the controller sequence
  recovers each controller's input position. So for a uniform deck, the steps (s, t) at which a and b are
  controllers are a uniform ordered pair.
* **Prop 3 (exact lower bound).** Let e(a,b) = #{k : act_k(a) = act_k(b)}. If the actions agree at both of the
  swapped cards' steps, the two runs use the same A, so the seat permutation is unchanged and the swap survives
  (F1). By Prop 2 that event has probability exactly **e(e−1)/(52·51)**. For PassMix-F, e counts the steps where
  the suit is invisible: a key pile with < 4 cards in normal steps and a hand with < 4 cards in fallback steps.
  Same-rank pairs with Δsuit = 2 give k ∈ {0,1,2,49,50,51}, so e = 6 and 30/2652 (35 pairs). Same-suit pairs give
  e = 0, and all but one "other" pair give e = 0. The per-pair table is in `logs/passformula.log`. Measured
  6♣↔6♦: 0.01129 at 10⁶ decks against the formula's 0.01131.
* **Prop 4 (partial converse, cyclic-order argument).** Suppose a swap survives with different action sequences.
  Let k₀ be the first step where they differ and k₁ the last. Then at k₀ the key cuts agree and the hand cuts
  differ; at k₁ the hand cuts agree and the key cuts differ; so at least two steps differ.
  * The k₀ half: a pile's cyclic order is never changed by cuts, and a later insertion on top keeps the relative
    cyclic order of the cards already there. If the key cuts differed at k₀ (with m ≥ 2), the controller would go
    into a different gap of the same cyclic key order, and the outputs would differ.
  * The k₁ half: symmetrically, run the inverse from the common output. Undoing a different hand cut at k₁ would
    re-insert the controller into a different gap of the same cyclic hand, contradicting the common starting order
    0…51.
* **Lemma M (survive ⇒ equal actions) is false in general.** On 3–7-card decks with random action tables it fails
  (`logs/lemmaM_small.log`). At 52 cards it fails rarely: PassMix-F has 9 exceptions in 66.3M pair-decks, and each
  printed witness has exactly 4 differing steps (`logs/passmech.log`). PassMix with no fallback has 0 in 66.3M,
  and the edge rule has 8. The first PassMix-F witness (5♣↔6♣) was re-checked in independent Python. Its
  differing steps are 36, 37, 45 and 46: two adjacent pairs where consecutive controllers trade order and the cuts
  compensate. The counts are deterministic; which witnesses get printed depends on thread timing.

So **survival = e(e−1)/2652 + R**, with a proved lower bound and a reconvergence term R that is measured at
≈ 1.4·10⁻⁷ per pair-deck but not bounded. A paper upper bound needs a bound on R. By Prop 4, R needs a hand-only
divergence that later re-synchronises the hand cursor, and a key-only divergence that cancels it. That looks
provable (hand cuts are ≤ 13 on a hand of ≥ 13 cards before the fallback region), but it is **not done**. For
comparison, v11 has no known paper route at all, and SumRanks' 1/64 bound took the ≈ 3300-line DP proof.

## 5. Rough Lean effort against the current v11 state

Line counts are for existing files on `doubledeal-v11`. The estimates are rough and assume the model, sudo and
emitted code are written in the same style as today.

| item | v11 GridCycle today | S3 PassMix-F | S2 TwinSum-GF | S1 PivotRoll |
|---|---|---|---|---|
| model + `inv ∘ L = id` | done (`GridCycle.lean` 779; re-proved at each tweak) | ~350–500, adapted from `PassKey.lean` (475) | ~200–300 (SumRanks pattern) | ~150 |
| `L ∘ inv = id` | **open** | comes with the step lemma | comes free | comes free |
| Link-2 refinement | done (`Link2/Mix.lean` 1417) | ~800–1500, PassKey templates | ~800–1100 (like `SumLink` 1117) | ~400 |
| T1: commutes only with id | done (`Walk` + `GridCycle` ≈ 490) | new, ~200–400, uncertain | Iff-style ~400 | ~200 |
| covariant conjecture, v10Sym case | done (fixed seat 26) | needs a new argument or the anchor rule | needs a new argument | — |
| survival bound | none; no paper route | lower bound on paper now; Lean ~300–600; upper bound open (R) | DP redo (~3300) | fails anyway |
| hand refinement (S7) | overflow scan, finger, marker, blocker | two cuts + one compare | like SumRanks | trivial |

## Files

| file | what |
|---|---|
| `layers.h` | all layers and inverses: v11 reference, SumRanks, PivotRoll, TwinSum (ℤ₄ and GF), SRDUP, PassKey F, PassMix variants (ids 0–13, listed in the header comment) and the v10 stem |
| `measure.c` | round-trip, survival (layer / one round / single pair), spread, symmetry scan, vectors |
| `passmech.c` | PassMix mechanism: survive vs equal actions, the closed form, witnesses of Lemma M failures |
| `passformula.py` | closed-form e(e−1)/2652 tables and hand-cost counts |
| `lemmaM_small.py` | exhaustive small-deck test showing Lemma M is false for arbitrary action tables |
| `passwalk.py` | PassMix-F walkthrough with decryption |
| `xcheck.py`, `stemvec.c` | cross-checks: C against the v11 `ddport.py` / `dd_v8.py` (v11 GridCycle, SumRanks, PassKey, stem) and against independent Python for the new layers |
| `run_all.sh` | reproduces every log; each log starts with its producing command |
| `logs/` | summaries only (no raw per-deck output) |

Reproduce: create `/tmp/v11tree` as in the header of `run_all.sh`, then run `./run_all.sh`. It takes about an hour
on 8 cores. Binaries are git-ignored.
