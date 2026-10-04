<!-- Owns: the change history of the ECBS draft before the 2026-10-03 edition, and the key encodings not chosen. Maintenance rules: ../../../DOCS.md. -->
# ECBS: history (not normative)

The normative design is [`primitives/key_exchange/ecbs/SPEC.md`](../../../primitives/key_exchange/ecbs/SPEC.md) with [`CARD.md`](../../../primitives/key_exchange/ecbs/CARD.md). This file keeps, verbatim, the change tables and the not-chosen key encodings of the 2026-09-30 draft (`kx-specs/ECBS_SPEC.md`, added by #146 and reverted by #148). Script names in it refer to `core/` (formerly `kx-specs/ecbs/`). Rows about the trace check, the receiver chain, the trace ladder and the 3-hole protocol marker are superseded by the certificate check (SPEC §0, §5.3); see [`history/trace-check/TRACE_CHECK.md`](history/trace-check/TRACE_CHECK.md).

## Draft §0: what changed (2026-09-30)


**After the math review and Zachary's key choice (2026-09-30):**

| # | Before | Now |
|---|---|---|
| R1 | Zachary to choose an encoding | **Pegs-only.** Serious **162 cells** (H∞ = 256.76 exactly), headline **"128-bit security, key-limited"**: brute force on the key (≈ 2^128) is the best attack and the curve's rho (2^136.78) is margin. Matching counts: **Hobby 51, Toy 16, Demo 2** (§4) [run: ecbs_tiers] |
| R2 | Three-state as the draft option; "proven ≈ 77" | **Three-state dropped in every tier.** Pair cancellation gives rigorous upper bounds H∞ ≤ **169.93** (Serious 6 fleets), **207.01** (7), **57.96** (Hobby 2), **25.06** (Toy 1), all below target [review: mr_pairs, mr_fleets]. The ≈ 77-bit figure is a **Monte-Carlo estimate**, never proven |
| R3 | "Serious twist has a 245-bit composite cofactor" | The Serious twist **factors completely**; largest prime 115.4 bits, rho ≈ 2^57.7 [run: ecbs_twists; review]. **Sending y and checking the curve equation are mandatory; an x-only variant must never be adopted.** Without the check: Serious leaks k mod a 120.3-bit number (node) plus 43.9 bits (b′ = 2); **Hobby's key falls completely** (§7) |
| R4 | Pegs-only exact "≤ 175 cells" | Exact threshold **n − 3**: Serious 176 → 278.95, Hobby 56 → 88.76, Toy 20 → 31.70, Demo 4 → 6.34 [review: mr_lemmaA; relation at n − 2 checked in ecbs_review_checks] |
| R5 | Frobenius-aware key search "[open]" | **Small gains:** ≤ 2^0.50 at 162 cells, 2^0.58 at 173, 2^1.53 at 176 [review: mr_frob; E[c] recomputed in ecbs_tiers] |
| R6 | Descent "[open]" | **No GHS/Weil descent applies** (n prime, E over GF(3)); the summation-polynomial question rests on the literature and is **unverified** (§7) [review Q5] |
| R7 | Fold bound constant 4√q; "under DDH" | Constant **3√q** [review: proof, not re-derived by me]; bounds re-run. **Only the uniform shared-point model is claimed**, not DDH (§6) [run: ecbs_extractor] |
| R8 | 12-multiply "chord rule kept over a bottom", peak 9 + 8 bands | **F-form verse** ("the chord rule told from the base point", six lines) and **lazy-y** receiver chain: **7 + 7 bands**, verified against PARI in every tier; **Serious 26 → 22 grids**, Toy and Hobby unchanged; the swap move is no longer needed [run: ecbs_fform, ecbs_budget_fform] |
| R10 | Key trits drawn from a bag (white peg, red peg, destroyer) | **Randomizer kit adopted (2026-09-30, approved by Zachary):** the key's trits come from the **d10 row cup** (§4). Same exactly uniform trits, so no entropy or tier figure changes; the all-empty re-draw is kept. A d6 per hole (1–2 empty, 3–4 white, 5–6 red) is the zero-reroll fallback, and the bag remains valid. [`../bs/randomizer-kit/`](../bs/randomizer-kit/README.md) [run: randomizer_kit.py] |
| R9 | Pattern counts [MC]; multiplicity 72 "not proven max" | Exact: 2^33.669 patterns, Shannon 33.6048 bits; **72 is the global maximum** [review: mr_fleets, mr_fleets2]. Only relevant to fleet-based options |

The two tables below are history. Rows about three-state keys (2, 3, 4), the 9 + 8-band peak (8, G, H), the old verse (F) and the old extractor figures (11) are superseded by the table above and by §2–§6.

**Since the draft:**

| # | Draft | This spec |
|---|---|---|
| 1 | Serious ≈ 2^136 (rho with Frobenius) | **2^136.78** expected rho iterations. The draft formula √(πℓ/4)/√(2n) counts the negation speed-up twice (0.50 bit) [run: ecbs_curve] |
| 2 | Key ≈ 50.6 bits per fleet × 6 = "enough" | Min-entropy after Frobenius aliasing for 6 fleets is **provably ≤ 225.48 bits** (an explicit heavy key). The best certified lower bound is ≈ 77 bits (Monte-Carlo estimate) [run: ecbs_entropy] |
| 3 | Aliasing loses "≥ 6 bits, no upper bound" | Rigorous: the loss is **≥ 55.9 bits** below log₂ℓ = 281.39 (6 fleets). A 7th fleet gives ≤ 260.04, which is still not proven ≥ 256 |
| 4 | Pattern multiplicity max 34 (Monte Carlo) | A pattern with **multiplicity 72** exists (an L-shape), so the single-fleet min-entropy is ≤ 45.64 bits. 72 is not proven to be the maximum [run: fleet_maxmult] |
| 5 | Cofactor strip 5B | **On-curve check plus trace (subgroup) check**. This rejects instead of silently transforming |
| 6 | Pegs-only +6 % / +31 %, six-state +64 % (counted in additions) | Counted in **moves** (§4) |
| 7 | Six-state "Frobenius, add ±P for peg; Frobenius, add φ(P) if ship" | Taken literally, that wording **collapses** two digit pairs. Use "Frobenius, ±P for peg, Frobenius, +P if ship" (§4.4) |
| 8 | 11 registers + separate 3n−2 cube strip; paper allowed | No-paper schedule on a **fixed workbench**: measured peak **9 register bands + the workbench** (walk) and 8 + workbench (validation) (§2) |
| 9 | Hidden state: loop positions, counters, script line, walk position | Each one is now a peg or a ship (§3, §8) |
| 10 | Receiver check via the mixed-add script | Affine-addition (chord) trace chain |
| 11 | "Hash the x-register" | A **fold** recipe with an honest extractor bound: 100 trits at Serious with statistical distance ≤ 2^−59.3 from uniform, *in a stated model* (§6) |

**In this edition (no rulebook):**

| # | Item | Now |
|---|---|---|
| A | Fold offsets "n back and n−k back" (counting 23/20, 59/42, 179/120) | **Lane layout + re-chosen taps**: "drop it one band up and one hole on, and again one row up" (Serious: six rows up). **Toy tap 3 → 15, Hobby tap 17 → 39**; Demo and Serious unchanged. Same curve group, same ℓ, rho and entropy results (§1) |
| B | Cube "hole i → hole 3i" (a count) | **Comb cube**: each register row is combed into a band three rows tall, one peg on every third hole [run: ecbs_workbench] |
| C | Printed base point P | **Derived on the board**: one white peg in hole 1, the root strip, slide on if it fails, then white-red-white-red [run: ecbs_basepoint] |
| D | Chain program rows (binary of n−1, n) | **Halving ladder**, built from a row of pegs [run: ecbs_basepoint] |
| E | Cursor grid + fleet-index row | **Ship-grid cursor** (marker peg / parking hole) for fleet keys; **coordinate rails** for grid-hole keys [run: ecbs_workbench] |
| F | 12-multiply script with no mnemonic | **"The chord rule, kept over a bottom"**: each line of the projective script is a line of the chord rule, scaled [run: ecbs_verse] |
| G | Hobby: 14 grids visual or 10 packed | **10 grids, fully visual** (8 workspace + 2 ship grids) [run: ecbs_workbench, ecbs_budget] |
| H | Demo with a fleet: 3 grids | **½ set (2 grids)**, with the chord rule and a trace *walk* for validation [run: ecbs_workbench, ecbs_budget, ecbs_walks] |

## Draft §4.2–4.3: key encodings not chosen

### 4.2 Alternatives kept for reference (not chosen)
- **Pegs-only, curve-matching:** Serious 173 cells (274.20, modelled 2^137.23, the review's recommendation) or 176 (278.95, the exact threshold). Not key-limited.
- **Six-state, 2 grids:** H∞ ≥ 278.95 [review, via Lemma A], at +46 % moves. Uses fleets, so the W1 cursor.
  - Wording pitfall (checked): the literal draft wording "Frobenius, add ±P for peg; Frobenius again, add φ(P) if ship" gives τ²Q + τ(peg + ship)P, which collapses (white, no ship) with (empty, ship) [run: ecbs_entropy §3]. Correct forms: "F, ±P, F, +P if ship", or "F, F, ±P, +φ(P) if ship".

### 4.3 Dropped: three-state (fleet + sign pegs), in every tier
- **Rigorous upper bounds from pair cancellation** [review: mr_pairs, mr_fleets; not re-run by me]: H∞(k) ≤ **169.93** (Serious, 6 fleets), **207.01** (7 fleets), **57.96** (Hobby, 2 fleets), **25.06** (Toy, 1 fleet). Every one is below its tier's curve-matching target, and 6 and 7 fleets are below 256.
- The lower-side figure ≈ 77 bits (Serious, 6 fleets) is a **Monte-Carlo estimate** of a per-layout bound, not a proof.
- My earlier explicit heavy keys (≤ 225.48, 260.04, 74.35) remain valid but are much weaker bounds. The fleet counts are now exact (2^33.669 patterns; multiplicity 72 is the global maximum) [review].

## Draft §2 notes on the old schedule

- With the old schedule on the same keys: Demo 2 (with the trace walk; the old chain does not fit, 17 / 16), Toy 5, Hobby 9, **Serious 26** grids; moves differ by +0.2 % to +0.9 % [run: ecbs_budget_fform].
- Demo alternatives that also fit: chord walk + trace walk (6 bands, control 15 / 24, 4,960 moves). The F-form at Demo (7 bands) needs 25 control holes of 24, so it does not fit the ½ set.
- Pegs-only keys use **coordinate rails** (20 holes) in the key grid's unused holes, so no control holes go to rails in any tier.
- Slides are ≈ 17 % of the total at Demo, ≈ 13 % at Toy, ≈ 8 % at Hobby and ≈ 3 % at Serious [run: slide moves in ecbs_fform].
- Hobby and Serious need **double grids: two grids placed side by side and treated as adjacent, so their rows run on continuously** **[assume; confirmed by Zachary]**. The grids do not physically butt; the gap between them is treated as continuous. Demo and Toy lanes live inside single grids.
- Control inventory per tier: colour-flip tally (3 / 11 / 29 / 89 holes), a script-marker row (15 projective, 7 chord), the inversion ladder (2 / 4 / 5 / 7), the trace ladder (same lengths) and a protocol-phase marker (3). Rails (20) live in the key grid for pegs-only keys.
