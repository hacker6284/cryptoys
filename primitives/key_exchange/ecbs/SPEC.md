# ECBS: Elliptic Curve Battleship

Elliptic-curve Diffie–Hellman on **E: y² = x³ − x² + 1 over GF(3ⁿ)**, worked by hand with Battleship pegs. The private key is a row of pegs (pegs-only key); each player walks it over a base point derived on the board, sends the result together with a **certificate** A = π(C) − C, and the receiver checks the certificate before walking its own key over A. ECBS is the elliptic-curve sister of [BS](../bs/SPEC.md) and shares its conventions: holes empty/white/red = 0/1/2, the colour wheel, fold recipes, a ternary key walk with one Frobenius per cell, and calling public values aloud ("red hits, white misses, empty misfires").

**Design (Zachary, 2026-10-03):** player's card v3 with the certificate check is *the* ECBS design. This SPEC carries that one design. The losing receiver check (the trace check) and earlier variants are kept only as evidence under [`proofs/key_exchange/ecbs/trace-check/`](../../../proofs/key_exchange/ecbs/trace-check/TRACE_CHECK.md) and [`HISTORY.md`](../../../proofs/key_exchange/ecbs/HISTORY.md).

**Normative:** this SPEC, the **player's card [`CARD.md`](CARD.md)** and the runnable spec **[`ecbs.sudo`](ecbs.sudo)** beside them (compiled by sudoc, as for BS; §11). The card is the hand procedure: the exact words players follow (play card, check card, Demo changes). §3 and §5 give the mathematics each card line implements; `ecbs.sudo` runs the card line by line.

**Code and evidence** live in [`proofs/key_exchange/ecbs/`](../../../proofs/key_exchange/ecbs/README.md) (index in its README). The evidence there runs the code sudoc generates from `ecbs.sudo` (the card followed literally on a modelled peg board) and checks every result against PARI/GP. There is no hand-written implementation of ECBS.

**Marks.**
- [run: dir/script] = computed by that script under `proofs/key_exchange/ecbs/`; `evidence/…` drivers run the sudoc-generated code of `ecbs.sudo` (recorded output in `evidence/results/`).
- [log: path] (also `log:` inside a run tag) = the recorded output of a Phase-1 script that was removed when `ecbs.sudo` replaced the hand-written board model; kept as history, not re-run (git history: commit `ad80f54`).
- [proof] = a short argument given here or in `proofs/key_exchange/ecbs/MATH_REVIEW.md` (item named).
- [review: mr_…] = computed or proved by the Mathematician's review (`proofs/key_exchange/ecbs/review/`), not re-run unless also marked [run].
- [heuristic] = a standard but unproven model. [open] = not known. [lit] = literature, not re-checked. [lit-mem] = literature cited from memory, not re-fetched.
- **[assume; confirmed by Zachary]** = a physical or house-rule assumption Zachary confirmed (§9).

**House rules.**
1. Every step is a visual peg recipe: no lookup tables, no colour arithmetic.
2. **No paper.** All working state lives in grids, pegs and ships.
3. **No printed rulebook.** Every rule is a short spoken recipe (CARD.md); every constant is spoken ("cube, minus square, plus one") or derived on the board (the base point, the ladder).
4. Fingers may hold a place during a pass. Cursor ships are parked before you let go **[assume; confirmed by Zachary]**.
5. Pegs are unlimited; only grids and fleets count. Hours of hand work are fine.
6. Claims are narrow, and each one names its assumptions.

---

## 0. This edition (2026-10-03)

The card v3 certificate check replaces the trace check. Changes against the 2026-09-30 draft (whose change tables are in `HISTORY.md`):

| # | Item | Now |
|---|---|---|
| 1 | Receiver check (§5.3) | **Certificate:** send C = [a]P and A = π(C) − C. The receiver tests C on the curve, rebuilds A with one chord addition, rejects an empty run, rejects unless the rebuilt A matches peg for peg, and walks over A. Shared point K = [(λ − 1)ab]P |
| 2 | What is accepted | Lemma (§5.3): π − 1 maps E(GF(3ⁿ)) onto ⟨P⟩ with kernel E(GF(3)). An accepted A is in ⟨P⟩∖{O}; C itself may lie outside ⟨P⟩ and is harmless. (The draft's "accepts exactly ⟨P⟩∖{O}" was the trace check's property.) |
| 3 | Curve test, §7 | Still **mandatory**: with a self-consistent A, every off-curve C with a non-empty run passes the certificate (Demo 4,774,308 of 4,774,308). §7 is rewritten for the certificate [run: evidence/twist_s7, evidence/soundness_demo] |
| 4 | §6 | K restated; the uniform shared-point model is unchanged because λ − 1 is a unit mod ℓ |
| 5 | Exchange (§5.2) | BS PR #152 §3.1 calling as revised after DHH's review: clear the receiving homes, a calling-in-progress hole, cursor parked at the next hole to call, holes named by grid and coordinate. C is called into the base bands first; A into the bottom and gap after both players have certified |
| 6 | Control (§2) | One ladder, one tally, a phase hole and a calling hole, in one control row (row J of the workspace grids; Demo rows I–J). The trace ladder, second tally and 3-hole protocol marker are gone |
| 7 | Numbers (§2, §5) | Check per person 1,890 / 15,293 / 92,867 / 758,385 moves (Demo / Toy / Hobby / Serious; the trace check cost 3.93 M at Serious). Per person 5,916 / 0.142 M / 1.71 M / 40.3 M. Peak 7 bands in every phase; grids 2 / 5 / 9 / 22 |
| 8 | R6 | One inversion ladder, laid in the spare from n − 1 pegs, leftover thrown away; rungs in build order in the control row; climbed from the last made with the parking hole; one tally, no rebuild rule |
| 9 | §5.1 | The root strip lives in the across; white-red-white-red goes in the first four key cells; the script marker counts strip steps; the base point is made before the key is rolled |
| 10 | R7, §8 | The chord rule appears only in the certificate (Toy–Serious) and in the Demo walk. Receiver-chain and trace rows dropped; certificate and calling rows added |
| 11 | Demo | Simulated for the first time with the certificate: all 64 key pairs exact against PARI; control row fixed (5 script holes; 13 of 16 holes) [run: evidence/card_sim Demo] |

---

## 1. Curve and tiers

**Curve.** E: **y² = x³ − x² + 1** over GF(3ⁿ), said as **"y squared is x cubed, minus x squared, plus one"** (a₂ = −1 = 2, a₆ = 1, i.e. y² = x³ + 2x² + 1).
- Over GF(3), E has 5 points, trace t = −1, and Frobenius τ satisfies τ² + τ + 3 = 0 (discriminant −11).
- #E(GF(3ⁿ)) = 3ⁿ + 1 − Vₙ with V₀ = 2, V₁ = −1, V_{j+1} = −V_j − 3V_{j−1}; agrees with PARI `ellcard` for n = 2, 3, 4, 5, 7 [run: core/ecbs_curve].

| Tier | n | Tap xⁿ = xᵏ + 1 | Lane: width × band rows, less the last hole | Fold, as said | ℓ = #E/5 (proven prime) | log₂ℓ | Rho (negation + Frobenius) |
|---|---|---|---|---|---|---|---|
| Demo | 7 | k = 5 | 2 × 4 | "one band up and one on; one row up" | 421 | 8.72 | 2^2.78 |
| Toy | 23 | k = 15 | 8 × 3 | "one band up and one on; one row up" | 18828582139 | 34.13 | 2^14.63 |
| Hobby | 59 | k = 39 | 20 × 3 (a double grid) | "one band up and one on; one row up" | 2826077218347794449447657747 | 91.19 | 2^42.48 |
| Serious | 179 | k = 59 | 20 × 9 (a double grid) | "one band up and one on; **six** rows up" | 5078489869…5423907 (282 bits) | 281.39 | 2^136.78 |

[run: core/ecbs_curve, log: core/ecbs_layout_results.txt]
- Taps: the lane layout needs n − k to be a whole number of rows; k = 15 (Toy) and k = 39 (Hobby) are the only "+ +" irreducible taps with that property [log: core/ecbs_layout_results.txt §1]. GF(3ⁿ) is unique up to isomorphism and E is defined over GF(3), so #E, ℓ, λ and rho do not depend on the tap [proof, MATH_REVIEW C1].
- Every n is prime, every tap irreducible, every curve ordinary and non-anomalous. Embedding degree 15 (Demo), 2^29.6, 2^83.7, 2^273.9 (Toy, Hobby, Serious) [run: core/ecbs_curve].
- Exactly one root λ of x² + x + 3 mod ℓ has λⁿ = 1; Frobenius acts on ⟨P⟩ as multiplication by λ. λ − 1 ≢ 0 mod ℓ in every tier (λ = 1 would give 1 + 1 + 3 = 5 ≡ 0 mod ℓ) [run: evidence/card_sim (all tiers)].
- The quadratic twist and the GF(3)-defined invalid curves are weak. Under the certificate this is harmless only because y is sent and the curve equation is tested (§7).
- **No GHS/Weil descent applies** (n prime, E over GF(3)) [review Q5: lit + reasoning]. Summation-polynomial index calculus in characteristic 3: no analysis known; **literature-based, unverified**.
- **Key target (Zachary's choice):** the key is deliberately the weak link. Serious: 162 cells, H∞ = 256.76, modelled best key search ≈ 2^128.4, 8.4 bits below rho. Headline **"128-bit security, key-limited"** (§4).

---

## 2. Kit per player: lanes, workbench, homes, control row

**Layout** (the card's "Board" line):
- A **number** (a register) fills a band of a lane "less its last hole", hole 0 first, in reading order (§1 table).
- **All multiplies and cubes happen on one fixed workbench** of three bands. Serious: three double grids. Demo: lane 1 of the target grid (20 holes).
- **Seven homes**, from the top: across, up, bottom, base across, base up, gap, spare. A finished result **slides** into a named home ("same hole, other band").
- Hobby and Serious use **double grids**: two grids side by side treated as adjacent, rows running on **[assume; confirmed by Zachary]**.
- Grids are numbered from the workbench's first grid; calls name them (§5.2).
- **Demo (½ set):** one target grid in five 2-wide lanes. Lane 1 is the workbench; homes are the 4-row slots of lanes 2–5 (rows A–D: across, up, bottom, base across; rows E–H: base up, gap, spare; lane 5 rows E–H free). The key is 2 cells of the ocean grid.

**Control row** (state of the procedure, all in pegs). Row J of the workspace grids, run on grid to grid; at Demo rows I and J of lanes 2–5, row I first. From the left: **script marker** (15 holes; Demo 5), **phase hole**, **calling hole**, **ladder** (one rung per hole), **parking hole**, **tally**.

| | Demo | Toy | Hobby | Serious |
|---|---|---|---|---|
| control holes available | 16 (rows I–J, lanes 2–5) | 40 (4 grids × row J) | 80 | 200 |
| script / phase / calling | 5 / 1 / 1 | 15 / 1 / 1 | 15 / 1 / 1 | 15 / 1 / 1 |
| ladder (build order) | WR | WRRW | WRWRR | WRWWRRW |
| tally peak | 3 | 11 | 29 | 89 |
| **need / available** | **13 / 16** | **33 / 40** | **52 / 80** | **114 / 200** |
| highest hole used | 12 | 32 | 51 | 113 |

[run: evidence/card_sim (all tiers); log: card/extras_v3.txt]. Asserted in every run: no overrun; the parked rung always matches the ladder; never a second tally; the phase hole ends red on both boards.
- **Demo fix.** With the other tiers' 15-hole script row, Demo needs 23 control holes and overruns the 16 holes of rows I–J (the generated code traps while laying the ladder; a sudo test) [run: evidence/card_sim Demo]. The Demo walk is the chord rule, whose script marker peaks at 5 holes (two cubes and three multiplies per cell; the marker stands still during the inversion), so Demo's script row is 5 holes and the control row needs 13 of 16. The free 8th slot (lane 5, rows E–H) stays spare.
- The key's walk position uses **coordinate rails** in unused holes of the key grid (20 holes), not control holes.

**Measured peak** [run: evidence/card_sim (Toy 10, Hobby 6, Serious 4 exchanges), evidence/card_sim Demo (all 64 Demo key pairs)]: **7 register bands plus the workbench in every phase** (base point, walk, curve test, make certificate, rebuild, shared walk; 6 while calling), counting bands being lifted. Highest workbench hole: 18/20, 66/72, 174/180, 534/540. Not shown: that 7 is minimal.

**Grids and moves per player:**

| Tier | Key | Walk | Workspace + key grids | Moves per person (mean; range) | Control-row moves (extra) | Hand time @ 1 move/s |
|---|---|---|---|---|---|---|
| Demo (½ set) | pegs-only 2 | chord | **1 + 1 = 2** | 5,916 (5,064–6,788; all 128 people) | 234 | ≈ 1.6 h |
| Toy (5) | pegs-only 16 | F-form | **4 + 1 = 5** | 141,822 (100,208–170,550) | 1,302 | ≈ 39 h |
| Hobby (11) | pegs-only 51 | F-form | **8 + 1 = 9** | 1,714,807 (1.36–1.97 M) | 3,367 | ≈ 476 h |
| Serious (32) | pegs-only 162 | F-form | **20 + 2 = 22** | 40,287,769 (37.2–44.0 M) | 10,564 | ≈ 11,191 h |

[run: evidence/card_sim (all tiers); grid counts: core/ecbs_budget bookkeeping at 7 bands, log: card/extras_v3.txt; hand time = mean ÷ 3600, an assumption of 1 move/s]. Move convention: place, lift or drop a peg = 1; slide or jump = 2 per peg; clear = 1 per peg; calls move no pegs (laying an answer = 1).

| Phase (mean moves per person) | Demo | Toy | Hobby | Serious |
|---|---|---|---|---|
| base point (incl. the W R W R walk) | 3,208 | 23,400 | 105,759 | 734,962 |
| own walk (+ finish) | 390 | 52,302 | 765,780 | 19,437,484 |
| laying called answers | 18 | 61 | 156 | 473 |
| curve test | 190 | 879 | 4,213 | 30,658 |
| make own certificate | 842 | 7,176 | 44,250 | 363,624 |
| rebuild theirs + compare + clears | 858 | 7,238 | 44,404 | 364,102 |
| shared walk (+ finish) + fold | 411 | 50,767 | 750,246 | 19,356,465 |
| check share (curve + make + rebuild) | 31.9 % | 10.8 % | 5.4 % | 1.9 % |
| base point share | 54.2 % | 16.5 % | 6.2 % | 1.8 % |

Ladder build, once per kit: 17 / 65 / 173 / 533 moves. Storing P across games instead of re-deriving it raises the peak to 9 bands (Serious 22 → 26 grids); re-deriving is the rule at every tier [run: evidence/card_sim store_P].

---

## 3. Recipes (the mathematics behind each card line)

**R0 Colour wheel:** empty → white → red → empty. **R1 Drop:** a dropped white peg turns a hole one step round; a dropped red peg one step back. Mirror = swap white and red (negation).

**R2 Add / take away:** drop every peg of one number onto the same holes of the other; to take away, drop it mirrored.

**R3 Fold** (lane layout): "From the far end, lift each peg beyond the number and drop it **one band up and one hole on**, and again **one row up** (Serious: **six rows up**)." "One on" at a row's end is the next row's start. With n = w·h − 1, "n back" is h rows up and one hole on; with n − k = w·r, "n − k back" is r rows up [proof, MATH_REVIEW C18]. 300/300 random strips per tier match the reference reduction [log: core/ecbs_workbench_results.txt A].

**R4 This times that** (on the workbench): lift that number's highest peg and lay this number from that hole (mirrored for a red peg) until that band is empty; then fold. "A copy of" that: copy it into the spare first and lift the copy. "Onto" a number: slide it onto the workbench first. Slide the result "into" the band named.

**R5 Comb cube:** comb each row, top first, into the next workbench band, one peg on every third hole, a cursor ship keeping your place; then fold. Frobenius = cube every coordinate of the point. 300/300 cubes per tier; the strip plus the 2-hole comb gap fits the workbench (69 ≤ 72, 177 ≤ 180, 537 ≤ 540) [log: core/ecbs_workbench_results.txt A]. **Demo:** rows are 2 holes, a finger keeps the place, no gap; the 19-hole cube strip fits the 20-hole workbench (highest hole 18) [run: evidence/card_sim Demo].
- No rigid motion of holes can be the cube in a polynomial basis; a normal basis needs a multiplication table [log: core/ecbs_layout_results.txt §2–3].

**R6 Invert (Itoh–Tsujii) with one halving ladder.**
- **Build once per kit:** lay a number's pegs less one (n − 1 pegs) in the spare; pair them off; a leftover makes a **red rung**, none a **white rung**; throw the leftover away, keep one peg of each pair, repeat down to one peg. Rungs go into the control row in build order: WR, WRRW, WRWRR, WRWWRRW [run: evidence/card_sim (all tiers)]; these are the Itoh–Tsujii programs for n − 1 [log: core/ecbs_basepoint_results.txt].
- **Use:** copy the number into the gap; tally = one white peg. Climb from the last rung made, parking each rung in the parking hole while you work it. At each rung: cube a copy of the gap in the spare once per tally peg, the gap times the spare into the gap, double the tally; on a red rung also cube the gap into the spare, the number times the spare into the gap, add a tally peg. At the last rung skip the doubling and the extra peg. Cube the gap once more. The gap times a copy of the number must be one peg in hole 0 (the quadratic character ±1); if red, mirror the gap.
- **Tally:** "once per tally peg" turns a white tally peg red after each go; to double, drop red on each red and lay as many whites again. One tally, no rebuild rule (inversions never nest).
- Every nonzero element at Demo (2186/2186) and 5000 / 3000 / 1000 samples at Toy / Hobby / Serious invert correctly [run: evidence/soundness_demo; evidence/soundness].

**R7 Addition.**
- **F-form walk** (Toy, Hobby, Serious): "the chord rule told from the base point" (x₂, y₂), the division saved up in the bottom Z. Card wording (play card step 12) and the identity each line implements:
  1. **Run:** "mirror the across; lay the base across times a copy of the bottom onto it": v = x₂Z − X. *Empty? Reroll your key.*
  2. **Rise:** "mirror the up; lay the base up times a copy of the bottom onto it": u = y₂Z − Y.
  3. **Gap:** F = u²Z + v²(v + Z) = v²Z·(x₃ − x₂).
  4. **Bottom:** new Z = v·(v²Z).
  5. **New across:** new X = v·F + x₂·(new Z).
  6. **New up:** new Y = −(u·F + y₂·(new Z)).
  For a red cell use −y₂ throughout. The identities hold in 50/50 random additions per tier against PARI [log: core/ecbs_fform_results.txt §1; proof MATH_REVIEW C25].
- **Chord rule** (the certificate at every tier, and the Demo walk): "slope = rise over run; new x = slope squared, plus one, plus the first x, minus the run; new y = slope times (first x minus new x), minus the first y" (the "plus one" is −a₂; plus the first x minus the run equals minus both x's, since −2 = 1 in GF(3)). The run is inverted first and the rise made afterwards ("lazy y"). On the card the chord is "do the gap times the spare, into the gap; do the gap times a copy of itself, drop a white peg in hole 0, add its across, take away the bottom, and put it into the bottom; take the bottom away from its across; mirror its up and lay the gap times its across onto it; clear the gap and slide the bottom into its across".

**R8 Walk:**
- Visit key cells in reading order. At each cell: Frobenius the accumulator (skip while it is empty), then add +P for white, −P for red. The first non-empty cell copies the base point (Toy–Serious also a white peg in hole 0 of the bottom). Toy–Serious finish by inverting the bottom (R6) and multiplying the across and up by it.
- **Script marker:** one hole on per cube or multiply of the walk (and of the root strip), lifted at each new cell: 15 holes (F-form: 3 cubes + 12 multiplies); Demo 5 (2 cubes + 3 multiplies; it stands still during the inversion) [run: evidence/card_sim (all tiers)].
- **Where am I** in the key: coordinate rails ("B-7") in unused holes of the key grid.
- If an addition finds the run empty, re-roll the key. For pegs-only keys with m ≤ n − 3 cells this never happens, for any base point in ⟨P⟩∖{O} (so also over a received A), except for the all-empty key [proof, MATH_REVIEW C28; run: core/ecbs_tiers]. The all-empty key is re-rolled at once.

---

## 4. Key encoding: pegs-only (Zachary's choice, 2026-09-30)

**Model.** One Frobenius per step puts a digit on τ^e. On ⟨P⟩, τ acts as λ and λⁿ = 1, so k = Σ_j c_j λ^{m−1−j} (mod ℓ) with c_j ∈ {0, 1, −1}. With m ≤ n cells there is no aliasing.

**Recipe** (randomizer kit, approved by Zachary 2026-09-30; the card's step 10): fill the first m holes of the key grid row by row with the **d10 row cup**: five d10s (red, orange, yellow, green, blue) per row, 0s rethrown, two holes per die in rainbow order; on a phone keypad the number's row gives the first hole's peg and its column the second's (top/left = empty, middle = white, bottom/right = red). Partial rows throw only the dice needed (an odd count uses the last die's keypad row only). If every hole came up empty, roll again. Exact: faces 1–9 ↔ pairs of trits, 0 rejected, so every trit is uniform and independent. Effort and the fallbacks (a d6 per hole; the bag) are in BS §4.2 and [`proofs/key_exchange/bs/randomizer-kit/`](../../../proofs/key_exchange/bs/randomizer-kit/README.md) (row-cup counts for 162 cells there). Dice per key: 81 / 26 / 8 / 1 d10s (Serious / Hobby / Toy / Demo).

**Entropy.** For pegs-only with m ≤ n − 3 the map from cells to k is injective (Lemma A; exact threshold n − 3 [review: mr_lemmaA; run: core/ecbs_review_checks]), so H∞ = log₂(3^m − 1) exactly and min-entropy, guesswork and brute force agree.

| Tier | **Cells** | Key grid shape | **H∞ (exact)** | Plain BSGS | Modelled best key search | GGM floor † | Rho | Margin (rho − plain BSGS) | Headline |
|---|---|---|---|---|---|---|---|---|---|
| Serious | **162** | one grid + rows A–F + 2 holes of row G | **256.76** | 2^129.38 | **2^128.38** | 2^124.14 | 2^136.78 | +7.40 bits | **128-bit, key-limited** |
| Hobby | **51** | rows A–E + 1 hole of row F | **80.83** | 2^41.62 | **2^40.62** | 2^36.98 | 2^42.48 | +0.86 bits | 40-bit, key-limited |
| Toy | **16** | row A + 6 holes of row B | **25.36** | 2^13.68 | **2^12.68** | 2^9.92 | 2^14.63 | +0.95 bits | 12-bit, key-limited |
| Demo | **2** | 2 holes | **3.00** (8 keys) | 6 operations | 2^1.79 | – | ≈ 6.9 iterations | +0.20 bits | a demonstration |

[run: core/ecbs_tiers] † Generic-group floor with free ±Frobenius, 2^((H∞ − log₂2n)/2) [review Q1, a model bound]. The headline uses the rotation model; neither figure is a proof about real attackers.
- **Why each count** [run: core/ecbs_tiers]: Serious 162 is the smallest m with H∞ ≥ 256 (Zachary); 128 is the largest multiple of 8 that stays key-limited. Hobby 51 is the smallest m with H∞ ≥ 80 (the next multiple of 8, 48 bits, is beyond the curve). Toy 16 is the smallest m with H∞ ≥ 24 (13 bits would need 17 cells, 0.05 bits past rho). Demo 2 is the only key-limited count.
- **Frobenius-aware key search** gains ≤ 2^0.50: E[c] = 2.000, 2.006, 2.003, 1.500 [run: core/ecbs_tiers; review mr_frob].
- Alternatives (curve-matching pegs-only counts, six-state, three-state fleet keys) are not part of this design; their analysis is in `HISTORY.md` and `core/ecbs_entropy`.

---

## 5. Base point, exchange and receiver check

### 5.1 The base point, derived on the board (card step 9)

"A white peg in hole 1 of the base across; its curve side in the bottom; the bottom times a copy of itself in the gap; a white peg in hole 0 of the up. In the across, lay the **root strip**, one hole short: red, empty, red, empty …, ending red, white. At each strip hole, under a cursor ship, cube the up, then on red do the up times a copy of the gap, on white of the bottom, into the up. … Not the bottom? Clear everything, move the white peg one hole on, and restart. … Walk **white, red, white, red**, laid in the first key cells; … slide the result into the base bands."
- The base point is made **before** the key is rolled, so the first four key cells are free for white-red-white-red.
- **Root strip:** y = rhs^((3ⁿ+1)/4), a square root because 3ⁿ ≡ 3 (mod 4); its digits are red, empty, …, red, white (n − 1 of them) [log: core/ecbs_basepoint_results.txt]. The script marker counts strip steps (two per hole at most).
- **White, red, white, red** = τ³ − τ² + τ − 1 = 5 on this curve [proof, MATH_REVIEW C16]: any R outside E(GF(3)) has 5R of order ℓ.
- First working hole 2 (Demo, Toy), 1 (Hobby, Serious). The base point by rule equals P in every simulated game: 128/128 (Demo), 20/20, 12/12, 8/8 [run: evidence/card_sim (all tiers)].
- **Test vectors** (hole 0 first): Demo x = `.RWR.WW`, y = `R..RRWR`; Toy x = `RW..W.WWWR..W...WWWRWRR`, y = `RRWWRRR..R.WRRW..RWWRRW`; Hobby sha256(x|y)[:16] = `e6635080e15e0cd7`; Serious `345ec55420cdd25e`. Full registers in `core/ecbs_exchange_results.txt`. P is self-checking on the board (y·y = rhs, then order ℓ by construction).

### 5.2 Exchange (card: play steps 11–14, check card)

1. **Own walk.** Each player walks the key over P (§3 R8) and finishes: C = [a]P in the across and up.
2. **Call C.** Each player calls the partner's across and up into its **base bands** (calling, below).
3. **Curve test** on the called C (§5.3). Then **make your own certificate** in place: A = π(C) − C replaces C in your across and up; drop a white peg in the phase hole.
4. **Rebuild theirs:** make the certificate of the base bands in place (reject if empty); drop a second white peg in the phase hole (it turns red).
5. **Call A.** Once the partner's phase hole shows a peg, call their across into your bottom and their up into your gap. Unless they match the base across and base up peg for peg, reject. Clear the bottom and gap and, once both have called, your across and up.
6. **Shared key:** walk your key over the base bands (their A) and finish; fold the across (§6).

C must be called before anyone certifies: each sender certifies in place, consuming C. A is called only after both have certified: with C and A called together, each receiver would still hold its own C and A and have 3 empty homes for 4 called bands [log: card/extras_v3.txt].

**Calling** (BS PR #152 §3.1 as revised after DHH's review; the card's "Calling"):
- Clear the homes named. Stand a peg in the **calling hole** ("calling in progress"). Put the cursor ships on hole 0 of the first home.
- Call the matching hole of the sender's published band aloud by **grid and coordinate** ("grid 3, B7"; Demo "grid 1, A3"), hole 0 to n − 1 in number order, every hole, no early stop, never a key grid or the control row. Red hits, white misses, empty misfires; lay each answer in the cursor hole and move the cursor ships to the **next** hole to call. After the last, park the ships off the board and lift the calling peg.
- Each call is driven by the board alone: the phase hole picks C or A, the cursor picks band and hole.
- Holes called per receiver: **28 / 92 / 236 / 716** (4 bands × n), every call naming the same hole of the sender's band (asserted) [run: evidence/card_sim (all tiers)]. Letting go before every one of the 14 / 46 / 118 / 358 calls of a two-band session and resuming from the board alone gives an exact copy. A stale receiving home laid over without clearing gives a wrong copy in 193/200 (Demo), 200/200 (other tiers); with "clear the homes named" 0/200 [run: evidence/soundness_demo, evidence/calling_check].

**Full exchanges against PARI** [run: evidence/card_sim Demo (all 64 pairs of non-empty Demo keys), evidence/card_sim (Toy 10, Hobby 6, Serious 4)]: base point = P, sent C = [a]P, sent A = [(λ − 1)a]P = π(C) − C, the receiver's rebuilt A = the sender's A, curve test passed, both shared points agree and equal [(λ − 1)ab]P, folded key = the §6 reference fold on both sides: **every check in every run** (Demo 128/128 people, 64/64 exchanges; Toy 20/20; Hobby 12/12; Serious 8/8). No home clash; every called answer landed in an empty home.

### 5.3 Receiver check: the certificate

Pedantic choice: **reject, never transform.** On the called C = (x, y):
1. **Curve test (mandatory):** "the base up times a copy of itself, in the gap, must match the base across's curve side (a copy of it cubed, take away it times a copy of itself, white peg in hole 0), in the bottom." Never adopt an x-only variant (§7).
2. **Rebuild A** by one chord addition of π(C) and −C: run = x − x³ ("copy its across into the bottom, cube it, mirror it and add its across"); **reject if the run is empty**; slope = −(y³ + y)/run; new x = slope² + 1 + x³ − run; new y = slope·(x³ − new x) − y³.
3. **Compare** the rebuilt A with the called A peg for peg; reject on any difference.
4. **Walk over the rebuilt A** (the base bands). The sent A is only compared, never used.

**Lemma** [proof]. E(GF(q)) is cyclic of order 5ℓ with ℓ ≠ 5 prime. π − 1 is an endomorphism of E(GF(q)) whose kernel is the set of Frobenius-fixed points, E(GF(3)), of order 5. So its image has order ℓ and is the unique subgroup of that order, ⟨P⟩. Hence for every C ∈ E(GF(q)), A = π(C) − C ∈ ⟨P⟩, each point of ⟨P⟩ is the image of exactly 5 points C, and A = O exactly for C ∈ E(GF(3)). For affine C the run x − x³ is empty iff x ∈ GF(3); on E (n odd) the affine points with x ∈ GF(3) are exactly the 4 affine GF(3)-points, so "reject if empty" rejects exactly A = O. For x ∉ GF(3), π(C) ≠ ±C and the chord gives the true sum.
- So an accepted A is always in ⟨P⟩∖{O}. **C itself may lie outside ⟨P⟩** (for example C = [a]P + T with T ∈ E(GF(3)), which gives the same A as [a]P); it is accepted and harmless, because the receiver uses A, never C. No small-subgroup leak is possible.

**Soundness** (receiver verdicts: accept / curve / empty / mismatch). Demo is exhaustive over GF(3⁷)² [run: evidence/soundness_demo]; Toy / Hobby / Serious sample 5000 / 3000 / 1000 per class [run: evidence/soundness]. Every verdict below comes from the generated code of `ecbs.sudo` (`receive_check` on boards), checked against PARI/GP.

| Class | Demo (exhaustive) | Toy | Hobby | Serious |
|---|---|---|---|---|
| every on-curve C, correct A | 2100 accept, 4 empty (the order-5 points) | 5000 accept | 3000 accept | 1000 accept |
| … accepted A = PARI's π(C) − C, in ⟨P⟩∖{O} | 2100 / 2100; 420 distinct, each 5 times | all | all | all |
| C outside ⟨P⟩, correct A | (included above) | 5000 accept | 3000 accept | 1000 accept |
| C outside ⟨P⟩, wrong A (A = C, −A, a non-subgroup point) | (in the next row) | 5000 mismatch | 3000 mismatch | 1000 mismatch |
| A not matching π(C) − C (−A, A = C, one peg changed, another subgroup point; Toy–Serious also a non-subgroup point) | 8400 (4 for each of the 2100 C): 8400 mismatch | 5000 mismatch | 3000 mismatch | 1000 mismatch |
| C = an order-5 point (4 points × 4 A's, incl. empty bands) | 4 empty (honest A) | 16 empty | 16 empty | 16 empty |
| C off the curve, A = the card's formulas on C | 4,780,865 curve | 5000 curve | 3000 curve | 1000 curve |
| … of those, would pass with no curve test | 4,774,308 (all with a non-empty run) | 5000 | 3000 | 1000 |
| ladder inversion wrong | 0 of 2186 | 0 / 5000 | 0 / 3000 | 0 / 1000 |

Board level: every row above is the card followed literally on boards by the generated code (receiver holding its own A while rebuilding, C and A called in), peak 7 bands throughout; Demo also runs every on-curve C (2104: 2100 accept, 4 empty) plus 200 / 200 / 8 / 300 / 300 sampled in the other classes on boards [run: evidence/soundness_demo, evidence/soundness]. (Before `ecbs.sudo`, the Python sample was field level at Toy–Serious with a peg-level spot check of 30 / 15 / 6 per class [log: card/soundness_v3_peg_*.json].)

**Cost of the check** per person (curve test + make own + rebuild theirs + compare + clears): **1,890 / 15,293 / 92,867 / 758,385** moves (Demo / Toy / Hobby / Serious) [run: evidence/card_sim (all tiers)]. The trace check it replaced cost 2,721 / 46.9 k / 0.390 M / 3.93 M per person (curve test + lazy-y trace chain) [log: core/ecbs_fform_results.txt].

### 5.4 Shared point

Alice sends C_a = [a]P and A_a = π(C_a) − C_a = [(λ − 1)a]P (π acts on ⟨P⟩ as λ). Bob's walk over A_a gives [b]A_a. So both hold **K = [(λ − 1)ab]P**. λ − 1 is a unit mod ℓ, so K is uniform on ⟨P⟩∖{O} whenever [ab]P is (the model of §6). Checked in every simulated exchange (Demo 64/64, Toy 10/10, Hobby 6/6, Serious 4/4).

---

## 6. The x-register "hash": a fold, honestly an extractor

**Recipe** (card step 14): "Fold the across: Serious drops rows F to I onto rows A to D, Toy and Hobby row C onto row A. The key is rows A to E (Serious) or A to B." Demo: "drop rows C and D onto rows A and B; the key is rows A and B." That is 100 / 40 / 16 / 4 trits. The fold is the F₃-linear map z_j = Σ_{i ≡ j (mod m)} x_i; the card's fold equals it on both sides of every simulated exchange [run: evidence/card_sim (all tiers)].

**Claim, and its model** [run: core/ecbs_extractor; review C19]:
- **Model: the uniform shared-point model.** K = [(λ − 1)ab]P is uniform on ⟨P⟩∖{O}. **This is the only claim.** It is not implied by anything unconditional (K is determined by the public values), and **no DDH-type claim is made**.
- **Bound:** an F₃ XOR lemma gives SD ≤ ½·√(3^m − 1)·δ, with δ ≤ 3√q/(ℓ − 1) for any subgroup, O excluded [review Q11a: proof via Weil II; not re-derived here].
- Min-entropy: Pr[z] ≤ 2·3^(n−m)/(ℓ − 1).

| Tier | Output | Max bits | SD from uniform ≤ | H∞ ≥ |
|---|---|---|---|---|
| Serious | **100 trits** (rows A–E) | 158.5 | **2^−59.7** | 155.2 |
| Serious | 80 trits (rows A–D) | 126.8 | 2^−75.5 | 126.8 |
| Hobby | **40 trits** (rows A–B) | 63.4 | 2^−12.2 | 60.1 |
| Toy | **16 trits** (rows A–B) | 25.4 | 2^−2.6 | 22.0 |
| Demo | **4 trits** (rows A–B) | 6.3 | exact SD 0.2529 (bound vacuous) | exact 4.714 |

- Serious, largest m with SD bound ≤ 2^−64: 94 trits. The bound, not necessarily reality, caps it.
- **Not claimed:** random-oracle behaviour, DDH, anything for Demo, Toy or Hobby beyond the table. With key-limited keys the folded key's security is the key's (≈ 2^128 at Serious), not the fold's.

---

## 7. Attacks and limits

- **Rho:** §1. **Key search:** §4; with the chosen keys it is the best attack by design. Frobenius-aware key search gains ≤ 2^0.50.
- **Descent and index calculus:** no GHS/Weil descent applies (n prime, E over GF(3)) [review Q5]. Summation polynomials in characteristic 3 over prime-degree extensions: no analysis known; **literature-based, unverified**. No attack beating rho is known [heuristic].

### 7.1 Twist and invalid curves, for the certificate check

The receiver's formulas never use the curve's constant term, and they hard-wire a₂ = −1 (the "plus one"). So any pair C = (x, y) yields some rebuilt A and some shared point; the receiver walks over the rebuilt A, not over C. Every (x, y) with x ∉ GF(3) is of one of two kinds [proof below; Demo exhaustive over all 4,776,408 such pairs; run: twist/s7_certificate A]:

**(i) On a GF(3)-defined curve y² = x³ − x² + a₄x + a₆, a₄, a₆ ∈ GF(3)** (at most one, since 1 and x are independent over GF(3)). The substitution X = x + a₄ maps it onto y² = X³ − X² + b′ with b′ = a₄² − a₄ + a₆: **E** (b′ = 1), **E′** (b′ = 2) or the **node** (b′ = 0, y² = X²(X − 1)). In characteristic 3 the chord rule is unchanged by this shift (x₃ = s² + 1 − x₁ − x₂ moves by r when x₁, x₂ do, because −2r = r) and the shift commutes with Frobenius, so the card computes the group law of E, E′ or the node's non-singular points. Demo: 2100, 2100 and 2184 points on each of the three translates of E, E′ and the node; the card's certificate equals (π − 1)C on that curve in 400/400 checked per curve (PARI for E and E′, the torus map below for the node).

**(ii) Everything else** (Demo: 4,757,256 pairs). The rebuilt A lies on the cubic through π(C) and −C, y² = x³ − x² + a₄′x + a₆′ with a₄′ = (b³ − b)/(x³ − x), b = y² − x³ + x²; a₄′ ≠ 0 and the cubic is not defined over GF(3) for every one of these pairs, so each Frobenius of the walk moves the point to another curve and the walk is not a group operation on any one curve. 2,002 of these A happen to satisfy E's equation. **[open]:** this class is not analysed and nothing is claimed about it; the curve test rejects all of it.

**The quadratic twist** falls entirely in (ii): all 2268 twist points with x ∉ GF(3) (twist order 2271 by PARI; the same in the model −y² = x³ − x² + 1) [run: evidence/twist_s7 A]. A twist point (model y² = x³ + x² + 2) has b = 2x² + 2, which would need x to satisfy a degree-2 equation over GF(3); x has degree n (odd prime). The twist's own group law (a₂ = +1) is never computed, because y is sent and the formulas hard-wire a₂ = −1. So **a twist point gains an attacker nothing beyond class (ii)**, and with the curve test nothing at all.

**With the curve test** (the design): the accepted C are exactly E(GF(q))∖E(GF(3)) and the rebuilt A is in ⟨P⟩∖{O} (Lemma, §5.3; Demo exhaustive). Twist and invalid points never reach the walk. The serious-tier twist's own weakness (fully factored, largest prime 115.4 bits, rho ≈ 2^57.7; Hobby's largest twist prime 39.3 bits [run: core/ecbs_twists]) is therefore irrelevant.

**Without the curve test** (why it stays mandatory):
- A self-consistent A (the card's formulas applied to C) passes the certificate for **every** off-curve C with a non-empty run: Demo 4,774,308 of 4,774,308 (the other 6,557 off-curve pairs have x ∈ GF(3)); Toy 5000/5000, Hobby 3000/3000, Serious 1000/1000 sampled [run: evidence/soundness_demo, evidence/soundness]. The comparison step cannot catch an off-curve C.
- On **E′** and the **node** the kernel of π − 1 is their GF(3)-points (E′: (2, 0) and O; node: (1, 0), (2, ±1) and O), so the rebuilt A ranges over the subgroup of **index 2** (E′) or **4** (node). In every tier that subgroup is exactly the odd part of the group [run: evidence/twist_s7 B].
- **Mechanism** [run: evidence/twist_s7 B, every tier]: for C of prime order r on E′, the receiver's walk ends at [κ(μ) mod r]A, where π acts on ⟨A⟩ as the root μ of μ² − 2μ + 3 ≡ 0 (mod r) and κ(z) = Σ_j c_j z^{m−1−j} is the key polynomial (4/4 per tier, against PARI). On the node, ψ(x, y) = (y + ix)/(y − ix), with i² = −1 in GF(3^{2n}), maps the non-singular points onto the norm-1 torus of GF(3^{2n})*: the chord rule becomes multiplication, π becomes z ↦ z^(−3), the certificate becomes ψ(C)^(−4), and the walk ends at ψ(A)^κ(−3) (6/6 per tier). So the node exposes **κ(−3), the key read as a balanced base-(−3) integer**, modulo the order of A.

| Tier | Key bits | E′: order of the image (factors) | Node: order of the image (factors) | Leak, primes < 2^40: E′ / node | Leak, primes < 2^60: E′ / node |
|---|---|---|---|---|---|
| Demo | 3.17 | 1051 | 547 | 10.0 / 9.1 | 10.0 / 9.1 |
| Toy | 25.36 | 47071896187 (35.5 bits) | 23535794707 (34.5 bits) | 35.5 / 34.5 | 35.5 / 34.5 |
| Hobby | 80.83 | 16993 · 3770219 · 312996889 · 352328177 | 3187 · p80 | 92.5 / 11.6 | 92.5 / 11.6 |
| Serious | 256.76 | p44 · p239 | 3755779 · p46 · p54 · p162 | 0 / 21.8 | 43.9 / 120.3 |

[run: evidence/twist_s7 B; Serious factors are the review's, re-verified: each divides exactly and is prime]. "Leak" = log₂ of the product of the image's prime factors below the bound: what an attacker learns from one chosen C per prime if it can try up to that many candidate shared points per prime (for example against traffic under the folded key). On E′ each prime r gives κ(μ_r) mod r with a different μ_r; turning those residues into key digits is a modular knapsack, not attempted here (at Hobby the residues carry 92.5 bits against an 80.83-bit key).
- **Whole key from one node point, run end to end:** if the attacker learns the receiver's shared point, one node point whose rebuilt A has the full order (q + 1)/4 gives κ(−3) mod (q + 1)/4 by a finite-field logarithm in GF(3^{2n}) (PARI `fflog`), and (q + 1)/4 > 3^m in every tier, so the balanced base-(−3) digits are the key: recovered exactly at **Demo** and **Toy** (log 1.1 s) [run: evidence/twist_s7 C]. At **Hobby** (logarithm in GF(3¹¹⁸)*) PARI `fflog` **did not finish within a 1,500 s run**, so recovery is not demonstrated there [log: twist/s7_partC.txt]. At Serious the logarithm is in GF(3³⁵⁸)*, where discrete logarithms in small characteristic are quasi-polynomial [lit-mem: Barbulescu–Gaudry–Joux–Thomé 2014]; not run.
- Therefore: **send y, test the curve equation before anything else, and never adopt an x-only variant.** A receiver that skips the curve test loses its whole key at Demo and Toy (run), gives an attacker residues worth 92.5 bits against an 80.83-bit key at Hobby, and 43.9 + 120.3 bits of residues at Serious (primes < 2^60); the last two are not turned into a key here.

### 7.2 Other limits
- **No authentication:** an active man-in-the-middle wins, as in any unauthenticated DH. Compare both public points over a trusted channel (for example, read the folded keys aloud in person).
- **Side channels:** additions happen only at peg cells, so anyone watching sees the key. Physical privacy is assumed.
- **Hand time** @ 1 move/s (an assumption), per person: Serious ≈ 11,191 h; Hobby ≈ 476 h; Toy ≈ 39 h; Demo ≈ 1.6 h (§2).

---

## 8. No-rulebook audit: every former reference and its memorable rule

The "Verified" column names the Phase-1 scripts under `proofs/key_exchange/ecbs/` (commit ad80f54) that first verified each rule. Apart from `core/ecbs_curve`, `core/ecbs_tiers` and `core/ecbs_extractor`, they were removed when `ecbs.sudo` landed and are cited by their recorded logs (`*_results.txt`, `*.json` beside where they stood). Every row is now carried by `ecbs.sudo` itself and re-checked on the generated code against PARI/GP by `evidence/` (card_sim, soundness, soundness_demo, calling_check, twist_s7) and `vectors/` (base point, cube, fold, walks).

| Former reference | Memorable rule now | Verified |
|---|---|---|
| Curve constants a₂ = −1, a₆ = 1 | "y squared is x cubed, minus x squared, plus one" | core/ecbs_curve, core/ecbs_basepoint |
| Tier sizes n | Number = lane band "less its last hole": 2×4, 8×3, 20×3, 20×9 | core/ecbs_workbench A |
| Fold offsets (n, n − k) | "One band up and one on; one row up" (Serious: six rows up) | core/ecbs_workbench A |
| Reduction polynomial | Implied by the fold picture; nothing else uses it | core/ecbs_layout §1 |
| Cube hole 3i | Comb cube, "a peg on every third hole", a cursor ship (Demo: a finger) | core/ecbs_workbench A, demo/card_sim_demo |
| Inversion chain (binary of n − 1) | One halving ladder from "a number's pegs less one", rungs in the control row | card/card_sim_v3, demo/card_sim_demo |
| "Cube m times" count | One colour-flip tally (white turns red) | card/card_sim_v3 |
| 12-multiply script | F-form verse, card wording: "mirror the across, lay base across times a copy of the bottom onto it" … (6 lines, §3 R7) | core/ecbs_fform, card/card_sim_v3 |
| Chord rule | The certificate (every tier) and the Demo walk: "the gap times the spare … slide the bottom into its across" | card/soundness_v3, demo/soundness_demo |
| Base point P | White peg in hole 1 → root strip in the across → slide on → white-red-white-red in the first key cells | core/ecbs_basepoint, card/card_sim_v3 |
| Square-root exponent | Root strip "red, empty, …, red, white" | core/ecbs_basepoint |
| Cofactor 5 | "White, red, white, red" | core/ecbs_basepoint, MATH_REVIEW C16 |
| Walk order / position | Reading order; rails in the key grid | core/ecbs_workbench B |
| Script position | One marker peg in the script holes (15; Demo 5) | card/card_sim_v3, demo/card_sim_demo |
| Protocol phase | The phase hole: empty (call C), white (own certified), red (theirs rebuilt: call A) | card/card_sim_v3 |
| Receiver check | "The base up times a copy of itself must match the base across's curve side" (mandatory); certificate "if the bottom is empty, reject"; "unless they match peg for peg, reject" | card/soundness_v3, demo/soundness_demo |
| Calling | "Clear the homes named, stand a peg in the calling hole …, call by grid and coordinate, every hole, red hits, white misses, empty misfires" | card/calling_check, demo/soundness_demo |
| Key randomness | Row cup and keypad rule (fallback: a d6 per hole) | BS randomizer-kit |
| Key-cell counts | Grid shapes: Serious 162 = a grid plus rows A–F plus two holes; Hobby 51 = rows A–E plus one hole; Toy 16 = row A plus six holes; Demo 2 holes | core/ecbs_tiers |
| "Hash the x-register" | "Drop rows F–I onto rows A–D; keep rows A–E" (Toy, Hobby: row C onto row A, keep A–B; Demo rows C–D onto A–B) | core/ecbs_extractor, card/card_sim_v3 |
| Test vectors | None printed; the derived P is self-checking (y·y = rhs) | core/ecbs_basepoint |

**Remaining flags:**
- A player must remember the four lane shapes, the Serious "six rows up", the six F-form lines, the certificate's chord and the ladder rule. These are spoken rules, not tables; whether that is memorable enough is Zachary's call.
- The card is 1,440 words (play card 1,089 + check card 350, a wc-style count) for Toy–Serious, so it is split into a play card and a check card; the single-page target is not met [log: card/V3_NOTES.md]. The Demo section adds 391 (wc -w).
- Not simulated: hands-off position *inside* a certificate or an inversion step (the script marker covers walks and the root strip only); the coordinate rails.

---

## 9. Assumptions (confirmed by Zachary) and open items

**Assumptions (all confirmed by Zachary):**
1. Grids placed side by side are treated as adjacent: two grids form one 20-wide double grid with continuous rows (Hobby, Serious).
2. Fingers hold a place within a pass, and cursor ships are parked before letting go.
3. One peg hole per ship cell (only relevant to fleet keys, which this design does not use).

**Other stated assumptions:** 1 move per second for hand time; the uniform shared-point model for the fold (§6); physical privacy (§7.2).

**Open:**
- Is 7 bands minimal? (Measured, not proven.)
- §7.1 class (ii): what a receiver that skipped the curve test would compute is not analysed (moot with the curve test).
- Summation-polynomial / index-calculus attacks in characteristic 3: literature-based, unverified.
- The 3√q character-sum constant is the reviewer's proof, not re-derived here.
- BS main has since removed letting go from its §3.1 calling (#175); ECBS keeps the #152-as-revised rule with cursor ships and resume (§5.2).

---

## 10. Files

Runnable spec: [`ecbs.sudo`](ecbs.sudo). Evidence index: [`proofs/key_exchange/ecbs/README.md`](../../../proofs/key_exchange/ecbs/README.md). In short: `evidence/` (drivers of the generated code: full exchanges, soundness, calling, §7.1), `vectors/` (known-answer vectors, PARI cross-check), `oracle/` (PARI), `lean/Generated/` (emitted Lean, TAP), `core/` (curve, tiers, extractor, twists, budget analysis; draft logs), `card/`, `demo/`, `twist/` (Phase-1 logs), `trace-check/` (the losing option, docs and logs), `review/` (the Mathematician's review, read-only), `MATH_REVIEW.md`, `HISTORY.md`.

## 11. `ecbs.sudo`

[`ecbs.sudo`](ecbs.sudo) models the board literally, as the card plays it, with the cost model of §2 in counters that never change a peg: GF(3ⁿ) arithmetic in the peg basis with the four taps (add, mirror, the lane fold, multiply, comb cube); the halving ladder and Itoh–Tsujii inversion with the tally and the quadratic-character sign; the curve side and curve test; the chord addition (Demo) and the F-form addition; the root strip and the base point by rule; the pegs-only key walk and the d10 row cup (§4); the certificate (make, rebuild, compare, reject on empty); calling with the phase hole, calling hole and cursor, resumable from the board; the exchange in card order; the fold per tier. Its sudo tests (Demo and Toy, values from PARI) run in JS and, emitted, in Lean. Known-answer vectors per tier (P, arithmetic, fold, certificate, walks, receiver verdicts, exchanges from dice to the folded key): [`proofs/key_exchange/ecbs/vectors/`](../../../proofs/key_exchange/ecbs/vectors/README.md), cross-checked against PARI. Nothing about the emitted Lean is proved (no Link 2).
