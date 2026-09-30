# ECBS: Elliptic Curve Battleship (refined, no-paper, no-rulebook edition)

Diffie–Hellman on an elliptic curve over GF(3^n), done with Battleship pegs.
This refines Toymaster's draft (`PEGBOARD_TERNARY.md`) and folds in Toymaster's
later ideas (`TOYMASTER_IDEAS.md`), each **re-verified by my own scripts** in `kx-specs/ecbs/` before
adoption. None of the numbers here is copied from either source.

**Updated 2026-09-30** with Mathematician's review (`/workspace/mathematician-review/ecbs/REVIEW.md`) and **Zachary's key choice: pegs-only, 162 cells at Serious, "128-bit security, key-limited"**. The three-state encoding is dropped in every tier. What changed is listed first in §0.

**Tags.**
- [run: file] = computed by that script (output in the matching `_results.txt`).
- [proof] = a short argument written out in `ECBS_MATH_REVIEW.md`.
- [heuristic] = a standard but unproven model.
- [open] = I don't know.
- [lit] = literature, not re-checked.
- [review: mr_…] = computed or proved by Mathematician, not re-run by me (I re-ran the ones also tagged [run]).
- **[assume; confirmed by Zachary]** = a physical or house-rule assumption that Zachary has confirmed (listed in §9).

**House rules this spec obeys.**
1. Every step is a visual peg recipe, with no lookup tables and no colour arithmetic.
2. **No paper.** All working state lives in grids, pegs and ships.
3. **No printed rulebook.** Every rule is a short spoken English recipe (§3, collected in §8). Every constant is either spoken ("cube, minus square, plus one") or *derived on the board* (the base point, the chains).
4. Fingers may hold a place during a pass. Cursor ships must be parked before you let go (confirmed by Zachary).
5. Pegs are unlimited; only grids and fleets count. Hours of hand work are fine.
6. Claims are narrow, and each one names its assumptions.

---

## 0. What changed

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
| R10 | Key trits drawn from a bag (white peg, red peg, destroyer) | **Randomizer kit adopted (2026-09-30, approved by Zachary):** the key's trits come from the **d10 row cup** (§4). Same exactly uniform trits, so no entropy or tier figure changes; the all-empty re-draw is kept. A d6 per hole (1–2 empty, 3–4 white, 5–6 red) is the zero-reroll fallback, and the bag remains valid. `bs/RANDOMIZER_KIT.md` [run: bs/kit/randomizer_kit.py] |
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

---

## 1. Curve and tiers

**Curve.** E: **y² = x³ − x² + 1** over GF(3^n), said as **"y squared is x cubed, minus x squared, plus one."**
- This is the draft's y² = x³ + 2x² + 1 (a = 2, b = 1), since −1 = 2 in GF(3).
- Over GF(3), E has 5 points, trace t = −1, and Frobenius τ satisfies τ² + τ + 3 = 0 (discriminant −11).
- The point count uses the recurrence #E(GF(3^n)) = 3^n + 1 − V_n, with V₀ = 2, V₁ = −1, V_{j+1} = −V_j − 3V_{j−1}. It agrees with PARI `ellcard` for n = 2, 3, 4, 5, 7 [run: ecbs_curve].

| Tier | n | Tap x^n = x^k + 1 | Lane: width × band rows, less the last hole | Fold, as said | ℓ = #E/5 (proven prime) | log₂ℓ | Rho (negation + Frobenius) |
|---|---|---|---|---|---|---|---|
| Demo | 7 | k = 5 | 2 × 4 | "one band up and one on; one row up" | 421 | 8.72 | 2^2.78 |
| Toy | 23 | **k = 15** (was 3) | 8 × 3 | "one band up and one on; one row up" | 18828582139 | 34.13 | **2^14.63** |
| Hobby | 59 | **k = 39** (was 17) | 20 × 3 (a double grid) | "one band up and one on; one row up" | 2826077218347794449447657747 | 91.19 | **2^42.48** |
| Serious | 179 | k = 59 | 20 × 9 (a double grid) | "one band up and one on; **six** rows up" | 5078489869…5423907 (282 bits) | 281.39 | **2^136.78** |

Why the taps changed, and why that is safe:
- The lane layout needs n − k to be a whole number of rows. The only "+ +" irreducible tap with that property is k = 15 for Toy (8-wide rows) and k = 39 for Hobby (20-wide rows) [run: ecbs_layout §1 lists every irreducible trinomial; Toymaster's `trinomials.py` agrees].
- GF(3^n) is unique up to isomorphism and E is defined over GF(3). So #E, ℓ, λ, rho and every entropy certificate are unchanged [proof, review C1]. I re-ran them anyway [run: ecbs_curve, ecbs_exchange, ecbs_validation, ecbs_physical].
- What does change: the concrete base point and every test vector (regenerated, §5.1). Cubes cost more moves: Toy 80 → 105, Hobby 195 → 273 per cube; multiplies are unchanged [run: ecbs_layout §5]. Per exchange this is Toy +5 to +9 % and Hobby +4 to +8 % [run: ecbs_physical_costs, before/after].

Facts per tier, all [run: ecbs_curve]:
- Every n is prime and every tap trinomial is irreducible over GF(3).
- Every curve is ordinary (3 ∤ V_n) and none is anomalous.
- The **embedding degree** is 15 for Demo, and 2^29.6, 2^83.7 and 2^273.9 for Toy, Hobby and Serious. This rules out MOV/FR transfer, except as a curiosity at Demo.
- ℓ−1 is fully factored for every tier. The **quadratic twist and the invalid curves are weak** (Serious twist rho ≈ 2^57.7; Hobby E′ fully smooth). This is harmless only because y is sent and the curve equation is checked (§5.2, §7) [run: ecbs_twists].
- Exactly one root λ of x² + x + 3 mod ℓ satisfies λ^n = 1. Frobenius acts on ⟨P⟩ as multiplication by λ.
- **No GHS/Weil descent applies** (n prime, E defined over GF(3); magic number 1) [review Q5: lit + reasoning]. Summation-polynomial index calculus in characteristic 3: no analysis known; **literature-based, unverified** (review Q5).
- **Key target (Zachary's choice):** the key is deliberately the weak link. Serious: 162 cells, H∞ = 256.76, best modelled key search ≈ 2^128.4, below rho 2^136.78 by 8.4 bits. Headline: **"128-bit security, key-limited"** (§4).

---

## 2. Kit per player: lanes and a fixed workbench

**Layout** (Toymaster H1/D1, re-verified and measured here):
- A **register** is a band of a lane "less its last hole" (table in §1).
- **All multiplies and cubes happen on one fixed workbench**: a destination band plus two overflow bands. Serious: the workbench is 3 double grids.
- A finished result **slides** to a free register band: "same hole, other band".
- If an accumulate target lives in a band while the workbench holds something else, the two **swap** hole by hole: lift both pegs of a hole and put each in the other's place **[assume; confirmed by Zachary]**. The adopted F-form schedule never needs it (the no-swap run gives identical bands and moves) [run: ecbs_fform].
- Control pegs sit in spare holes (Toy: columns 9–10 and row J; Hobby and Serious: row J of each double grid; Demo: rows 9–10 of lanes 2–5).

**Measured peak** [run: ecbs_fform, pegs-only keys, every exchange checked against PARI]:
- **Walk (F-form, §3 R7): 7 register bands plus the workbench**, in every tier. The chord walk (Demo): 6.
- **Validation (lazy-y trace chain, §5.2): 7 plus the workbench**, in every tier.
- The old schedule on the same keys: 9 (walk) and 8 (validation); without the swap move 10 [run: ecbs_workbench, ecbs_workbench_noswap]. Not shown: that 7 is minimal.

**Grids per player** [run: ecbs_budget_fform = the unchanged ecbs_budget bookkeeping over the measured peaks and tallies of ecbs_fform]:

| Tier (budget) | Chosen key | Recipes | Workspace + key grids | Control holes needed / spare | Moves per person, incl. slides [run: ecbs_fform; Demo 20 runs, Toy 10, Hobby 5, Serious 5] |
|---|---|---|---|---|---|
| Demo (½ set = 2) | pegs-only 2 | chord walk, lazy-y trace chain | **1 + 1 = 2** | 17 / 24 | 3,724 (≈ 1.0 h) |
| Toy (5) | pegs-only 16 | F-form walk, lazy-y chain | **4 + 1 = 5** | 37 / 112 | 0.149 M (≈ 41 h) |
| Hobby (11) | pegs-only 51 | F-form walk, lazy-y chain | **8 + 1 = 9** | 57 / 80 | 2.02 M (≈ 561 h) |
| Serious (32) | pegs-only 162 | F-form walk, lazy-y chain | **20 + 2 = 22** | 121 / 200 | 44.89 M (≈ 12,470 h) |

- With the old schedule on the same keys: Demo 2 (with the trace walk; the old chain does not fit, 17 / 16), Toy 5, Hobby 9, **Serious 26** grids; moves differ by +0.2 % to +0.9 % [run: ecbs_budget_fform].
- Demo alternatives that also fit: chord walk + trace walk (6 bands, control 15 / 24, 4,960 moves). The F-form at Demo (7 bands) needs 25 control holes of 24, so it does not fit the ½ set.
- Pegs-only keys use **coordinate rails** (20 holes) in the key grid's unused holes, so no control holes go to rails in any tier.
- Slides are ≈ 17 % of the total at Demo, ≈ 13 % at Toy, ≈ 8 % at Hobby and ≈ 3 % at Serious [run: slide moves in ecbs_fform].
- Hobby and Serious need **double grids: two grids placed side by side and treated as adjacent, so their rows run on continuously** **[assume; confirmed by Zachary]**. The grids do not physically butt; the gap between them is treated as continuous. Demo and Toy lanes live inside single grids.
- Control inventory per tier: colour-flip tally (3 / 11 / 29 / 89 holes), a script-marker row (15 projective, 7 chord), the inversion ladder (2 / 4 / 5 / 7), the trace ladder (same lengths) and a protocol-phase marker (3). Rails (20) live in the key grid for pegs-only keys.
- The base point is derived on the board once per kit (§5.1). It then occupies one register pair like any live point.

---

## 3. Recipes (each is what a player says)

**R0 Colour wheel:** empty → white → red → empty. **R1 Drop:** a dropped white peg turns a hole one step round the wheel; a dropped red peg turns it one step back. Mirror = swap white and red.

**R2 Add / subtract:** drop every peg of A onto the same hole of B. To subtract, drop A mirrored.

**R3 Fold** (lane layout): "From the far end, lift each peg beyond the register. Drop it **one band up and one hole on**, and again **one row up** (Serious: **six rows up**). Pegs that land beyond the register are lifted again later."
- "One on" at a row's end means the first hole of the next row.
- Why it is right: with n = w·h − 1, "n back" is exactly h rows up and one hole on. With n − k = w·r, "n − k back" is r rows up [proof, review C18].
- Checked: 300/300 random strips per tier against the PARI-checked Board [run: ecbs_workbench A].

**R4 Multiply-accumulate** D += A·B, on the workbench:
- Take B's highest remaining peg and **lift it**. Lay A onto the workbench starting at the same hole as that peg (as-is if the peg was white, mirrored if red). Repeat, then fold (R3).
- If B is still needed, jump each lifted peg into an empty twin band instead.
- Slide the result to a free band ("same hole, other band"). (Swapping with the next accumulate target is allowed but the adopted schedule never needs it.)

**R5 Comb cube** (Toymaster C1): "Take the register's top row and comb it into the top band of the workbench, three rows tall, one peg on every third hole. Lay a cursor ship in the emptied row and the patrol boat in the first gap of the band you just filled. Then take the next row into the next band. When all rows are done, fold."
- The input is consumed; to keep it, copy it first.
- Checked: 300/300 cubes per tier, and the parked patrol boat never covered a peg [run: ecbs_workbench A]. The strip plus the 2-hole comb gap fits the workbench: Toy 69 ≤ 72, Hobby 177 ≤ 180, Serious 537 ≤ 540. Demo's workbench is lane 1 (20 holes); its 19-hole cube strip fits, and no gap is needed because Demo parks no ships.
- Demo has no spare ships; its rows are 2 holes, so fingers cover a pass.
- **Rejected alternatives** (item 2 of the brief):
  - No rigid motion of holes (rotation, reflection, any permutation) can be the cube in a polynomial basis. A single peg at hole i ≥ n/3 cubes to 2 or more pegs: 4 of 7, 15 of 23, 39 of 59 and 119 of 179 holes [run: ecbs_layout §3].
  - A normal basis turns the cube into a rotation (zero peg moves), but multiplying needs the Massey–Omura pair pattern, which is a table. Type-I/II optimal bases exist only for Toy and Serious; the Gaussian types are 4, 2, 12 and 2 [run: ecbs_layout §2].
  - The palindromic type-II basis ("mirror both ends; a peg on the anchor floods every hole") is correct but costs **×1.72 (Toy) and ×1.96 (Serious)** per multiply [run: ecbs_verse §2; Toymaster ×1.92 / ×2.01 in lays].
  - My earlier lockstep-ship spread (landing ship hops three holes per input hole) is also verified [run: ecbs_layout §4], but the comb is simpler and cheaper to park.

**R6 Invert (Itoh–Tsujii)** with a **halving ladder**:
- **Build the ladder once** from n − 1 pegs (a register less one more hole): pair the pegs off; a leftover peg makes a **red rung**, none a **white rung**; keep one peg per pair and repeat until one is left. Read the rungs from the last one.
- **Use it:** start with e = x and m = 1. On a white rung, e ← e^(3^m)·e and m doubles. On a red rung, do the same, then e ← e³·x and m gains one. Finally cube e and multiply by x: the product is a single peg in hole 0. If it is red, mirror the inverse.
- "Cube m times" uses the **colour-flip tally**: a row of m white pegs; each cube turns one red; stop when all are red. To double it, copy the row once more.
- The ladders are RW, WRRW, RRWRW and WRRWWRW, and they equal the Itoh–Tsujii programs [run: ecbs_basepoint].

**R7 Addition.**
- **Chord rule (Demo walk, and every receiver chain):** "Slope = rise over run. New x = slope squared, plus one, minus both x's. New y = slope times (old x minus new x), minus old y. Stop if the run is empty."
  - This is Wong ch. 5's picture; the "+ one" is −a.
  - One inversion per addition. Walk moves versus projective (old verse, three-state keys): Demo −11 %, Toy +11 to +21 %, Hobby +46 to +73 %, Serious +63 to +68 % [run: ecbs_walks].
- **Projective walk, the F-form: "the chord rule told from the base point"** (Toy, Hobby, Serious; adopted 2026-09-30 from the review's Q13, re-derived and re-verified here). Everything is measured from the base point (x₂, y₂), and the division is saved up in the bottom Z. In chord terms: *gap = slope² + 1 + run; new x = x₂ + gap; new y = −(y₂ + slope·gap).*
  1. **Run:** v = x₂·Z − X, written over X. *Stop if v is empty.*
  2. **Rise:** u = y₂·Z − Y, written over Y.
  3. **Gap:** F = u²·Z + v²·(v + Z). (Order on the board: u², times Z; v²; v² times Z, kept as "v²Z"; add v·v²; add v²Z.) This equals v²Z·(new x − x₂).
  4. **Bottom:** new Z = v·(v²Z).
  5. **New X** = v·F + x₂·(new Z).
  6. **New Y** = −(u·F + y₂·(new Z)).
  - For a red cell (−P), use y₂ mirrored in lines 2 and 6.
  - Same 12 multiplies as the retired 4-line verse ("the chord rule kept over a bottom", still correct [run: ecbs_verse §1]).
  - The identities (run, rise, gap = v²Z·(x₃ − x₂), X₃/Z₃ = x₃, Y₃/Z₃ = y₃, equal to PARI) hold for 50/50 random additions per tier [run: ecbs_fform §1; proof, review C25]. This line order *is* the measured 7-band schedule (§2) [run: ecbs_fform §3].

**R8 Walk:**
- Visit key cells **in reading order, fleets like pages, left to right.**
- At each cell: Frobenius the accumulator (comb-cube each coordinate; skip while it is empty), then that cell's addition (§4).
- **Where am I?** (Toymaster W1; fleet keys, i.e. only the six-state alternative now) "Arriving at an empty cell, stand a marker peg in its grid hole. Arriving at a ship cell, lift its sign peg into the parking hole; its colour says +P or −P. Leaving, pull the marker or put the peg back. When you let go, the one grid-hole peg on any ship grid, or the one empty ship hole, is your place, and it also says which fleet you are on."
  - Checked: 300 walks over 1, 2 or 6 fleets; digits read correctly 300/300; 0 ambiguous hands-off moments; key restored 300/300 [run: ecbs_workbench B].
  - This assumes **one peg hole per ship cell, and ships that cover their grid holes** **[assume; confirmed by Zachary]**.
- **Grid-hole keys** (pegs-only, the chosen encoding): **coordinate rails**, a marker in a 10-hole "letter" row and one in a 10-hole "number" row ("B-7"), in unused holes of the key grid.
- If an addition finds the run empty, **re-roll the key**. For pegs-only keys with m ≤ n − 3 cells this **never happens**, except for the all-empty key (probability 3^−m: 1 in 9 at Demo with 2 cells) [proof, review C28; run: ecbs_tiers, Demo exhaustive].

---

## 4. Key encoding: pegs-only (Zachary's choice, 2026-09-30)

**Model.** One Frobenius per step puts a digit on τ^e. On ⟨P⟩, τ acts as λ, and λ^n = 1. So k = Σ_r c_r λ^r (mod ℓ), where c_r is the sum of the digits whose exponent ≡ r (mod n). That sum is the Frobenius aliasing. With m ≤ n cells there is no aliasing at all.

**Recipe** (randomizer kit, 2026-09-30, approved by Zachary). "Fill the first m holes of the key grid row by row with the row cup. Walk the holes in reading order: Frobenius the accumulator, then add +P for white, −P for red." If every hole came up empty, roll the whole key again.
- **Row cup:** "At the start of each row, throw the five d10s (red, orange, yellow, green, blue) into the tray. Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each: red holes 1–2, orange 3–4, and on to blue 9–10. Picture a phone keypad (1 2 3 / 4 5 6 / 7 8 9, with 0 hanging below): the row a number sits in gives the first hole, the column gives the second. Top is empty, middle white, bottom red. When both of its holes are done, the die goes back in the cup."
  - **Partial rows:** throw only the dice the holes need. If the count is odd, the last die gives only its **keypad row** (the first hole).
  - Dice per key: Serious 162 → 81 d10s; Hobby 51 → 26 (the last one row only); Toy 16 → 8; Demo 2 → 1.
- **Exact:** faces 1–9 correspond one-to-one to pairs of trits (3 × 3), and a 0 is re-thrown on its own face only (rejection). Every hole gets an exactly uniform, independent trit, and H∞ below is unchanged.
- **Effort:** Serious 24.6 throws / 90.0 reads / 9.0 voids; Hobby 8.4 / 28.9 / 2.9; Toy 2.8 / 8.9 / 0.9; Demo 1.1 / 1.1 / 0.1 [run: `bs/kit/randomizer_kit.py`].
- **Position while filling:** the coordinate rails (§3 R8), plus the d10s still in the tray (colour ↔ hole pair of the current row).
- **Zero-reroll fallback (still valid):** a d6 per hole, 1–2 empty, 3–4 white, 5–6 red. The former bag (one white peg, one red peg and the destroyer, drawn with replacement) also gives exactly uniform trits and remains valid.
- **Optional:** the **rainbow queue**: throw a cup of same-shape dice, one per rainbow colour (red, orange, yellow, green, blue, purple). Each roll the recipe asks for takes the next colour still in the tray, and that die goes back in the cup once read. When none are left, throw the cup again. It is exact because the colour order is fixed before the throw and no die is read twice.
- Walk position: coordinate rails in unused holes of the key grid (§3 R8).

**Entropy measure.** Min-entropy H∞(k) of the scalar mod ℓ. For pegs-only with m ≤ n − 3 the map from cells to k is injective (Lemma A; exact threshold n − 3 per the review), so the key is **flat**: H∞ = Shannon entropy = log₂(3^m − 1) (all-empty key re-rolled), and min-entropy, guesswork and brute force all agree.

### 4.1 Cell counts per tier: key-limited

**Rule, the same in every tier** [run: ecbs_tiers]:
1. **Key-limited:** the *plain* baby-step giant-step count on the key set, 3^⌊m/2⌋ + 3^⌈m/2⌉ group operations (a concrete attack using no negation or Frobenius tricks), is below the curve's rho. Then the key, not the curve, is the weak link, and rho is margin.
2. **Headline h:** the cell count is the smallest with H∞ ≥ 2h. The "modelled best key search" (BSGS with the √2 negation saving and the √E[c] Frobenius saving of the rotation model, review Q3) then comes out at ≈ 2^h.
3. **Exact:** m ≤ n − 3, so H∞ is exact, not a bound.

| Tier | **Cells** | Key grid shape | **H∞ (exact)** | Plain BSGS | Modelled best key search | GGM floor † | Rho | Margin (rho − plain BSGS) | Headline |
|---|---|---|---|---|---|---|---|---|---|
| Serious | **162** | one grid + rows A–F + 2 holes of row G | **256.76** | 2^129.38 | **2^128.38** | 2^124.14 | 2^136.78 | +7.40 bits | **128-bit, key-limited** (Zachary) |
| Hobby | **51** | rows A–E + 1 hole of row F | **80.83** | 2^41.62 | **2^40.62** | 2^36.98 | 2^42.48 | +0.86 bits | 40-bit, key-limited |
| Toy | **16** | row A + 6 holes of row B | **25.36** | 2^13.68 | **2^12.68** | 2^9.92 | 2^14.63 | +0.95 bits | 12-bit, key-limited |
| Demo | **2** | 2 holes | **3.00** (8 keys) | 6 operations (2^2.58) | 2^1.79 | – | ≈ 6.9 iterations (2^2.78) | +0.20 bits | a demonstration, key-limited |

† Generic-group-model floor with free ±Frobenius, 2^((H∞ − log₂2n)/2) [review Q1, a model bound]. The 128-bit headline uses the rotation model; the GGM floor is 4.2 bits lower. Both are stated honestly; neither is a proof about real attackers.

**Why each count** [all figures run: ecbs_tiers]:
- **Serious 162 (Zachary):** the smallest m with H∞ ≥ 256; the modelled key search is 2^128.38, and plain BSGS (2^129.38) is 7.4 bits below rho. 161 cells gives 255.18 bits (modelled 2^127.80), below the headline. 128 is also the largest multiple of 8 that stays key-limited: a 136-bit headline needs 172 cells, whose plain BSGS (2^137.31) exceeds rho.
- **Hobby 51:** the headline is **40 bits**, the round number of the same kind as 128 (a multiple of 8) that stays key-limited: 51 is the smallest m with H∞ ≥ 80, and plain BSGS (2^41.62) is below rho (2^42.48). The next multiple of 8 (48 bits) is beyond the curve. 52 cells (82.42 bits, "41-bit") is also key-limited, with a 0.27-bit margin; 53 is not (2^43.21 > 2^42.48). The n − 3 threshold, 56 cells (88.76), is **curve-limited** (plain BSGS 2^45.38).
- **Toy 16:** the headline is **12 bits**, the largest whole-bit headline that stays key-limited: 16 is the smallest m with H∞ ≥ 24, plain BSGS 2^13.68 < 2^14.63. A 13-bit headline needs 17 cells, whose plain BSGS (2^14.68) misses rho by 0.05 bits; the n − 3 threshold, 20 cells (31.70), is curve-limited (2^16.85).
- **Demo 2:** the only key-limited count: BSGS takes 6 group operations against ≈ 6.9 rho iterations; 3 cells (26 keys) already takes 12. At Demo every attack is a handful of operations; the tier only demonstrates the mechanics. The n − 3 threshold, 4 cells (6.32 bits with the empty key re-rolled; 6.34 for 4 i.i.d. trits), is curve-limited.
- Near the n − 3 threshold, only Serious could be key-limited, and there Zachary's headline sits lower (162 < 176).

**Frobenius-aware key search** gains little on these key sets: E[c] = 2.000 (Serious 162), 2.006 (Hobby 51), 2.003 (Toy 16), 1.500 (Demo 2), so the saving is ≤ 2^0.50 [run: ecbs_tiers; matches review mr_frob].

### 4.2 Alternatives kept for reference (not chosen)
- **Pegs-only, curve-matching:** Serious 173 cells (274.20, modelled 2^137.23, the review's recommendation) or 176 (278.95, the exact threshold). Not key-limited.
- **Six-state, 2 grids:** H∞ ≥ 278.95 [review, via Lemma A], at +46 % moves. Uses fleets, so the W1 cursor.
  - Wording pitfall (checked): the literal draft wording "Frobenius, add ±P for peg; Frobenius again, add φ(P) if ship" gives τ²Q + τ(peg + ship)P, which collapses (white, no ship) with (empty, ship) [run: ecbs_entropy §3]. Correct forms: "F, ±P, F, +P if ship", or "F, F, ±P, +φ(P) if ship".

### 4.3 Dropped: three-state (fleet + sign pegs), in every tier
- **Rigorous upper bounds from pair cancellation** [review: mr_pairs, mr_fleets; not re-run by me]: H∞(k) ≤ **169.93** (Serious, 6 fleets), **207.01** (7 fleets), **57.96** (Hobby, 2 fleets), **25.06** (Toy, 1 fleet). Every one is below its tier's curve-matching target, and 6 and 7 fleets are below 256.
- The lower-side figure ≈ 77 bits (Serious, 6 fleets) is a **Monte-Carlo estimate** of a per-layout bound, not a proof.
- My earlier explicit heavy keys (≤ 225.48, 260.04, 74.35) remain valid but are much weaker bounds. The fleet counts are now exact (2^33.669 patterns; multiplicity 72 is the global maximum) [review].

---

## 5. Base point, exchange and receiver validation

### 5.1 The base point, derived on the board (Toymaster F3, re-verified)
"Put one white peg in hole 1 of x. Build the right-hand side: cube x, add x·x mirrored, and drop a white peg in hole 0. Take its root by the **root strip**. If y·y is not the right-hand side, slide x's peg one hole on and repeat. Finally walk **white, red, white, red** over (x, y): that is P."
- **Root strip:** y = rhs^((3^n+1)/4), which is a square root because 3^n ≡ 3 (mod 4). Its base-3 digits are **red, empty, red, empty, …, red, white** (n − 1 of them).
  - Walk it like a key: at each digit, cube y (skip while empty), then multiply by rhs² on red or by rhs on white.
  - Checked for all four n [run: ecbs_basepoint].
- **White, red, white, red** = τ³ − τ² + τ − 1 = 5 on this curve [proof, review C16]. Any R outside E(GF(3)) has 5R ≠ O, and 5R has order ℓ.
- **Results** [run: ecbs_basepoint, in pegs, checked against PARI]:
  - The first working hole is 2 (Demo, Toy) and 1 (Hobby, Serious).
  - P has order ℓ in every tier.
  - One-time cost at Serious ≈ 0.18 M (root strip) + 0.44 M (strip), about 1.4 % of one person's exchange (44.89 M).
- **Test vectors (regenerated; hole 0 first):**
  - Demo: x = `.RWR.WW`, y = `R..RRWR`.
  - Toy: x = `RW..W.WWWR..W...WWWRWRR`, y = `RRWWRRR..R.WRRW..RWWRRW`.
  - Hobby: sha256(x|y)[:16] = `e6635080e15e0cd7`; Serious: `345ec55420cdd25e`. Full registers are in `ecbs_exchange_results.txt`.
  - Earlier test vectors (random P, old taps) are void.

### 5.2 Exchange
1. Each player walks the key over P, giving A = aP (F-form projective walk, then go to affine with R6; Demo: chord walk). The partner copies A **peg for peg, x and y** (never x alone).
2. **Receiver checks on B** (pedantic choice: *reject*, never transform):
   1. **On-curve:** y·y against "cube x, minus x·x, plus one". **This is mandatory**, because the addition rules never use b. Skipping it leaks k mod a 120.3-bit number at Serious and the whole key at Hobby (§7) [proof, review C12; run: ecbs_twists]. **Never adopt an x-only variant.**
   2. **Trace (subgroup) check:** build the halving ladder from n (a full register of pegs: WRRWWRR at Serious). Compute S_m = B + τB + … + τ^{m−1}B along it: a white rung is S_{2m} = S_m + τ^m S_m; a red rung also adds S_{m+1} = τS_m + B (chord rule). **Accept iff one more Frobenius of S_{n−1} gives the mirror of B.** Reject on any exceptional case.
      - **Lazy y (adopted 2026-09-30):** in each chord addition, make the *second* point's y (the Frobenius copy of S's y, or the copy of B's y) only **after** inverting the run. On a red rung, keep S's y through the inversion and cube it afterwards. Same operations, reordered: peak 7 bands instead of 8 [run: ecbs_fform §2–3; review Q13].
      - It accepts exactly ⟨P⟩∖{O} [proof, review C11]. Demo, exhaustively: accepts exactly 420 of 2104 points.
      - Honest points accepted and B + T₅ rejected at Toy, Hobby and Serious; Demo exhaustive with the lazy-y chain: accepts exactly 420 of 2104, 0 misclassified [run: ecbs_fform §2, ecbs_review_checks (c)].
      - Cost at Serious ≈ 3.9 M moves including slides [run: ecbs_fform].
   3. **Demo alternative: the trace walk** (also fits the ½ set, 6 bands): walk n − 1 = 6 all-white cells over B (S ← τS + B), then one more Frobenius must give the mirror of B. The ruler is a free register slot. Exhaustive: accepts exactly the 420 subgroup points of 2104 [run: ecbs_walks]. The lazy-y chain is the default because it is the same recipe as the other tiers and cheaper at Demo (2,721 against 3,889 validation moves) [run: ecbs_fform].
3. Shared secret: K = a·B. Both sides agree in every simulated tier [run: ecbs_exchange, ecbs_physical, ecbs_workbench].
4. **Extract the key from K's x-register (§6).**

---

## 6. The x-register "hash": a fold, honestly an extractor

**Recipe (Serious):** "Fold the shared x-register: drop rows F–I onto rows A–D, same column. The key is rows A–E: 100 trits." Optional: "then also drop row E onto row A. The key is rows A–D: 80 trits."
- Other tiers: Hobby "drop row C onto row A" (40 trits) or "rows B and C onto row A" (20). Toy "row C onto row A" (16) or "rows B and C onto row A" (8).
- The fold is the F₃-linear surjection z_j = Σ_{i ≡ j (mod m)} x_i.

**What is claimed, and in which model** [run: ecbs_extractor, re-run 2026-09-30 with constant 3; review C19]:
- **Model: the uniform shared-point model.** K is uniform on ⟨P⟩∖{O}. **This is the only claim.** It is not implied by anything unconditional (K is determined by the public A and B), and **no DDH-type claim is made**: with key sets of H∞ below log₂ℓ, such a statement would be at best a generic-group heuristic [review Q11c].
- **Bound.** An F₃ XOR lemma gives SD ≤ ½·√(3^m − 1)·δ, where δ is the largest normalised character sum of x over the subgroup [review: stated correctly]. **δ ≤ 3√q/(ℓ−1)** for any subgroup, O excluded [review Q11a: proof via Weil II and Grothendieck–Ogg–Shafarevich; not re-derived by me]. The older Kohel–Shparlinski form 4√q [lit] is weaker.
- **Min-entropy.** Elementary fibre counting under the model gives Pr[z] ≤ 2·3^(n−m)/(ℓ−1).

| Tier | Output | Max bits | SD from uniform ≤ | H∞ ≥ |
|---|---|---|---|---|
| Serious | no fold (179 trits) | 283.7 | not close to uniform (only ≈ 1/10 of patterns occur) | **280.39 exactly** |
| Serious | **100 trits** (rows A–E) | 158.5 | **2^−59.7** | 155.2 |
| Serious | 80 trits (rows A–D) | 126.8 | **2^−75.5** | 126.8 |
| Serious | 60 trits | 95.1 | 2^−91.4 | 95.1 |
| Hobby | 40 / 20 trits | 63.4 / 31.7 | 2^−12.2 / 2^−28.0 | 60.1 / 31.7 |
| Toy | 16 / 8 trits | 25.4 / 12.7 | 2^−2.6 / 2^−9.0 | 22.0 / 12.3 |
| Demo | any | | vacuous | |

- **Per-trit bias** of any single output trit at Serious: SD ≤ 2^−138.4.
- Largest m with SD ≤ 2^−64 at Serious: 94 trits; with ≤ 2^−128: 13 trits (unchanged by the better constant). The bound, not necessarily reality, caps it. No hand-performable fold with a provably better m is known [review Q12].
- **Sanity checks** [run: ecbs_extractor]:
  - *Demo, exact:* the largest subgroup character sum is 1.41√q (bound 3√q), and the exact SD of the m-trit folds is 0.005 (m = 1) up to 0.90 (m = 7).
  - *Whole-group sums:* 2.25√q, 2.91√q and 2.85√q at n = 7, 11 and 13. These exceed 2√q but stay below 3√q; n = 11 comes within 3 % of it. (The prime subgroups at n = 11, 13 are smaller than 3√q, so their test is trivial.)
  - *Toy, Monte Carlo:* 200,000 samples of the 5-trit fold give χ² = 240.3 (df 242, p = 0.52), and the largest per-trit deviation is 0.0020. No gross bias; this cannot confirm a bound this small.
- **Not claimed:** random-oracle behaviour, DDH, security when K is not close to uniform, or anything for Demo, Toy or Hobby beyond the table. The fold adds no security; it only removes the visible structure of x. With the chosen key-limited keys the folded key's security is still the key's (≈ 2^128 at Serious), not the fold's.

---

## 7. Other attacks and limits
- **Rho:** as in §1. **Key search:** as in §4.1; with the chosen keys it is the best attack by design.
- **Frobenius-aware key search** on the chosen key sets: saving ≤ 2^0.50 (Serious 162), and similar elsewhere (§4.1) [run: ecbs_tiers; review: mr_frob, heuristic model tested exhaustively on small cases].
- **Descent and index calculus.** No GHS/Weil descent applies: n is prime and E is defined over GF(3), so the descent has magic number 1 [review Q5: lit + reasoning]. Summation-polynomial index calculus in characteristic 3 over a prime-degree extension: no analysis is known to me or the reviewer; **this rests on the literature and is unverified**. No attack beating rho is known [heuristic].
- **Twist and invalid curves** [run: ecbs_twists; review: mr_factor_check, mr_invalid_trace]:
  - Serious quadratic twist: fully factored, largest prime 115.4 bits, rho ≈ 2^57.7. Hobby twist: largest prime 39.3 bits.
  - The trace check passes exactly the odd part of the node (b′ = 0, index 4) and of E′ (b′ = 2, index 2). So if the on-curve check were skipped, an active attacker could learn, at **Serious, k mod a 120.3-bit number for ≈ 2^26.5 work (node) and a further 43.9 bits (b′ = 2)**, and at **Hobby the whole key for ≈ 2^14 (b′ = 2, fully smooth)**.
  - Therefore: **send y, check the curve equation, and never adopt an x-only variant.**
- **No authentication:** an active man-in-the-middle wins, exactly as in Wong ch. 5. Compare both public points over a trusted channel (for example, read the folded x-registers aloud in person).
- **Side channels:** additions happen only at peg cells, so anyone watching sees the key. A constant-work variant costs ≈ 1.5× for pegs-only (modelled at 175 cells) [model]. Physical privacy is assumed.
- **Hand time** @ 1 move/s (an assumption), per person, with slides, chosen keys and adopted recipes [run: ecbs_fform]: Serious ≈ 12,470 h; Hobby ≈ 561 h; Toy ≈ 41 h; Demo ≈ 1 h.

---

## 8. No-rulebook audit: every former reference and its memorable rule

| Former reference | Memorable rule now | Verified |
|---|---|---|
| Curve constants a = 2, b = 1 | "y squared is x cubed, minus x squared, plus one" | ecbs_curve, ecbs_basepoint |
| Tier sizes n | Register = lane band "less its last hole": 2×4, 8×3, 20×3, 20×9 | ecbs_workbench A |
| Fold offsets (n, n−k) | "One band up and one on; one row up" (Serious: six rows up) | ecbs_workbench A (300/300 per tier) |
| Reduction polynomial | Implied by the fold picture; nothing else uses it | ecbs_layout §1 |
| Cube hole 3i | Comb cube, "one peg on every third hole", two parked ships | ecbs_workbench A |
| Inversion chain (binary of n−1) | Halving ladder from "a register less one more hole" | ecbs_basepoint |
| Trace chain (binary of n) | Halving ladder from a full register | ecbs_basepoint |
| "Cube m times" count | Colour-flip tally (white turns red) | ecbs_physical |
| 12-multiply script | F-form: "the chord rule told from the base point" (6 lines, §3 R7): run, rise, gap, bottom, new X, new Y | ecbs_fform (old 4-line verse: ecbs_verse) |
| Chord rule | "Slope = rise over run …" (Wong's picture) | ecbs_walks |
| Base point P | White peg in hole 1 → root strip → slide on → white-red-white-red | ecbs_basepoint |
| Square-root exponent | Root strip "red, empty, …, red, white" | ecbs_basepoint |
| Cofactor 5 | "White, red, white, red" | ecbs_basepoint, review C16 |
| Walk order | Reading order; fleets like pages | ecbs_workbench B |
| Walk position | Rails in the key grid (pegs-only, chosen); marker peg / parking hole (fleet keys, six-state only) | ecbs_workbench B |
| Script position | One marker peg on the script row (a row of 15 or 7 holes) | ecbs_budget |
| Protocol phase | A marker in a 3-hole row | ecbs_budget |
| Receiver checks | "y·y against cube minus square plus one" (mandatory); "one more Frobenius must give the mirror"; "make the second y after the inversion" | ecbs_validation, ecbs_fform, ecbs_review_checks |
| Key randomness | Row cup: "keypad row gives the first hole, column the second; top empty, middle white, bottom red; 0 is thrown again" (fallback: a d6 per hole, 1–2 / 3–4 / 5–6). Adopted 2026-09-30, approved by Zachary | bs/kit/randomizer_kit.py |
| Key-cell counts | Grid shapes: Serious 162 = a grid plus rows A–F plus two holes; Hobby 51 = rows A–E plus one hole; Toy 16 = row A plus six holes; Demo 2 holes | ecbs_tiers |
| "Hash the x-register" | "Drop rows F–I onto rows A–D; keep rows A–E" | ecbs_extractor |
| Test vectors | None printed; the derived P is self-checking (y·y = rhs; trace check on P) | ecbs_basepoint |

**Remaining flags:**
- A player must *remember* the four lane shapes, the Serious "six rows up", the six F-form verse lines, the lazy-y rule and the three ladders' building rule. These are spoken rules, not tables. Whether that is memorable enough is Zachary's call.
- The walk-cell script row still needs 15 marker holes (projective) or 7 (chord).
- Exceptional-case re-rolls cannot happen with the chosen pegs-only keys, except the all-empty key (re-drawn).

## 9. Assumptions (confirmed by Zachary) and open items

**Assumptions (all confirmed by Zachary):**
1. *Confirmed:* **one peg hole per ship cell**, with ships plugging into (covering) grid holes, as on the classic ships. W1 depends on this; with the chosen pegs-only keys W1 is not used (rails in the key grid instead).
2. *Confirmed:* **grids treated as adjacent.** Grids placed side by side do not physically butt, but the gap between them is treated as continuous, so two grids form one 20-wide double grid with continuous rows (Hobby, Serious). Fallback for Hobby: none found in 11 grids.
3. *Confirmed:* **swap move:** two registers exchanged hole by hole, with a peg in each hand. The adopted F-form schedule does not need it (7 bands with or without) [run: ecbs_fform].
4. *Confirmed:* fingers hold a place within a pass, and cursor ships are parked before letting go.

**Other stated assumptions:** 1 move per second for hand time; the uniform shared-point model for the fold (§6); physical privacy (§7).

**Open:**
- Is 7 bands minimal for the walk and for validation? (Measured, not proven; no 6-band schedule found.)
- Summation-polynomial / index-calculus attacks in characteristic 3 on prime-degree extensions: literature-based, **unverified** (§7).
- The 3√q character-sum constant is the reviewer's proof; I have not re-derived it (every computed spectrum agrees).
- The 128-bit headline uses the Frobenius rotation model (2^128.38); the rigorous generic-group floor with free ±Frobenius is 2^124.14 (§4.1).

## 10. Files
Everything is in `kx-specs/ecbs/`, run with the venv `/workspace/.venv-ecbs` (cypari2, python-flint, sympy, gmpy2, numpy, mpmath):
- **New after the math review (2026-09-30):**
  - `ecbs_tiers.py`: key-limited cell counts, exact E[c], BSGS / GGM / rho per tier, and the Demo exceptional-case check.
  - `ecbs_fform.py`: F-form identities (PARI), lazy-y receiver chain, full exchanges on the workbench board (spec vs F-form, with and without the swap), moves with slides.
  - `ecbs_budget_fform.py`: the unchanged `ecbs_budget` bookkeeping over the ecbs_fform peaks.
  - `ecbs_twists.py`: twist, E′ and node orders, factorisations and leak sizes.
  - `ecbs_review_checks.py`: the n − 2 relation, the Demo injectivity threshold, and the Demo exhaustive lazy-y check.
  - `ecbs_extractor.py` re-run with the constant 3 (the constant-4 output is superseded).
- **Earlier in this edition:**
  - `ecbs_workbench.py`: lane fold, comb cube, W1 cursor, and the old-schedule workbench peak and moves.
  - `ecbs_budget.py`: grid and control budget (old-schedule peaks).
  - `ecbs_basepoint.py`: base point, root strip, ladders and test vectors.
  - `ecbs_verse.py`: the old 4-line projective verse and the palindromic basis.
  - `ecbs_walks.py`: chord versus projective moves, and the Demo trace walk.
    - Its "workspace grids" column uses my superseded gap-band model; `ecbs_budget` / `ecbs_budget_fform` are authoritative.
    - Its DemoPB slide arithmetic is a no-overflow alternative at 0.107 M moves.
  - `ecbs_layout.py`: tap search, Gaussian normal bases, rigid-motion proof by count, my lockstep-ship alternative, and tap prices.
- **Re-run with the new taps and the rule-derived P:** `ecbs_curve.py`, `ecbs_exchange.py`, `ecbs_validation.py`, `ecbs_physical.py`, `ecbs_physical_costs.py`, and `ecbs_costs.py` (Toy and Hobby lines).
  - The "aligned/packed" totals in `ecbs_physical_results.txt` are superseded by `ecbs_budget_fform`.
- **Unchanged (tap-independent):** `ecbs_entropy.py`, `fleet_count.c`, `fleet_maxmult.py`.
- **Randomizer kit (2026-09-30, approved by Zachary):** `bs/RANDOMIZER_KIT.md`, verified by `bs/kit/randomizer_kit.py` (face rules, row-cup counts per tier).
- **Reviewer's scripts** (read-only, not modified): `/workspace/mathematician-review/ecbs/mr_*`.
