# ECBS (Elliptic Curve Battleship): pegboard ternary ECDH where the fleet is the private key

Zachary's idea: use Battleship grids as a ternary abacus, with empty hole = 0, white peg = 1, red peg = 2. The private key is one or more randomly placed fleets.

The feasibility bar is *theoretically* doable by hand, so years of work are acceptable. Every step must be a visual English recipe: no lookup tables, and no colour-to-number arithmetic.

## Terminology (used strictly throughout)

* **Grid:** one 10×10 grid of 100 peg holes. There are two kinds:
  - A **ship grid** (Hasbro's "ocean grid") is where a player places their ships.
  - A **target grid** is the upright one for recording shots.
  - For arithmetic, any grid is just 100 holes.
* **Fleet:** one set of 5 ships (lengths 5, 4, 3, 3, 2) placed on a ship grid, with a **white or red sign peg in each ship's peg holes**. That is 17 sign pegs, one per ship cell.
  - In ECBS, a fleet on its ship grid **is** (part of) a private key.
  - "G fleets" means G ship grids, each holding one fleet.
* **Game set:** one standard Battleship box, which is **4 grids + 2 fleets**. Each player gets 1 ship grid, 1 target grid and 1 fleet.
* **How the pieces map in ECBS:**
  - Each player's **ship grid(s) hold their secret fleet(s)**. Nothing else goes on a ship grid.
  - **Target grids, and any spare grids, are arithmetic workspace.**
  - A *register* is a row of n holes read in reading order. It may span several grids.
  - A *strip* is a longer temporary register used during multiply, cube and fold.
* **Paper:** idle registers can be copied to paper as W/R/blank strings ("photographs") and re-pegged later. This trades grids for copying moves.

---

ECBS is **one family with shared recipes**. All tiers use the same curve equation, the same peg rules, the same fold, cube and multiply recipes, the same cofactor strip and the same fleet walk. They differ only in three things:
1. **Register length n.** This sets the field GF(3^n) and the fold distances.
2. **Fleet count G.** This sets how much key entropy there is.
3. **Workspace grid count.** This follows from the first two.

The two headline tiers are:
* **ECBS-Toy:** 1 fleet. Each player's work fits in **their own ship grid + target grid (+ paper)**, so a single game set serves both players.
* **ECBS-Serious:** 6 fleets and ~26 workspace grids per player, about **8 game sets per player** comfortably.

**Code** (in `peg/`):
- `pegs.py`: the recipes, acting on colours only. They are parameterised by n and the fold rule.
- `reference.py`: independent integer arithmetic to check against.
- `tiers.py`: the full exchange for every tier. Output is in `tiers_output.txt`.
- `run_tests.py`: the original detailed ECBS-Serious run. Output is in `run_tests_output.txt`.
- `fleets.c`, `entropy.py`: fleet counts and key entropy.
- `alias.py`, `alias_enum.py`, `alias_swaps.py`: walk-aliasing loss (§2.4).
- `params.py`, `curves.py`: parameter searches.

**Marks:** [run] = computed here. [lit] = from a source found in this session. [est] = my estimate. [unverified] = from memory.

---

## 0. Summary

### The ECBS family at a glance [run unless marked]

All tiers use the curve **E: y² = x³ + 2x² + 1** (a = red peg, b = white peg) and cofactor **5**. Group size is #E = 5·ℓ with ℓ prime.

**Per-player requirements.** Both players need the same kit, since they work in parallel.

| Tier | n (register length) | Fold rule | Fleets (= ship grids) | Workspace grids: minimum† / comfortable‡ | Total grids per player: min / comfortable | **Game sets per player**: min / comfortable | ℓ | Security | Peg moves per person / whole exchange | Hand time per person @ 1 move/s, 8 h/day |
|---|---|---|---|---|---|---|---|---|---|---|
| ECBS-Demo | 7 | 7 back & 2 back | 1 | 1 / 1 (no paper) | 2 / 2 | **½ / ½** (own ship grid + target grid) | 9-bit (421) | none (~2^2) | 31.7 k / 63 k | ~1 day |
| **ECBS-Toy** | **23** | 23 back & 20 back | **1** | **1 + paper** / 4 | **2** / 5 | **½ (own ship grid + target grid + paper)** / 2 | 35-bit | ~2^14 (rho); a laptop breaks it instantly | **167 k / 334 k** | ~6 days |
| ECBS-Hobby | 59 | 59 back & 42 back | 2 | 3 + paper / 9 | 5 / 11 | 2 / 3 | 92-bit | ~2^42 (rho); a PC in days [est] | 1.67 M / 3.34 M | ~2 months |
| **ECBS-Serious** | **179** | 179 back & 120 back | **6** | 8 + paper / **26** | 14 / 32 | **4 / 8** | 282-bit | **~2^136** (rho with Frobenius and negation) | **38.4 M / 76.9 M** | ~3.7 years |

† Minimum workspace: the cubing strip (3n − 2 holes) plus one live register (n holes). The other 10 registers are kept on paper.
‡ Comfortable workspace: all 11 live registers (11n holes) plus the cubing strip, pegged at once. The product strip (2n − 1 holes) reuses the cubing strip's holes.

**How the game-set counts work.** Each game set supplies 4 grids and 2 fleets. The per-player count is the larger of the grid need and the fleet need:
* **Serious, comfortable:** 32 grids needs 8 sets. The 6 fleets would need only 3.
* **Serious, minimum:** 14 grids needs 4 sets.
* **Hobby:** 2 fleets need 1 set. 5 or 11 grids need 2 or 3 sets.
* **Toy and Demo:** one player's half of a set.
* **Both players:** double the per-player numbers, except that Toy and Demo need just **one game set in total**.

**ECBS-Toy on one player's half of a game set:**
* The **ship grid** holds the fleet (17 sign pegs in the ships), i.e. the key.
* The **target grid** (100 holes) holds the 67-hole cube/product strip plus one live 23-hole register: 90 holes used.
* The other ten registers live on paper as 23-character W/R/blank strings.
* Fully pegged Toy, with no paper, needs 253 + 67 = 320 workspace holes, i.e. 4 grids.
* The ship grid's 83 uncovered holes are **not** used as workspace, so a stray peg can never be mistaken for key material. Using them would still leave Toy short of 320 holes.

**ECBS-Demo** fits without paper: 11·7 + 19 = 96 holes on the target grid.

**Key findings:**
* **The tiers fall out naturally.** For prime n < 200, the curve y² = x³ + 2x² + 1 has cofactor exactly 5 with a prime ℓ **only for n = 7, 23, 59 and 179**, and each of those n has a "+ +" fold trinomial [run, `curves.py`/`tiers.py`].
  - So Demo, Toy, Hobby and Serious are the complete same-curve family with registers under 200 holes.
  - No other intermediate tier exists without changing the curve.
  - Off-family options, with a different b peg and cofactor, and hence a different cofactor strip:
    - n = 83 (cofactor 2, rho ≈ 2^61.4)
    - n = 193 (cofactor 2, ≈ 2^148)
    - n = 199 (y² = x³ + x² + 1, cofactor 6, ≈ 2^152) [run]
* **Fleet count is an independent knob.** Security ≈ min(curve rho, key-set square root). The key-set square root is ≈ (50.6·G − aliasing loss)/2 bits (§2.4).
  - The recommended G is the smallest that stops the fleets from being the bottleneck.
  - Toy and Demo: 1 fleet, because the group is smaller than the key set anyway.
  - Hobby: 2 fleets. With 1 fleet, a meet-in-the-middle attack over the ships costs ~2^26.6, below rho's 2^42.
  - Serious: 6 fleets. With 5 fleets, security is marginal at ≈ 2^126.5. A 7th fleet is optional extra margin against walk aliasing (§2.4), at about +17% work.
* **Verified end to end for every tier [run, `tiers.py`]:**
  - Peg multiply, cube and invert match the reference 20/20 each.
  - Public keys equal the reference a·P.
  - Both on-curve checks pass.
  - Alice's and Bob's shared x-registers agree and equal the reference 5ab·P.
* **Only ECBS-Serious is cryptographically meaningful.** Toy, Demo and Hobby are teaching tiers.
  - Toy's honest value is showing the *hand-vs-hand* gap. Eve doing rho by hand needs ~2^14 point additions (≈ 5·10⁷ moves [est]), about 300× the honest work.
  - A computer breaks Toy in milliseconds.
* **Everything else that fits on the grids is broken or much weaker** (§4):
  - Plain DH in GF(3^n) for n ≤ 200.
  - Prime-field DH with p ≤ 3^200.

---

## 1. What is shared and what changes per tier

**Identical in every tier:**
* **Peg colour rules** R0–R2 (colour wheel, drop, mirror, add). See §3.
* **The fold recipe R3.** "Working from the far end back to hole n, lift each peg and drop it **n holes back and (n − k) holes back**." Only the two distances change per tier: 7/2, 23/20, 59/42, 179/120.
* **The multiply (R4) and cube (R5) recipes.** Strips are 2n − 1 and 3n − 2 holes.
* **The curve**, the point-addition script (R7), negation (mirror Y) and Frobenius (cube X, Y, Z).
* **The cofactor strip.** Walk "white, red, white, red" over the received point to get 5·B. The same strip works in every tier, because every tier has trace −1 over F₃, so 5 = τ³ − τ² + τ − 1 [run].
* **The fleet walk R8 and the dice placement procedure.** Every fleet is a standard 5, 4, 3, 3, 2 fleet on a 10×10 ship grid, with a white or red sign peg in every ship peg hole.
* **The point checks (R9) and the exchange script (R10).**

**Changes per tier:**
* **n and the fold distances.**
* **The inversion chain (R6).** It follows the binary digits of n − 1. Toy's chain is literally the first half of Serious's:
  - Demo (6 = 110): ×1, +1, ×3.
  - Toy (22 = 10110): **×1, ×2, +1, ×5, +1, ×11**.
  - Hobby (58 = 111010): ×1, +1, ×3, +1, ×7, ×14, +1, ×29.
  - Serious (178 = 10110010): **×1, ×2, +1, ×5, +1, ×11**, ×22, ×44, +1, ×89.
* **G (the number of fleets, i.e. ship grids)** and hence the number of walk cells, 100·G.
* **The public base point P**, which is published once per tier.

**Graduating from one tier to the next** changes no rule. You use longer registers, set different fold distances, place more fleets and add more game sets.

---

## 2. Private key = fleets

### 2.1 How many fleets are there? Exact counts [run, `fleets.c`]

These count the standard fleet 5, 4, 3, 3, 2 on a 10×10 ship grid, with ships labelled (the two 3-ships count as different ships).

| Rule | Labelled placements | log₂ |
|---|---|---|
| Touching allowed, no overlap (Hasbro rules) | **30,093,975,536** | 34.81 |
| No touching, even diagonally | **3,851,502,784** | 31.84 |

* **The key depends only on which cells are covered**, so labelling adds nothing.
  - *Touching allowed:* one covered-cell pattern can come from 2 to 34 labelled placements [run, 20k Monte Carlo samples]. So there are about 1.37·10¹⁰ distinct patterns, and the **entropy under uniform placement is ≈ 33.6 bits**.
  - *No touching:* each pattern comes from exactly 2 placements (swap the 3-ships), giving **30.84 bits**.
* **Sign pegs:** a white or red peg on each of the 17 ship cells, chosen by coin (randomizer kit, 2026-09-30: a d8 per two cells, §2.3), adds exactly **17 bits**. That gives **≈ 50.6 bits per fleet** (touching allowed).
* **One fleet is hopeless.**
  - Brute force is only 2^34.8 candidate scalars.
  - Worse, the scalar is a *sum* of per-ship contributions. Meet-in-the-middle over the ships costs about √(120·140·160·160·180) ≈ 2^18 [run], i.e. seconds on a computer.

### 2.2 How many fleets are needed? [run, `entropy.py`]

Target (ECBS-Serious): 128-bit security. Rho on the n = 179 curve already caps security at 2^136. For the smaller tiers, the target is just "not below the curve's own rho": ECBS-Toy needs ≥ 28 bits (1 fleet gives 50.6), and ECBS-Hobby needs ≥ 84 bits (2 fleets give 101.2). Square-root attacks on the key set cost about 2^(entropy/2), so we need about 256 bits of entropy or more.

| Fleets (G) | With sign pegs: entropy / MITM by ships | Without signs: entropy / MITM |
|---|---|---|
| 1 | 50.6 bits / 2^26.6 | 33.6 / 2^18.1 |
| 4 | 202.4 / 2^106 | 134.4 / 2^72 |
| 5 | 253.0 / 2^133 | 168 / 2^90 |
| **6 (recommended)** | **303.6 / 2^159.5** | 201.6 / 2^108.5 |
| 8 | 404.8 / 2^213 | 268.8 / 2^144.7 |

* **Recommendation: 6 signed fleets (7 for extra margin against walk aliasing, §2.4).** The entropy figures in this table are *raw* fleet entropy, before the aliasing loss of §2.4. G = 5 is marginal: 253 bits of entropy gives an entropy/2 bound of ≈ 126.5.
* **An 8-fleet unsigned version also clears the bar** (~134 bits by the sqrt bound), if sign pegs feel un-Battleship-like. It costs a few more ship grids (and a second game set's fleets) but no more work: 8×17 = 136 additions against 6×17 = 102.
* **The MITM column is deliberately generous to Eve.** She enumerates unconstrained half-fleets and ignores overlaps. The more conservative figure is entropy/2 (151.8 bits for G = 6).
* **Using the other half of the kit:** each player's target grid could hold random white/red/empty pegs, i.e. 100 random trits = 158.5 bits. One fleet (50.6 bits) plus one target grid is about 209 bits, so two such pairs would be enough. Those trits are just a random ternary key, though, which loses the "ships are the key" charm. It is an option, not the recommendation.

### 2.3 Distribution and bias caveats
* **Humans must not place the ships.** Human placements are far from uniform; their entropy is unknown [unverified: no measurement], and every bit counted above assumes uniform placement. Use dice. The randomizer kit was adopted 2026-09-30, approved by Zachary (`bs/RANDOMIZER_KIT.md` §4.3, verified by `bs/kit/ecbs13_kit.py`):
  1. For each ship in the order 5, 4, 3, 3, 2, **roll the d20**. Bottom half (1–10) lies across, top half (11–20) lies down. The **last digit** (0 = 10) is its row if across, its column if down.
  2. **Roll the along-die** for the ship's first (top or left) hole, re-rolling any number that would put the ship off the grid. Use the smallest die that can still put the far end in hole 10: **5-ship d6, 4-ship d8, 3-ships d8, 2-ship d10.**
  3. If the ship overlaps an earlier one, **pick up the whole fleet and start again from the 5-ship.** Touching is allowed; overlapping is not.
  4. When all five fit, go along the ship cells in walk order, **one d8 per two cells**. For the first cell, bottom half (1–4) = white peg and top half = red. For the second cell, odd = white and even = red.
  - **Same distribution as the former procedure**, which remains valid: a coin for orientation, d10s for row and column with off-grid re-rolls, and a coin per ship cell. Each ship is uniform on its 2·10·(11 − L) placements either way.
  - The kit needs 30.4 reads per fleet instead of 52.2, and 0.51 off-grid re-rolls instead of 3.95. The restart is unchanged.
  - Optional: the **rainbow queue**: throw a cup of same-shape dice, one per rainbow colour (red, orange, yellow, green, blue, purple). Each roll the recipe asks for takes the next colour still in the tray, and that die goes back in the cup once read. When none are left, throw the cup again. It is exact because the colour order is fixed before the throw and no die is read twice.
* **Why the full restart matters:** it makes the result exactly uniform over legal labelled fleets (horizontal and vertical positions are equally numerous). Retrying just the colliding ship would bias placements toward sparse grids. The acceptance rate is 0.389 [run], so expect about 2.6 attempts per board.
* **Scalar distribution:** the secret scalar is k = Σ ±λ^j mod ℓ, over the ship cells at walk positions j, where λ is Frobenius's eigenvalue.
  - Its support is at most 2^303.6 values in a group of size 2^282. It is **not** uniform on Z/ℓ, and I have no proof of closeness to uniform, only the heuristic that 102 signed terms spread well.
  - Covered-cell patterns are also not equiprobable: some arise from 34 labelled placements, others from 2. That is already in the 33.6-bit figure.
  - Centre cells are covered more often than corners. That is inherent to uniform placement and also already counted.
* **Frobenius rotations:** Eve can also attack φ^j(A), which corresponds to shifting the walk positions. Shifted fleets are generally not legal fleets, so I don't count a loss. A worst-case accounting would subtract ≤ log₂(2·179) ≈ 8.5 bits from 151.8, still above the 136-bit cap.

### 2.4 Walk aliasing: cells n apart act the same [run, `alias.py`]
**The issue (found while building the tiers).** On every tier's curve, Frobenius satisfies τ^n = 1 on the points, so λ^n ≡ 1 mod ℓ. The walk cubes once per cell, which means **walk positions j and j + n contribute the same power of λ**.

The secret scalar is therefore really k = Σ_r c_r λ^r over r < n, where c_r is the sum of the ±1 sign pegs at all walk positions ≡ r (mod n). Two different fleet tuples with the same vector (c_r) give **the same key**. This loses entropy *before* any mod-ℓ effects. How many walk cells share each residue:
* Serious: 600 cells onto 179 residues, 3–4 each.
* Hobby: 200 cells onto 59 residues.
* Toy: 100 cells onto 23 residues.

**Measurements [run].** The loss is H(fleets | c) ≈ log₂ of the number of signed fleet tuples consistent with c.

| Tier | Method | Result |
|---|---|---|
| Toy (1 fleet, n = 23) | ApproxMC projected model count, 1 key | 2^8.8 consistent fleets |
| Toy | Exact SAT enumeration (cap 4096), 2 keys | 904 (2^9.8) and ≥ 4096 (≥ 2^12) |
| Toy / Hobby | Lower bound: ships that can slide to another legal spot on their own grid with identical residues | mean 4.5 / 3.75 such ships per key |
| Serious (6 fleets, n = 179) | Lower bound: disjoint same-length ship swaps between two fleets that keep every residue sum unchanged (300 keys) | mean 6.3, max 11 per key, so the loss is ≥ ~6 bits on average |
| Serious / Hobby | ApproxMC and exact enumeration | **did not finish** within 50 min (timed out); no upper bound obtained |

**What this means per tier:**
* **Toy:** about 9–12+ bits lost out of 50.6, leaving ~38–41 bits. That is still ≫ the 28 bits needed to exceed the curve's 2^14 rho. **No change.**
* **Hobby:** ≥ ~4 bits lost out of 101.2. The design tolerates up to ~17 bits of loss before key-set attacks (entropy/2) drop below rho's 2^42. **Probably fine [est; not measured].**
* **Serious:** ≥ ~6 bits lost out of 303.6. The key-set bound stays above the 2^136.3 curve cap unless the true loss exceeds **~31 bits**.
  - I could not measure an upper bound.
  - The swap bound counts only one mechanism. Chains of swaps, sign cancellations (a white and a red at the same residue sum to zero), and a ship's pegs being attributed across three or four fleets all add more.
  - So I **flag this as unverified** [est: likely 10–30 bits].
  - **Conservative recommendation:** use **7 fleets** for ECBS-Serious. That gives 354.2 raw bits, so a 60-bit loss would still leave ≥ 2^147. The cost is +17 additions per walk (about +17% moves, ≈ 45 M per person). The minimum stays at 4 game sets per player (15 grids, 7 of the 8 fleets); the comfortable count becomes 9 sets (33 grids).
* **Why the obvious fixes don't help:**
  - Inserting idle cube steps between fleets only re-labels residues, and some pair of fleets always overlaps at a shift under 100 cells.
  - A different base point per fleet needs a cheap public multiplier. Cheap multipliers have short τ-expansions, which create exactly the same kind of collisions.
  - Aliasing is inherent to a "cube at every cell" walk over more than n cells.

---

## 3. The shared ECBS recipes (written for general n; tier values in brackets)

* **Layout:** a *register* is n holes in reading order (hole 0 first). It stores a polynomial: the colour in hole i is the coefficient of x^i.
* **Registers per tier:** [Demo 7, Toy 23, Hobby 59, Serious 179].
* **Why these fields:** prime degree avoids subfield and Weil-descent structure. Each tier's fold trinomial x^n = x^k + 1 is irreducible over GF(3), with k = [5, 3, 17, 59] [run]. Both extra coefficients are +1, so a folded peg is dropped **unchanged**, with no mirroring, in every tier.

**R0 Colour wheel.** empty → white → red → empty.

**R1 Drop a peg into a hole.** A white peg moves that hole one step forward on the wheel. A red peg moves it one step back.
* *Mirror* (negation) means treat white as red and red as white.
* *Subtracting* a peg means dropping its mirror.

**R2 Add register B into A.** Drop every peg of B into the same-numbered hole of A (R1). Subtract by dropping mirrors. There are no carries.

**R3 Fold (reduction).** Work from the far end of a strip back to hole n. Lift out each peg you meet and drop it twice: **once n holes back, and once n − k holes back.**
* Distances per tier: [7 & 2; 23 & 20; 59 & 42; 179 & 120].
* This is x^n = x^k + 1.
* Working from the far end means pegs dropped past hole n − 1 get folded again later.

**R4 Multiply A×B.**
1. Clear a (2n − 1)-hole product strip.
2. For every pegged hole i of B, lay a copy of A into the strip starting at hole i: as-is if B's peg is white, mirrored if red. Each laid peg is dropped (R1).
3. Fold (R3). Holes 0 to n − 1 are the answer.
* Cost ≈ 0.45·n² moves [run]: ≈ 240 (Toy), ≈ 14,500 (Serious).

**R5 Cube A (Frobenius, cheap in characteristic 3).**
1. Clear a (3n − 2)-hole spreading strip.
2. The peg in hole i jumps to hole 3i.
3. Fold.
* Cost ≈ 2.6·n moves [run], about 1/30 of a multiply at n = 179. It is linear because (Σaᵢxⁱ)³ = Σaᵢx^{3i} in characteristic 3.

**R6 Invert x (Itoh–Tsujii, cube-and-multiply).** The plan follows the binary digits of n − 1 (chains in §1).
1. Start with e = x.
2. Each "×m" step means: cube e m times, then multiply by the e you had before cubing. Each "+1" step means: cube e once, then multiply by x.
3. Finally cube e once to get the candidate inverse, then multiply it by x. The result (the "norm") is a single peg in hole 0. **If that peg is red, mirror the answer.**
* Why this works: the norm lies in GF(3)*, where both 1 and 2 are their own inverses.
* Cost (Serious): 11 multiplies and about 179 cubes, ≈ 242,000 moves [run].

**R7 Point operations** on E: y² = x³ + 2x² + 1 (the a-coefficient is red, the b-coefficient is white).
* **Frobenius on a point:** cube all three registers X, Y, Z.
* **Negate a point:** mirror its Y register.
* **Mixed addition** Q(X,Y,Z) + P(x,y), as a written script over named registers:
  1. v = x·Z − X
  2. u = y·Z − Y
  3. w = v − X − Z (in characteristic 3, 2t = −t, and a = 2)
  4. uuZ = u·u·Z; vv = v·v; vvv = vv·v
  5. A = uuZ − vv·w
  6. X′ = v·A; Y′ = u·(vv·X − A) − vvv·Y; Z′ = vvv·Z
* Cost: 12 multiplies. Peak workspace: 11 registers plus the strip.
* **If v comes out empty, stop.** That is the doubling or inverse case. It is negligible for Toy and above (≈ 17G/ℓ per walk). In ECBS-Demo (ℓ = 421) it happens often: the first simulated Demo fleet hit it [run]. The rule for Demo is "re-roll the fleet", because no doubling recipe is provided.

**R8 Secret walk (scalar multiplication).**
1. Take the G ship grids (fleets) in a fixed order, and on each grid read cells left to right, top to bottom.
2. At every cell after the first ship, first cube Q's three registers (R7 Frobenius).
3. Then, if the cell holds a ship: white peg → add P; red peg → add P mirrored.
* The first ship cell just sets Q = ±P with Z = one white peg in hole 0.
* That gives 100·G Frobenius steps and 17·G − 1 additions. At the end, convert to affine (1 inversion, 2 multiplies).

**R9 Checking the other side's point** (Wong 5.4 lessons).
* **On the curve?** Compute y·y and x³ + 2x² + 1, and compare the two registers peg by peg.
* **Clear the cofactor 5.** Run the R8 walk with the received point as the base, over a four-hole strip **white, red, white, red** (read left to right). Since 5 = τ³ − τ² + τ − 1 in Z[τ] [run], this computes 5·B. The same strip works in every tier.
* Why clearing matters: E(F₃) has 5 points, so order-5 points have *only hole 0 pegged*. A malicious order-5 point would leak (#white − #red ship pegs) mod 5, because Frobenius acts trivially on F₃-points.

**R10 The exchange.**
1. Alice publishes A = a·P and Bob publishes B = b·P, both affine.
2. Each checks the other's point (R9) and clears the cofactor.
3. Each walks their own fleets over the cleared point: K = a·(5B) = b·(5A).
4. The shared secret is K's x-register (n trits). Hash it before use.
* P is a fixed public base point of prime order ℓ for the tier. `tiers.py` generates one per tier [run]; in practice it would be published once.

**Normal-basis alternative (Serious).** A type-II optimal normal basis exists for n = 179: 359 is prime, 359 ≡ 3 mod 4, and ord₃₅₉(3) = 179 [run].
* In that basis, **cubing is a literal rotation** of a 179-hole ring, or just moving a start marker.
* The catch is multiplication: it becomes a cyclic convolution on a 359-hole mirror-symmetric ring, about 4× the work.
* Cubing is only ~5% of the cost, so the polynomial basis wins. I didn't check the other tiers for this.

---

## 4. Security analysis

### 4.1 Per tier [run for rho/ℓ; est for wall-clock]

Rho cost here is √(πℓ/4)/√(2n): Pollard rho, sped up by the Frobenius and negation classes.

| Tier | ℓ | Rho cost | Key-set √ (entropy / 2) | Security | Who breaks it |
|---|---|---|---|---|---|
| ECBS-Demo | 421 | ~2^2 | 25.3 | none | anyone, by listing multiples of P |
| ECBS-Toy | 35 bits | 2^14.1 | 25.3 (1 fleet) | ~2^14 | any computer, instantly; by hand, ~300× the honest work [est] |
| ECBS-Hobby | 92 bits | 2^42.0 | 50.6 (2 fleets) | ~2^42 | a PC in days, faster with a GPU [est, not run] |
| ECBS-Serious | 282 bits | 2^136.3 | 151.8 (6 fleets) | **~2^136** | nobody, by generic attacks |

* **Other checks for n = 23, 59, 179 [run]:**
  - Trace −1, so the curves are ordinary.
  - None is anomalous.
  - The embedding degree is > 999, so MOV is irrelevant.
* **ECBS-Demo** has embedding degree 15, which is irrelevant at 9 bits.

### 4.2 Alternatives that fit on Battleship grids
| Option | Fits | Best attack | Security |
|---|---|---|---|
| DH in GF(3^n), any n ≤ 200 (≤ 317-bit field) | 2 grids | Small-characteristic DLP. Heuristic quasi-polynomial: Barbulescu–Gaudry–Joux–Thomé, EUROCRYPT 2014 [lit]. Rigorous: Kleinjung–Wesolowski 2019, (pn)^{2log₂n+O(1)} [lit]. Records: GF(3^{6·509}), 4841 bits, 2016, ~220 CPU-years (Adj et al.) [lit]; prime-degree GF(2^1279) in < 4 core-years, 2014 (Kleinjung) [lit] | **Broken.** A 315-bit small-characteristic field is far below 1990s function-field-sieve records (e.g. GF(2^401), 1992 [unverified]) [est: core-hours or less] |
| Prime-field DH, p ≤ 3^200 (≤ 317 bits), balanced ternary with carries | 2 grids | Number field sieve. Record: 795-bit p (2019, ~3100 core-years) [lit] | **Broken** [est: core-hours to core-days with public NFS software; not run] |
| Prime-field DH at 3072 bits (128-bit security) | 1938 trits per register, ~20 grids each | Number field sieve | OK, but ≈ 380 multiplies of ~3.5 M moves each ≈ **1.3·10⁹ moves per exponentiation** [est], ~70× the ECDH cost |
| ECDH over GF(3^83), cofactor 2 (off-family) | 83-hole registers; 165-hole product strip | Rho ≈ 2^61.4 [run] | Weak. Public ECDLP records are ~112–117-bit groups [unverified]; 2^61 is within reach of a determined effort |
| **ECBS-Serious: ECDH over GF(3^179), Koblitz, 6 signed fleets** | 179-hole registers | Rho 2^136.3 (key-set sqrt ≥ 2^151.8) | **~2^136 generic** |

### 4.3 Caveats (pedantic; they apply to every tier, and matter only for ECBS-Serious)
1. **Characteristic 3 is unusual.** No standard curve uses GF(3^n), and ordinary curves there have had less scrutiny than prime-field or binary curves. Smart (J. Cryptology 12, 1999) studies exactly this setting: curves over small odd-characteristic fields with Frobenius expansions [lit].
2. **Subfield (Koblitz) structure.** Frobenius and negation shrink rho by √(2n) ≈ 2^4.2; that is already in the 136.3. There is no Weil descent (GHS), because that needs composite n, and 179 is prime [lit/standard]. Summation-polynomial index calculus (Semaev, Gaudry, Diem, Petit–Quisquater) is heuristic, and I know of no practical attack at prime n of this size [unverified].
3. **Checked properties [run]:**
   - t = −1, so the curve is ordinary (not supersingular; supersingular curves would move DLP into GF(3^{6n}), which is broken).
   - #E ≠ 3^n, so it is not anomalous.
   - The embedding degree is > 50, so MOV is irrelevant. I only checked up to 50.
   - The cofactor is 5, and it is cleared.
4. **The key is not uniform on Z/ℓ.** It is a heuristic-only claim that this doesn't matter (§2.3). Security rests on the 303.6-bit raw entropy, minus the walk-aliasing loss of §2.4 (≥ 6 bits measured; upper bound not measured), and on the generic-attack assumption.
5. **Side channel: the work reveals the key.** Every ship cell triggers a big visible addition (12 multiplies), and every empty cell triggers none. **Anyone watching or timing the walk learns the fleet.** Work out of sight. A "constant-time" walk (a dummy addition on every empty cell) multiplies the cost by about 6.
6. **Human error.** One wrong peg ruins the result.
   - That breaks correctness, not secrecy. A bad public point fails the other side's on-curve check.
   - Recommended checkpoint: every ~10 additions, test the projective point on the curve, Y²Z = X³ + 2X²Z + Z³ (≈ 7 multiplies).
7. **Man in the middle.** Plain DH isn't authenticated (Wong ch. 5/7). Exchange public points in person or authenticate them.
8. **Certicom-style ECDLP record claims and the NFS time estimates are unverified.**

---

## 5. Move counts [run, `tiers_output.txt`; ECBS-Serious detail in `run_tests_output.txt`]

A "move" is one hole colour change, or one peg lifted or placed. Each simulation used one random fleet set per tier.

| Phase (moves) | Demo | Toy | Hobby | Serious |
|---|---|---|---|---|
| Alice public key a·P | 14.2 k | 75.3 k | 793 k | 18.81 M |
| Check B on the curve | 0.1 k | 0.8 k | 4.1 k | 27 k |
| Clear the cofactor (5·B) | 1.9 k | 14.7 k | 85 k | 0.76 M |
| Shared key a·(5B) | 14.7 k | 79.5 k | 795 k | 19.00 M |
| **Per person** | **31.7 k** | **167 k** | **1.67 M** | **38.4 M** |
| **Whole exchange** | 63 k | 334 k | 3.34 M | 76.9 M |
| Per person @ 1 move/s | 8.8 h | 46 h | 464 h | 10,700 h ≈ 445 days non-stop |

* **Scaling:** moves ≈ G·n² times a constant. The cost is dominated by 12(17G − 1) multiplies at ≈ 0.45n² moves each.
* **Serious breakdown:** ~92% multiplication inside point additions, ~5% cubing, ~1% inversion.
* **Earlier run:** the ECBS-Serious run in `run_tests_output.txt` (different random fleets) gave 77.2 M.
* **Possible savings (not simulated):**
  - Karatsuba at 1–2 levels: −25 to −45%, with a more complex recipe [est].
  - A sparser key: fewer additions, at an entropy cost.

**Workspace (holes)**

| Tier | 11 registers (holes) | Cube strip (holes) | Comfortable workspace grids | Minimum workspace grids (strip + 1 register) | Ship grids (fleets) |
|---|---|---|---|---|---|
| Demo | 77 | 19 | 1 | 1 | 1 |
| Toy | 253 | 67 | 4 | 1 (90 holes) | 1 |
| Hobby | 649 | 175 | 9 | 3 | 2 |
| Serious | 1969 | 535 | 26 | 8 | 6 |

* **Correction to my earlier ECBS-Serious "minimum 4 boards" figure:** 4 grids only hold the product strip. The cubing strip needs 535 holes, so the true minimum is 8 workspace grids.
* **Alternative:** cubing could be done as two multiplies on the product strip (no cubing strip), at ~60× the cube cost. That would make it 6 workspace grids minimum at n = 179 (357 + 179 holes) [est].
