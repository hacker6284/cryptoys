# BS: Battleship Diffie–Hellman

Finite-field Diffie–Hellman (powers of 3 modulo a prime p), worked by hand on Battleship pegboards. The private exponent is by default one or more dice-rolled **pegs-only key grids** (a uniform trit in every hole). A three-state fleet key is kept as an optional themed variant for the toy tiers. BS is the prime-field sister of **ECBS** (`../PEGBOARD_TERNARY.md`) and reuses its conventions:
* holes empty/white/red = 0/1/2;
* the colour wheel;
* fold recipes;
* the key walk (pegs-only by default, following the ECBS review and the spike below);
* for the themed variant: dice-placed fleets with sign pegs, their entropy counts (≈ 33.6 bits of covered cells + 17 sign bits per fleet), and the meet-in-the-middle caveat on sum-of-ships keys.

The small tiers are deliberately weak. The goal is a working, honest DH that scales up by adding boards.

**Code** (in `bs/`):
* `bspegs.py`: the recipes. They act on colours only.
* `bsref.py`: independent integer reference and the dice fleet sampler.
* `bsparams.py`: prime search and verification.
* `run_bs.py`: arithmetic tests, malicious-value tests and full exchanges.
* `bigmul.py`: full-size multiplications for the real tiers.
* `tiers.py`: the tier table.
* `break_small.py` and `break_t2.c`: attacks on the toy tiers.
* `parity_check.py`: the error-detecting checksum.
* `fleet_entropy.py`: Rényi entropy of fleets.

**Outputs:** `params*.json/txt`, `run_output.json/txt`, `bigmul_output.json/txt`, `tiers_output.json/txt`, `break_small_output.txt`, `parity_check_output.txt`, `fleet_entropy_output.txt`.

**Marks:**
* **[run]** = computed in this session by the scripts above.
* **[lit]** = from a source I checked in this session.
* **[lit-mem]** = standard literature I cite from memory and did not re-fetch.
* **[est]** = my estimate.
* **[unverified]** = a plausible claim I did not check.

**Randomizer kit adopted (2026-09-30, approved by Zachary).** Key randomness now follows `RANDOMIZER_KIT.md`:
* **Pegs-only key grids (§4.0):** the d10 **row cup**. A d6 per hole stays valid as the **zero-reroll fallback**.
* **Themed fleets (§4.1):** d20 + along-die + sign d8s, replacing coin + d10s + a coin per ship cell.
* **Optional everywhere:** the **rainbow queue**: throw a cup of same-shape dice, one per rainbow colour (red, orange, yellow, green, blue, purple). Each roll the recipe asks for takes the next colour still in the tray, and that die goes back in the cup once read. When none are left, throw the cup again. It is exact because the colour order is fixed before the throw and no die is read twice.
* **Every key distribution is unchanged:** exactly uniform independent trits, and exactly uniform labelled fleets. So no entropy, cost or security figure in this document changes.
* Dice remain a source, not storage. Unused dice lying in the tray are allowed physical state; a die is never moved until it is used.
* Verified in `kit/randomizer_kit.py` and `kit/ecbs13_kit.py`.

---

## No-paper rule (hard constraint, added 30 Sep 2026)

**Nothing in BS may rely on paper.** Every register and every piece of state must live in physical grids, pegs and ships. A **kit** is half a classic Hasbro set: one player's ocean (ship) grid, target grid, 5-ship fleet, 42 red pegs and 84 white pegs. **1 game set = 2 kits** (4 grids, 2 fleets, 84 red and 168 white pegs [lit: Hasbro contents list]).

**Audit.** These are the places the earlier text relied on paper or off-board state, and what they became:

| Earlier text | Now |
|---|---|
| §1 A1: the fleet could be "marker pieces or a sketch" | The key always sits on its own grid (ocean grid for fleets, any grid for pegs-only) and is counted per player. |
| §6: idle registers as paper "photographs" | Removed. Every register lives on grids and is counted in the holes. |
| §6: the long toll "could be a printed card" | Removed. The toll is a register on grids (it was already counted). |
| Implicit: loop counters and positions in your head (which fleet cell you're on, which hole of B, A and the strip you're laying at) | **Cursor ships** plus a **10-hole control lane** (below). |
| Implicit: "pair off the whites" parity and the sub-step of the cell in your head | Pegs in the control lane. |
| §3 B9 and §9: "hash K" and "compare a short hash aloud" | BS now ends with K on the grid; hashing is outside BS. Key confirmation is done physically (§9). |
| Public values as "W/R/. strings" | The other player copies your published register peg by peg into their Y register (Y is free at that point; own A stays in X until copied). The trits may be read aloud, but they are never stored anywhere except pegs. |

Unchanged: dice are a randomness source, not storage. The two-peg toy tolls are part of the recipe (like "drop it n back and n−k back"), not state.

**Control state, made physical.**
* **Control lane:** 10 holes per player.
  - One peg in holes 1–6 marks the cell sub-step: square, cube product, hit-multiply 1, hit-multiply 2 (and, for six-state, ship-square and ship-multiply).
  - Hole 7 is the parity bit (white = odd).
  - Hole 8 is the phase: empty = public walk, white = check, red = shared walk.
  - Hole 9 is the "accumulator started" flag. Hole 10 is spare.
  - Fold progress needs no marker ("always the highest peg" is visible).
* **Cursors:** 4 cursors (fleet-walk cell, B hole, A hole, strip hole), each a pair of ships laid flat against a grid's frame. One ship points at the row, the other at the column; the ship type names the cursor.
  - That is 8 ships = **2 extra fleets per player**.
  - **Finger rule (confirmed by Zachary):** you may keep your place with a finger while laying, but **before you take your hands off, park the cursor ships**, so the table is always a complete record.
  - Parking costs only O(n) moves per multiplication, which is negligible. Moving the cursors on *every* peg instead would add about 2n² moves per multiplication, roughly doubling all hand times.
* **Peg supply is not a constraint.** Zachary: extra pegs can be bought. For provisioning, the measured peak pegs in use per player are T1 46 red / 45 white; T2 83 / 77; T6 212 / 212 [run, `bs/peg_supply.py`]. For big tiers it is ~0.36 per workspace hole of each colour, plus the key's ~33 ± 5 of each colour per key grid.
* **Game sets per player** = max(⌈grids/4⌉, ⌈fleets/2⌉). Grids and fleets only.
* **The default key is now pegs-only (§4).** The key is one or more **key grids**: any 10×10 grid with a dice-rolled peg in every hole (the d10 row cup, §4.0; a d6 per hole is the zero-reroll fallback). Each key grid is its own grid and is counted. No fleet is needed for the key, so a player's fleets are just the 2 cursor fleets.
* **T1:** the arithmetic still fits on one grid, exactly (90 register holes + the 10-hole control lane). With the key grid, a T1 player needs **2 grids, 2 fleets (cursors) = 1 game set**. The themed three-state variant needs 2 grids and 3 fleets = 2 game sets.

---

## 0. Summary

**The design**
* **Field:** a prime p = 3ⁿ − c. I call c the **toll**.
* **Reduction:** a peg that spills past the last hole of a register is lifted and replaced by a copy of the toll, laid n holes lower (twice if the peg was red). This is ECBS's fold, now with integer carries.
* **Toll size by tier:**
  - Toy tiers use a two-peg toll, c = 3ᵏ + 1. The fold is then "drop it n holes back and n−k holes back", word for word the ECBS fold.
  - Real tiers use a **long toll** of about n/2 trits, taken from the ternary digits of π. This avoids special-number-field-sieve weakness (§9).
* **Group:** every p is a **safe prime** (q = (p−1)/2 is prime) and **g = 3**. For every safe prime p > 7, 3 is a quadratic residue, so g = 3 generates the prime-order subgroup of size q.
* **Arithmetic** is plain ternary with an **odometer carry**: when a hole clicks from red over to empty, flick a white into the next hole up.
* **Multiplication** is ECBS's "lay a copy at every pegged hole" (twice for red), followed by paying the toll.
* **Key (default, pegs-only):** one or more **key grids**, each a 10×10 grid with a dice-rolled peg in every hole: the d10 row cup, keypad row and column = empty/white/red (§4.0). Fallback: a d6 per hole, 1–2 empty, 3–4 white, 5–6 red. Read in reading order, the key grids *are* your exponent written in ternary. You compute g^e by a left-to-right **cube-and-multiply walk**:
  - On every cell, cube the accumulator.
  - In the public phase, a white or red cell costs nothing: you just **nudge** the second cube product one hole (white) or two holes (red) higher, because multiplying by g = 3 is a shift.
  - In the shared phase, a white cell means one multiply by the base, a red cell two.
  - *Optional themed variant (toy tiers only):* the three-state fleet key (water / white-pegged ship / red-pegged ship), walked the same way.
* **Received-value check** (Wong §5.4): **square the received number first.**
  - If the square comes out empty (0) or a lone white in hole 0 (1), reject.
  - Otherwise the square has order q, and you walk your key grids over it.
  - The shared secret is K = 3^(2ab). This costs one multiplication.

**Tiers (details in §7).** Default pegs-only key, no paper. Security is the minimum of NFS, rho on q, and the key's √ bound. Moves are per person; hand time assumes 1 move per second.

| Tier | Grids per player (workspace + key) | Fleets | Game sets | p | Security | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|---|
| **T1 skiff** | **2 (1 + 1)** | 2 | **1** | 3¹⁸ − 3² − 1 (29 bits) | ≈ 2^14; **broken in 0.00 s** [run] | 2.3·10⁵ [run] | 63 h / 8 days |
| **T2 frigate** | **3 (2 + 1)** | 2 | **1** | 3³⁵ − 3²⁹ − 1 (56 bits) | ≈ 2^27; **broken in 6.8 s** [run] | 7.7·10⁵ [run] | 9 days / 27 days |
| T6 demo | 7 (6 + 1) | 2 | 2 | 159 bits | ~2^31 [est] | 9.3·10⁶ [run] | 107 days / 11 months |
| R1024 | 38 (36 + 2) | 2 | 10 | 1024 bits | 80 | 7.4·10⁸ | 23 years / 70 years |
| R2048 | 74 (72 + 2) | 2 | 19 | 2048 bits | 112 | 3.0·10⁹ | 94 years / 281 years |
| **R3072 serious** | **109 (107 + 2)** | 2 | **28** | 3072 bits | **128** | 6.6·10⁹ | **209 years / 626 years** |

The themed three-state variant is for the toy tiers only. T1 needs 2 grids, 3 fleets = 2 game sets, 1.7·10⁵ moves. T2 needs 4 grids, 4 fleets = 2 game sets, 1.3·10⁶ moves.

**Verified [run]**
* p and q are prime (Miller–Rabin with 50 rounds, plus BPSW; also deterministic Miller–Rabin for T1 and T2), and 3^q ≡ 1 (mod p), for T1, T2, T6, R512, R1024, R2048 and R3072.
* The peg recipes compute exactly what Python computes:
  - multiply: 300/300 (T1, T2) and 100/100 (T6);
  - multiply with nudge: 300/300 and 100/100;
  - tidy: every edge value;
  - full-size multiplications at 1024, 2048 and 3072 bits: 3/3 each.
* **End-to-end exchanges:** pegs-only keys 20 (T1), 5 (T2) and 1 (T6) [`pegsonly_output.txt`]; three-state fleets 20, 5 and 2. In every one, the public values equal pow(3, e, p), both parties get the same K, and K = pow(3, 2·e_A·e_B, p).
* **Received-value check:**
  - It rejects 0, 1, p−1 and p+1.
  - A non-residue is accepted but squared into the subgroup.
  - A victim who skips the check leaks e mod 2 to a p−1 attacker (4/4 trials).

**Caveats, in one breath**
* This is ~170× more hand work than ECBS for similar security. Finite-field DH is simply worse by hand than ECDH.
* The long-toll prime family fixes the top half of the digits. I know no attack on that, but nobody has reviewed it [est].
* The key is a short exponent: uniform on [0, 3^(100G)). Security rests on the standard short-exponent assumption with a safe prime.
* NFS precomputation is per-prime and amortises over all users of that prime (Logjam).
* Hand work leaks the key to watchers, one wrong peg ruins the result, and there is no authentication.

---

## 1. Explicit assumptions

* **A1. "One board" = one 10×10 peg grid of 100 holes**, holding every working register and all scratch space.
  - The key is *not* in those holes. A pegs-only key sits on its own key grid (themed variant: the fleet sits on its own ocean grid with sign pegs). Under the no-paper rule that key grid is counted, so T1 is 2 grids per player.
  - If a themed fleet had to occupy 17 of the 100 workspace holes, T1 would not fit: n = 16 has no safe prime of the two-peg shape [run, `params_output.txt`].
* **A2. Each key grid is its own grid** (pegs-only default: any grid; themed variant: an ocean grid with the fleet). Workspace grids carry no key. Cursor ships (2 fleets per player) lie against the frames (no-paper rule).
* **A3. A "move"** is one peg placed, one peg lifted, or one hole's peg swapped for another colour.
  - One carry is one more move.
  - Moving a register costs two moves per peg: lift and place.
  - Hand time assumes 1 move per second with no errors. Real humans are slower; multiply by 2–3 [est].
* **A4. Keys come from dice, never from humans** (randomizer kit, 2026-09-30, approved by Zachary). Pegs-only: the d10 row cup, or one d6 per hole as the zero-reroll fallback. Themed variant: fleets are placed by dice using ECBS §1.3's full-restart procedure (`../PEGBOARD_TERNARY.md` §2.3), now read with a d20 and an along-die. It gives exactly uniform labelled placements. Sign pegs come from d8s, two ship cells per die. Every entropy figure assumes fair dice and the rule followed exactly.
* **A5. Security is classical.** Shor's algorithm breaks every tier; that is out of scope.
* **A6. Standard hardness assumptions.** CDH and DLP in the order-q subgroup of F_p* are as hard as the best known algorithms (NFS, rho). For the long-toll primes, I additionally assume the fixed top half gives NFS no special advantage [est, §9].
* **A7. Work is done out of sight.** The pattern of work reveals the fleet (§9).
* **A8. Public values reach the other side authentically**: in person, or over an authenticated channel. Plain DH does not stop an active man in the middle (Wong ch. 5).

---

## 2. Parameters

### 2.1 Why p = 3ⁿ − c (the toll)
* A register holds n trits; hole i holds the digit of 3ⁱ.
* Because 3ⁿ ≡ c (mod p), a peg at hole h ≥ n is worth the toll laid starting at hole h − n. So reduction is **"lift and lay the toll lower"**, with no division.
* **Every legal toll has a white peg in hole 0:**
  - For a safe prime p > 7 we need p ≡ 2 (mod 3). (If p ≡ 1 mod 3, then 3 | 2q, so q = 3.)
  - That means c ≡ 1 (mod 3).
  - c must also be even, so that p is odd.
* **Two-peg tolls, c = 3ᵏ + 1 (toy tiers).**
  - The fold is: *lift, drop it n holes back and n−k holes back* (ECBS R3, verbatim).
  - Safe primes of this shape for n = 16…44 exist only at **n = 18 (k = 2), 30 (k = 4, 12), 31 (k = 1), 35 (k = 29)** [run]. There are none at n = 20 or 40, which is why the rows don't line up with 10-hole rows (§6).
* **Long tolls (real tiers).**
  - c = (first ⌈n/2⌉ ternary digits of π) + j, where j is the smallest offset that makes p a safe prime [run].
  - π = 10.0102110122…₃, so every long toll begins **W . . W . R W W . W R R R R …**
  - This is "nothing up my sleeve", like RFC 7919, whose primes fix the top and bottom 64 bits and take the middle from e [lit].
  - Anyone can regenerate every parameter with `bsparams.py`. That matters because trapdoored SNFS primes are a real thing (Fried–Gaudry–Heninger–Thomé, EUROCRYPT 2017 [lit]).

### 2.2 Why a safe prime with g = 3
* **The subgroups** of F_p* for p = 2q + 1 have orders 1, 2, q and 2q. The only small subgroups are {1} and {±1}.
* **3 generates the order-q subgroup.** p ≡ 3 (mod 4) (q is odd) and p ≡ 2 (mod 3), so p ≡ 11 (mod 12), and then by quadratic reciprocity (3/p) = +1. So 3 is a quadratic residue, and since 3 ≠ 1 its order is exactly q. I checked that 3^q ≡ 1 for every tier [run].
* **Multiplying by g is a one-hole shift.** That is why public-phase hits cost nothing (the nudge, B6).
* **Short exponents are fine with a safe prime.** Exponents are short: e < 3^(100G), far below q in the real tiers. van Oorschot–Wiener (EUROCRYPT '96) show that short exponents are dangerous when p − 1 has medium-sized factors, and that safe primes "preclude this particular attack" because a partial Pohlig–Hellman decomposition yields only one bit [lit]. Here even that bit is gone, because g is in the order-q subgroup.

### 2.3 Concrete parameters

| Tier | n (trits) | p | p bits | Toll | Checks [run] |
|---|---|---|---|---|---|
| T1 | 18 | 3¹⁸ − 3² − 1 = 387,420,479; q = 193,710,239 | 29 | white at holes 0, 2 | p and q prime (deterministic MR + BPSW); 3^q = 1 |
| T2 | 35 | 3³⁵ − 3²⁹ − 1 = 49,962,914,721,634,823; q = 24,981,457,360,817,411 | 56 | white at holes 0, 29 | same |
| T6 demo | 100 | 3¹⁰⁰ − (π₅₀ + 4383) | 159 | 50 trits, 40 pegs | MR-50 + BPSW; 3^q = 1 |
| R512 | 323 | 3³²³ − (π₁₆₂ + 108769) | 512 | 162 trits | same |
| R1024 | 646 | 3⁶⁴⁶ − (π₃₂₃ + 1052835) | 1024 | 323 trits, 230 pegs | same |
| R2048 | 1292 | 3¹²⁹² − (π₆₄₆ + 176296) | 2048 | 646 trits, 448 pegs | same |
| **R3072** | **1938** | **3¹⁹³⁸ − (π₉₆₉ + 1453486)** | **3072** | 969 trits, 663 pegs | same |

* π_t is the integer whose base-3 digits are the first t ternary digits of π.
* The full decimal values of p, q and c are in `bs/params.json` and `params_323.json`.
* In every big tier, q is a *probable* prime: Miller–Rabin with 50 rounds plus BPSW, with no ECPP certificate. p follows from q by Pocklington in principle [not run].

---

## 3. The recipes (colours only)

Registers are strips of n holes. Hole 0 is first, and hole i is worth 3ⁱ. No step ever turns a colour into a number.

* **B0. Colour wheel:** empty → white → red → empty. One step is one **click**.
* **B1. Drop a peg (odometer carry).**
  1. A white peg clicks the hole once; a red peg clicks it twice.
  2. **Whenever a hole clicks from red over to empty, flick a white into the next hole up.** That flick is itself a drop, so it may carry again, like an odometer.
  - Examples: white into red gives empty plus a white next door. Red into white gives empty plus a white next door. Red into red gives white plus a white next door.
* **B2. Lay a copy of A starting at hole s:** drop each peg of A, in its own colour, into the hole s places further on.
* **B3. Multiply A × B.**
  1. Clear a product strip of 2n holes (2n + 2 in the public phase).
  2. For every pegged hole i of B, lay a copy of A starting at hole i: once if B's peg is white, **twice if it is red**.
  3. Pay the toll (B4). Holes 0 … n−1 are the answer; slide it into its register.
  - The strip can never overflow: A·B < 3^(2n), and partial sums only grow toward it.
* **B4. Pay the toll (fold).** Repeat until nothing sits at or beyond hole n: **lift the highest peg at or beyond hole n, and lay the toll starting n holes lower** (twice if the lifted peg was red).
  - *Two-peg toll:* drop the lifted peg's colour at h − n and at h − n + k.
  - *T1 example:* a white peg at hole 20 is lifted, and whites are dropped into holes 2 and 4, since 3²⁰ ≡ 3²·(3² + 1).
  - Carries from the laid toll can only land at or below the lifted hole: the value went down, and everything above was already empty. So "always the highest" terminates.
* **B5. Tidy (canonical form; needed only for published values and the final secret).**
  1. Copy the register into the strip, with one extra hole on top.
  2. Pour the toll into the copy.
  3. If a white spills into the extra hole, throw the spill away: the copy is the tidy answer. Otherwise keep the original and clear the copy.
  - This works because x ≥ p exactly when x + c ≥ 3ⁿ.
  - In the toy tiers, p itself looks like **all red except a white at hole k**. Tidying it gives the empty register.
* **B6. Cube, with a nudge.**
  1. Y = X × X.
  2. X ← Y × X.
  - In the *public phase* on a hit cell (white or red peg), lay every copy of the second product one hole higher (white hit) or two holes higher (red hit). That multiplies by 3 or 9 = g or g² for free.
* **B7. Key walk (the exponentiation).** A **hit** is a pegged cell: white or red. An empty cell is 0. In the themed variant a hit is a pegged ship cell, and water is 0.
  1. Take your key grids in a fixed order, and read the cells left to right, top to bottom. The walk cursor (2 ships) sits on the current key grid's frame.
  2. Before the first hit, do nothing (the accumulator is 1).
  3. At the first hit, start the accumulator X:
     - *Public phase:* a lone white peg at hole 1 (white hit) or hole 2 (red hit).
     - *Shared phase:* a copy of the base C (white), or C × C (red).
  4. At every later cell, **cube** (B6). Then, if the cell is a hit:
     - *Public phase:* the hit was the nudge; nothing else to do.
     - *Shared phase:* multiply by C once for white, twice for red.
  5. At the end, tidy (B5).
* **B8. Check the received number (Wong 5.4).**
  1. The number must have exactly n trits.
  2. Square it (B3), then tidy.
  3. **If the square is empty, or is a lone white in hole 0, reject.**
  4. Otherwise the square C is your base.
  - Squaring maps anything into the order-q subgroup. 0, 1 and −1 are exactly the inputs that fail.
* **B9. The exchange.**
  1. Alice walks her key grids with g = 3 and publishes A (tidy, n trits read as W/R/. from hole 0). Bob does the same and publishes B.
  2. Each checks and squares the other's number (B8).
  3. Each walks their own key grids over the square (B7, shared phase): K = (B²)^a = (A²)^b = 3^(2ab).
  4. BS ends with K on the grid. Any hashing or later use happens outside BS (no-paper rule).
* **B10. Optional error check: "pair off the whites" (casting out twos).** A register is odd exactly when it holds an odd number of white pegs, because every 3ⁱ is odd and a red counts as two.
  - *Before folding:* the strip has odd whites ⇔ A and B both have odd whites. A nudge changes nothing, because 3 and 9 are odd.
  - *While folding:* every lifted **white** flips the parity; lifted reds don't. (Lifting d·3^h and laying d·c·3^(h−n) subtracts d·3^(h−n)·p, and p is odd.)
  - It catches every forgotten carry and every wrong click count (each is off by an odd power of 3), and about 2/3 of random single-peg errors (63–69% measured, §8).

**Why plain ternary and not balanced.**
* Balanced ternary (red = −1) makes subtraction free, but BS never subtracts.
* It would clash with the exponent digits, where red must mean *two* (multiply by the base twice): a −1 digit would need the base's inverse, which costs a whole extra exponentiation for a received base.
* It would also make the canonical-form test sign-dependent.
* Plain ternary keeps ECBS's colour meanings: red is "two clicks".

---

## 4. The key

### 4.0 Default: pegs-only key grids (no paper)
* **Generation** (randomizer kit, 2026-09-30, approved by Zachary; `RANDOMIZER_KIT.md` §4.1): each key grid is a 10×10 grid of 100 holes, filled row by row. The walk cursor's row ship marks the row being filled, because empty holes leave no mark.
  - **Row cup (default):** "At the start of each row, throw the five d10s (red, orange, yellow, green, blue) into the tray. Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each: red holes 1–2, orange 3–4, and on to blue 9–10. Picture a phone keypad (1 2 3 / 4 5 6 / 7 8 9, with 0 hanging below): the row a number sits in gives the first hole, the column gives the second. Top is empty, middle white, bottom red. When both of its holes are done, the die goes back in the cup."
  - **Exact.** Faces 1–9 correspond one-to-one to pairs of trits (3 × 3). A 0 is re-thrown on its own face only, which is rejection sampling. So every hole gets an exactly uniform, independent trit.
  - **Cost per grid:** 50 dice, 55.5 d10 reads, 14.6 throws. 10 % of reads are void 0s (5.5 per grid) [run: `kit/randomizer_kit.py`].
  - **Hands-off:** the d10s still in the tray show which hole pairs of the current row are unfinished (colour ↔ pair). The row ship shows the row.
  - **Zero-reroll fallback (still valid):** roll a d6 for every hole in reading order: 1–2 leave it empty, 3–4 put in a white peg, 5–6 a red peg. That is 100 reads per grid with no re-rolls, and the rainbow queue works with it (six d6s per throw).
  - **Both rules give exactly uniform trits**, so everything below is unchanged.
* **Exponent:** the key grids, read in order, are e written in ternary, most significant hole first. e is uniform on [0, 3^(100G)), and the map from grids to e is trivially injective.
* **Entropy:** exactly 100·log₂3 = 158.5 bits per grid. The best attack is the √ split (50 trits against 50) or kangaroo on the interval: **2^79.25 per grid, with no slack**.
* **Grids by tier:** G = ⌈security / 79.25⌉. That is 1 grid for the toy tiers, R512 and T6; 2 for R1024, R2048 and R3072.
  - At 1024 bits, 1 grid (79.25 bits) falls just short of 80.
  - Trimming to exactly the cells needed (e.g. 162 cells for R3072) saves ~19% there, but I kept whole grids.
* **No-paper layout:** the key grids sit apart from the workspace, in a fixed order. The fleet-walk cursor (2 ships) lies on the current key grid's frame. Key pegs stay put for both walks and are cleared only at the end.
* **Walk:** the unchanged B7 walk; an empty hole is 0, white 1, red 2. Every cell is a candidate hit, so the shared walk does about 1 extra multiplication per cell on average.
* **Why this is the default:**
  - It has the most key entropy per multiplication (spike, below).
  - It needs 2 key grids instead of 6 at R3072.
  - Crypto's ECBS review found aliasing entropy loss in three-state fleet keys and recommended pegs-only.
  - Note for BS specifically: the three-state fleet-to-exponent map here is a plain ternary numeral, so it is injective as long as 3^(100G) < q (§4.1). The switch in BS is on efficiency and consistency grounds.

### 4.1 Optional themed variant: three-state fleet key (toy tiers; ECBS §1 reused)

* **Placement:** the ECBS §1.3 full-restart dice procedure (`../PEGBOARD_TERNARY.md` §2.3), read with the randomizer kit (2026-09-30, approved by Zachary; `RANDOMIZER_KIT.md` §4.3). For each ship, largest first (5, 4, 3, 3, 2):
  1. **Roll the d20.** Bottom half (1–10) lies across, top half (11–20) lies down. The **last digit** (0 = 10) is its row if across, its column if down.
  2. **Roll the along-die** for its first hole, re-rolling any number that would hang it off the grid. The along-die is the smallest die that can still put the far end in hole 10: **Carrier d6, Battleship d8, Sub and Cruiser d8, Destroyer d10.**
  3. **If it overlaps an earlier ship, pick up the whole fleet and start again** from the Carrier (acceptance 0.389, unchanged). Ships may touch; they may not overlap.
  4. **Signs:** go along the ship cells in walk order, one d8 per two cells. For the first cell, bottom half (1–4) is white and top half red. For the second cell, odd is white and even red.
  - **Exact:** each ship is uniform on its 2·10·(11 − L) placements, exactly as with the former coin + d10s, and the restart keeps the fleet uniform. The entropy figures below stand.
  - **Cost per fleet:** 30.4 reads instead of 52.2, and 0.51 off-grid re-rolls instead of 3.95 [run: `kit/ecbs13_kit.py`].
  - The former coin + d10 + coin-per-cell procedure gives the same distribution and remains valid.
* **Exponent:** e = Σⱼ dⱼ·3^(M−1−j) over the M = 100G cells in walk order, with dⱼ = 0 (water), 1 (white) or 2 (red).
  - **The fleet boards, read in order, are e written in ternary**, most significant cell first. (Inside registers, hole 0 is least significant. The walk is Horner's rule, so the two orders are opposite. Don't mix them up.)
  - Because digits are < 3, the map from signed fleets to e is **injective** as long as 3^(100G) < q. That holds in every real tier, so ECBS's entropy counts carry over exactly.
* **Entropy per fleet [run, from ECBS]:** 33.6 bits of covered-cell pattern (Shannon) + 17 sign bits = **50.6 bits**.
  - The collision (Rényi-2) entropy is 33.49 + 17 = 50.49 bits [run, `fleet_entropy.py`], so birthday-style attacks don't get a discount.
  - Min-entropy is ≤ 29.9 + 17 bits (the most frequent covered pattern seen arises from 30 labelled placements).
* **Attacks on the key set**, taking the smallest of these:
  - The generic bound 2^(entropy/2) ≈ 2^(25.3G).
  - ECBS's ship-split meet-in-the-middle, about 2^(26.6G). e is a *sum of per-ship terms*, so Eve tabulates 3^(e₁) over half-fleets and matches against A·3^(−e₂).
  - Kangaroo on the interval [0, 3^(100G)], about 2^(79G), which is irrelevant.
* **Fleet count rule (themed variant; shown for comparison, since real tiers use pegs-only):** G = ⌈(NFS security) / 25.3⌉. That gives 4 fleets for 80-bit, 5 for 112, 6 for 128, 8 for 192 and 11 for 256.
* **Toy tiers:** 3^(100G) > q, so e wraps mod q. The fleet's 50.6 bits collapse to log₂ q (27.5 bits for T1).
* **Why a ternary walk (cube) and not binary (square).**
  - Squaring per cell would cost about 1.9× less.
  - But with digits {0, 1, 2} in base 2, the fleet-to-exponent map is not injective. For example, a horizontal destroyer pegged red-red equals the same destroyer one cell to the left pegged white-white (2·2ʷ + 2·2^(w−1) = 2^(w+1) + 2ʷ).
  - I did not measure the resulting entropy loss [not run]. So I chose honesty over speed.
  - A base-4 walk (square twice) is injective but costs the same as cubing.

---

## 5. Received-value check (Wong §5.4)

* **The attack it stops.** If Bob sends an element of a small subgroup, Alice's "shared key" lives in that subgroup and leaks her exponent modulo its order (Lim–Lee).
  - With a safe prime the only small subgroups are {1} and {±1}. So the worst leak is one bit, e mod 2. A non-residue would also leak that bit through the Legendre symbol of K.
  - **Demonstrated [run]:** with the check skipped, B = p − 1 gives K = ±1, and K = 1 exactly when e_A is even (4/4 trials).
* **The fix (B8).** Square first; reject 0 and 1.
  - This clears the cofactor 2, like ECBS's "clear the cofactor 5", at the cost of one multiplication.
  - **Tested [run]:** 0, 1, p − 1 and p + 1 (a non-canonical 1) are all rejected in T1, T2 and T6. A non-residue is accepted, and its square lies in the order-q subgroup.
* **Why not the full check B^q = 1?** It would need a walk over the n-trit public exponent q: about 5,000 multiplications at 3072 bits, roughly twice one person's whole exchange. The square-first variant gives the same protection for honest protocols.
* The exchange must use (B²)^a on both sides. Both sides do, so K = 3^(2ab).

---

## 6. Layouts

**T1 on one workspace grid (n = 18), plus 1 key grid.** Registers use columns 1–9. Column 10 is the 10-hole **control lane** (no-paper rule).

| Rows | Contents |
|---|---|
| 1–2 | X, the accumulator (holes 0–8, then 9–17) |
| 3–4 | Y, the square |
| 5–8 | S, the product strip, holes 0–35 |
| 9–10 | C, the checked base (shared phase). In the public phase these rows are empty, and the strip's nudge overflow (holes 36–37) runs into row 9. |

* Holes used: 18 × 3 + 36 = 90, plus the 10-hole control lane = 100. No spare hole.
* The tidy copy (19 holes) goes in the strip after the walk.
* The toll (white at holes 0 and 2) is kept in your head.

**T2 on two workspace grids (n = 35), plus 1 pegs-only key grid** (themed variant: 2 ocean grids). Stack the workspace grids to get 20 rows of 9 plus a 20-hole column; 10 of those holes are the control lane. A register is 4 rows, with the last hole unused.

| Rows | Contents |
|---|---|
| 1–4 | X |
| 5–8 | Y |
| 9–16 | Strip: 72 holes, exactly 2n + 2 |
| 17–20 | C |

* The fold for T2 is "drop it 35 holes back and 6 holes back". A peg high in the strip therefore folds several times in a chain, which the simulation includes.

**Real tiers:** 5n + (toll length) + 10 holes of workspace, plus separate key grids.
* Three registers X, Y and C, a 2n-hole strip, a toll register on grids, and the control lane.
* Chain grids in reading order to form each register.
* R3072 workspace: 3 × 1938 + 3876 + 969 + 10 = 10,669 holes = 107 grids, plus 2 pegs-only key grids = 109 grids per player. The themed fleet key would need 6 ocean grids (113 grids).
* Cursor ships (8 per player, 2 fleets) lie against the frames of whichever grids they point into.
* No paper anywhere; nothing is stored off the grids.

---

## 7. Tier table [run: `tiers.py`, `pegsonly.py`; `pegsonly_output.json`]

Column notes. This is the default pegs-only key under the no-paper rule; peg supply is not a constraint.
* **NFS:** the NIST SP 800-57 equivalences where tabulated (1024/2048/3072 bits → 80/112/128) [lit-mem]. Otherwise the L_p[1/3, 1.923] formula, shifted to match NIST at 1024 bits [est]. The formula is meaningless below ~128 bits.
* **Rho on q:** Pollard rho, ≈ √(πq/4). Pohlig–Hellman adds nothing, because p − 1 = 2q and g has prime order q.
* **Key √:** 79.25 bits per key grid (the exact √ split / kangaroo bound), capped at log₂(q)/2.
* **Security** is the minimum of the three.
* **Grids** = workspace ⌈(5n + toll + 10)/100⌉ + key grids G.
* **Fleets** = 2 (8 cursor ships). **Game sets** = max(⌈grids/4⌉, ⌈fleets/2⌉).
* **Mults per person** = 500G − 5.5:
  - 2 walks × 2 multiplications per cell after the first non-empty cell (expected position 1.5);
  - plus 1 hit multiplication per cell on average in the shared walk;
  - plus the check squaring.
* **Moves per mult** is measured at that exact n where marked [run], otherwise 1.763·n² [est]. The toy tiers' moves per person come from full simulations [run].

| Tier | Grids per player (workspace + key) | Fleets | **Game sets** | n / p bits | NFS | Rho on q | Key √ | **Security** | Mults per person | Moves per mult | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| T1 skiff | 2 (1 + 1) | 2 | **1** | 18 / 29 | trivial | 2^13.8 | 2^14.0 cap | **≈ 2^14**; BSGS: 0.00 s [run] | 494 | 457 [run] | 2.26·10⁵ [run] | 63 h / 8 days |
| T2 frigate | 3 (2 + 1) | 2 | **1** | 35 / 56 | trivial | 2^27.3 | 2^27.5 cap | **≈ 2^27**; rho: 6.8 s [run] | 494 | 1,659 [run] | 7.75·10⁵ [run] | 9 days / 27 days |
| T6 demo | 7 (6 + 1) | 2 | **2** | 100 / 159 | ~2^31 [est] | 2^78.8 | 2^79.0 | **~2^31** | 494 | 18,367 [run] | 9.27·10⁶ [run] | 107 days / 11 months |
| R512 | 19 (18 + 1) | 2 | **5** | 323 / 512 | ~2^57 [est] | 2^255 | 2^79.2 | **~2^57** | 494 | 1.84·10⁵ [est] | 9.1·10⁷ | 2.9 years / 8.7 years |
| R1024 | 38 (36 + 2) | 2 | **10** | 646 / 1024 | 80 | 2^511 | 2^158.5 | **80** | 994 | 7.45·10⁵ [run] | 7.41·10⁸ | 23 years / 70 years |
| R2048 | 74 (72 + 2) | 2 | **19** | 1292 / 2048 | 112 | 2^1023 | 2^158.5 | **112** | 994 | 2.97·10⁶ [run] | 2.96·10⁹ | 94 years / 281 years |
| **R3072** | **109 (107 + 2)** | **2** | **28** | **1938 / 3072** | **128** | 2^1535 | 2^158.5 | **128** | **994** | **6.62·10⁶ [run]** | **6.59·10⁹** | **209 years / 626 years** |

**Tier decision (2026-09-30):** Zachary dropped R15360 (256-bit) and R7680 (192-bit) because those security levels are overkill for this toy; R3072 (128-bit) is the top tier. Every remaining tier's ships+pegs key fits on one key grid.

**Themed three-state variant (toy tiers only):**

| Tier | Grids (workspace + key) | Fleets (key + cursors) | Game sets | Security | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|
| T1 | 2 (1 + 1) | 3 | 2 | ≈ 2^14 | 1.72·10⁵ [run] | 48 h / 6 days |
| T2 | 4 (2 + 2) | 4 | 2 | ≈ 2^27 | 1.33·10⁶ [run] | 15 days / 46 days |

Reading the table:
* The pegs-only mults formula matches the simulations: T1 494 × 457 = 2.26·10⁵ against 2.26·10⁵ simulated. T2 is 8.2·10⁵ by formula against 7.75·10⁵ simulated [run].
* Both people work in parallel, so wall-clock time equals the per-person time.
* Scaling: with W workspace grids, n ≈ (100W − 10)/5.5 (long toll). Add G = ⌈security/79.25⌉ pegs-only key grids.
* Grid counts include the 10-hole control lane and the separate key grids (no-paper rule).
* **Real-world yardsticks for the weak tiers:**
  - A 512-bit DH prime was precomputed in about a week on 2,000–3,000 cores (~10 core-years). After that, each individual log took a median 70 s (Logjam, Adrian et al., CCS 2015) [lit].
  - The prime-field DLP record is 795 bits, about 3,100 core-years (Boudot et al., 2019/2020) [lit].
  - R1024 is plausibly within nation-state reach, the Logjam authors' estimate for 1024-bit primes [lit].

### 7.1 No-paper resources per player

The per-player grids, fleets and game sets are now in the §7 tables. Since extra pegs can be bought, they come from grids and fleets only.
* **History:** before that assumption, red pegs (42 per kit) set the count from T6 up; e.g. R3072 needed 48 sets. See `bs/nopaper.py` / `nopaper_output.json`, kept for reference.
* **Peg provisioning** still matters physically; see the no-paper section for the measured peaks.
* **Six-state variant** (spike): same workspace, key grids as in the spike table, fleets = key fleets + 2.

---

## 8. Verification results [run]

* **Parameters** (`params_output.txt`, `params_323_output.txt`): every tier's p and q passed Miller–Rabin with 50 rounds and BPSW (sympy). T1 and T2 also passed deterministic Miller–Rabin (first 12 prime bases, valid below 3.3·10²⁴). 3^q ≡ 1 (mod p), p ≡ 11 (mod 12).
  - **Search effort:** R3072 took 4,113 candidates after sieving (27 s); R2048 took 502 and R1024 took 3,010.
* **Arithmetic** (`run_output.txt`, `bigmul_output.txt`): operands are arbitrary register contents, including non-canonical values ≥ p.

  | Tier | Multiply | Multiply + nudge | Worst case (all-red × all-red, nudge 2) | Tidy |
  |---|---|---|---|---|
  | T1 | 300/300 | 300/300 | OK | 313/313, including all 10 values in [p, 3¹⁸) |
  | T2 | 300/300 | 300/300 | OK | 506/506 |
  | T6 | 100/100 | 100/100 | OK | 306/306 |

  - Full-size peg multiplications plus tidy with the real long tolls: R1024, R2048 and R3072 at 3/3 each. That took 1.1 s of Python per R3072 multiplication.
* **Exchanges, pegs-only default key** (`bs/pegsonly.py`, `pegsonly_output.txt`): T1 ×20, T2 ×5 and T6 ×1 with fresh d6 key grids, using the peg recipes. All public values and both K's matched Python's pow. Mean moves per person: T1 225,794; T2 774,802; T6 9,271,512.
* **Exchanges, themed three-state key:** T1 ×20, T2 ×5 and T6 ×2 with fresh dice fleets. In every run:
  - the public values equal pow(3, e, p) and lie in the order-q subgroup;
  - K_A = K_B = pow(3, 2·e_A·e_B mod q, p) = pow(B², e_A, p);
  - K is canonical.
* **Malicious values:** 0, 1, p − 1 and p + 1 were rejected in all tiers. A non-residue was accepted and squared into the subgroup. The unchecked victim leaked e mod 2 in 4/4 trials.
* **Attacks on the toy tiers** (`break_small_output.txt`): T1 fell to baby-step/giant-step in Python in 0.00 s. T2 fell to Pollard rho in C in 6.8 s (2.07·10⁸ iterations). In both, Eve's K equalled the real K.
* **Parity check** (`parity_check_output.txt`): it passes 300/300 on correct multiplications. It catches 63–66% of single wrong pegs injected while laying and 64–69% injected after folding (theory: 2/3).
* **Where the moves go** (R3072 multiplication): 43% are carries; α = moves/n² ≈ 1.76 (T1 1.41, T2 1.35, long tolls 1.76–1.84); the fold is ~1,300 lifts, each laying a 663-peg toll.

---

## 9. Security analysis and caveats (pedantic)

1. **Toy tiers are broken, and I demonstrated it.**
   * T1: q ≈ 2^27.5, broken instantly.
   * T2: q ≈ 2^54.5, broken in 7 s.
   * Their two-peg primes are also SNFS-shaped, which doesn't matter at this size.
   * T6 (159 bits) should fall to NFS in minutes to hours with CADO-NFS [est, not run].
2. **Special form vs NFS.**
   * Sparse primes like 3ⁿ − 3ᵏ − 1 admit small-coefficient polynomials, so the **special** NFS applies: L[1/3, (32/9)^(1/3) ≈ 1.526] instead of L[1/3, (64/9)^(1/3) ≈ 1.923] [lit].
   * Keeping sparse tolls at 128-bit security would need p ≈ 5,000–5,500 bits by the asymptotic formula [est], about 2–3× the work of the long-toll design. That is why the real tiers use long tolls.
   * **Long-toll argument [est]:** in any base x = 3^(n/d), p = x^d − c with c having about d/2 base-x digits of full size ~x. So the best "special" polynomial has coefficients ~p^(1/d), no better than generic base-m selection (~p^(1/(d+1))).
   * **Unreviewed structure:** the top half of p is all red. That is more fixed structure than RFC 7919's 64 bits. I know of no attack that exploits it, but it has not been reviewed. If you are paranoid, use a longer toll, e.g. about 3n/4 trits. The price rises steeply as the toll approaches n trits, because each fold only lowers the spill by n − t holes [est]. A p with no fixed digits at all would need a different reduction recipe (e.g. Barrett), which I have not designed.
3. **The NFS figures are rough.**
   * NIST's table is policy, not measurement [lit-mem]. My interpolated L-values for 159 and 512 bits are [est].
   * NFS precomputation depends only on p. Because every BS user shares each tier's p, one precomputation breaks all exchanges in that tier cheaply afterwards (Logjam's lesson [lit]).
   * If you worry about R1024, use R2048+ or generate your own p with `bsparams.py`, e.g. by using e instead of π.
4. **Short exponents.**
   * *Default pegs-only key:* e is uniform on [0, 3^(100G)): ≈ 2^317 for G = 2, in a group of order 2^3071. That is a standard short-exponent DH setting.
     - The best known attacks are kangaroo on the interval, or the equivalent 50/50 trit split: 2^(79.25G).
     - With a safe prime, short exponents don't leak through Pohlig–Hellman [lit, van Oorschot–Wiener].
     - Margins over the NFS level: +78.5 bits at 1024, +46.5 at 2048, +30.5 at 3072, +45.7 at 7680, +61 at 15360.
   * *Themed three-state variant (toy tiers only):* the key is a sum of per-ship terms. The ship-split meet-in-the-middle is the natural attack (§4.1), and I have no proof that cleverer structured-key attacks don't exist [unverified]. At toy sizes this doesn't matter, because q caps everything.
5. **g = 3 and a base-3 exponent.**
   * A = ∏ (3^(3^(M−1−j)))^(dⱼ): a product of public table entries chosen by the key trits.
   * For pegs-only keys that is just a generic short exponent. For themed fleets, it is the structure the meet-in-the-middle exploits. I know no further weakness [est].
6. **Received values:** checked by square-first (B8). Tested, see §5.
7. **The shared secret is K = 3^(2ab).**
   * Any hashing of K happens outside BS (no-paper rule). K's "entropy" to Eve is bounded by CDH hardness, not by log₂ q.
   * K = 1 would need 2ab ≡ 0 (mod q), which has negligible probability. In T1 it is about 10⁻⁸.
8. **Side channels.**
   * *Public phase:* nearly uniform work (two multiplications per cell), but a watcher can see *where* copies are laid (the nudge).
   * *Shared phase:* hits cost one or two extra multiplications, so timing reveals the key.
   * Work out of sight. A constant-work variant does one "multiply by 1, C or C²" on every cell.
     - For pegs-only keys that is essentially free with a stored C² register (one more register): 1 multiplication per cell against 1 on average.
     - It adds about 33% to the shared phase if every cell does two multiplications instead [est].
9. **Human error.**
   * One wrong peg gives garbage. That breaks correctness, not secrecy.
   * Use the B10 parity check on every multiplication; it catches all forgotten carries.
   * Confirm the result without paper: compare the parity of K ("pair off the whites") and K's lowest 4 trits out loud, abort if they differ, and afterwards treat those 4 trits as public, i.e. don't use them (about 7.3 bits spent) [est].
   * There is no cheap point-on-curve style check for F_p* public values. The received-value check only catches 0 and ±1.
10. **Authentication:** none. Plain DH falls to an active man in the middle (Wong ch. 5); authenticate public values.
11. **Quantum:** Shor breaks every tier.
12. **Unverified items:**
    * the NIST equivalence table (from memory);
    * the long-toll no-SNFS argument;
    * "no better attack on fleet-structured exponents" (themed variant only);
    * hand-time assumptions (1 move/s, no errors);
    * the R512 moves per multiplication (extrapolated from R3072's α);

---

## 10. Cost, and comparison with ECBS

* **R3072 per person (pegs-only default):** 994 multiplications of 1938-trit numbers at about 6.6 M moves each gives **6.59·10⁹ moves**. That is ~209 years non-stop, or ~626 years at 8 h/day. The three-state fleet key would take 1.66·10¹⁰. ECBS (§4) needed 3.9·10⁷ moves per person for ~2^136. **BS is ~170× more work for 128 bits.**
* **Where it goes:**
  - ~80% cubing in the two walks (2 × ~198 cubes × 2 multiplications);
  - ~20% shared-phase hit multiplications (about 1 per cell);
  - within a multiplication, ~43% of moves are carries, and the long-toll fold is about a third of all moves [run: 33% at R3072, 34% at R1024].
* **ECBS §3 estimated ~1.3·10⁹ moves per 3072-bit exponentiation.** BS's figure is ~3.3·10⁹ (pegs-only), for three reasons:
  - the 200-cell ternary walk needs ~400–500 multiplications per walk, versus ~380 for a 256-bit binary exponent;
  - carries;
  - the long-toll fold.
* **Possible savings (none simulated):**
  - Karatsuba, −25 to −45% [est];
  - trimming the key to exactly the needed cells (162 at R3072), −19%;
  - storing C² to avoid double multiplies on red hits, about −2% [est].
* **Verdict:**
  - BS is a correct, honest, fully specified DH that runs on Battleship kit.
  - It is a fine teaching toy at 1–2 boards: textbook DH, a visible toll fold, a visible small-subgroup check, and a live demonstration that the result is broken in seconds.
  - At real sizes it is theoretically hand-doable only on multi-century timescales. For hand-scale security, ECBS is the better design by about two orders of magnitude.

---

## Spike: six-state cells

Physically, a cell has 6 states: ship or no ship, times peg none/white/red. BS and ECBS currently use only 3 of them: water, ship + white, ship + red.

**Scripts:** `bs/sixstate.py` (arithmetic) and `bs/sixstate_sim.py` (peg simulation). Outputs are in `sixstate_output.txt` and `sixstate_sim_output.txt`.

**1. Entropy per grid.**
* Setup: a dice-placed standard fleet, plus an independent uniform peg (none/white/red) in **every** cell. Water holes take pegs; that is what white miss pegs are for. Roll a d6 per cell: 1–2 none, 3–4 white, 5–6 red.
* Pegs and ships are independent, so the entropies add exactly: H = H(covered pattern) + 100·log₂3 = 33.6 + 158.5 = **192.1 bits per grid** [run]. That is 3.8× the current 50.6.
* Don't use log₂(placements × 3¹⁰⁰) = 34.8 + 158.5. Ship labels are invisible, so only the covered pattern counts (ECBS §1.1).
* The ships contribute only 33.6 of the 192.1 bits (33.5 by Rényi-2). **Pegs alone give 158.5 bits per grid.**

**2. Does it remove the ship-sum meet-in-the-middle?**
* No, and nothing can. In a DLP group, Eve can always split a product-structured key into two halves and match (BSGS-style). Generic-group lower bounds say about √ is also the floor [lit-mem, Shoup 1997].
* The current design's real problem was never that the meet-in-the-middle beats √(keys). It gives 2^26.6 against 2^25.3 per fleet. The problem is that there are only 2^50.6 keys.
* Six-state raises the per-grid bound from 2^25.3 to **2^96.1**. The best split (ships plus 40 peg trits against 60 peg trits) costs about 2^97.3 [run].
* Pegs alone give exactly 2^79.2 per grid. Splitting 100 trits into 50 + 50 achieves it, so pegs-only has no slack at all.

**3. Reading a six-state cell in the walk (mixed radix, injective).**
* Recipe per cell: **cube for the peg, then square for the ship.**

  acc ← (acc³ · g^peg)² · g^ship = acc⁶ · g^(2·peg + ship)

* So each cell is one base-6 digit d = 2·peg + ship ∈ {0 … 5}. The map from boards to exponent is injective whenever 6^(100G) < q, which holds for every real tier at the grid counts below.
* **Public phase (g = 3):** both hits stay free.
  1. Nudge the cube's second product 1 or 2 holes for a white or red peg.
  2. Square the result, nudging it 1 hole higher if the cell holds a ship.
* **Shared phase:** after the cube, multiply by C once (white) or twice (red). After the square, multiply by C if the cell holds a ship.
* **Simulated with the peg recipes [run]:** T1 10/10 and T2 3/3 exchanges were correct. The public values equal 3^e and K = 3^(2ab).
* **Cost per grid, per person, both phases:**
  - six-state: 3 multiplications per cell per walk, plus about 1 peg multiplication per cell and 0.17 ship multiplications per cell in the shared walk, for **717** in total;
  - current three-state: 425.5;
  - pegs only: 500.
  - Storing C² saves about 33 for six-state and for pegs only, and 8.5 for three-state.
* **Entropy per multiplication:** 0.268 bits (six-state), **0.317 (pegs only)**, 0.119 (three-state).
* The ship bit costs 100 extra squarings per grid to encode 33.6 bits, i.e. 0.155 bits per multiplication. That is **worse than simply walking more peg cells**.
* Encoding the ship as a second ternary step instead (cube twice) costs 4 multiplications per cell, which is worse still.

**4. Grids needed and hand work per person.** Target = each tier's NFS level. The toy tiers are capped by q, so 1 grid suffices for every encoding. (Grid counts here are *key* grids only. Total per-player grids and game sets under the no-paper rule are in §7.1. The d6-per-cell column needs 2 grids per key grid without paper.)

| Tier (target) | Three-state: grids / moves | Pegs only | Six-state | d6 per cell, no fleet shape (258.5 bits) |
|---|---|---|---|---|
| R1024 (80) | 4 / 1.2·10⁹ | 2 / 7.5·10⁸ (1 grid gives 79.2, just short) | 1 / 5.3·10⁸ | 1 / 5.6·10⁸ |
| R2048 (112) | 5 / 6.2·10⁹ | 2 / 3.0·10⁹ | 2 / 4.3·10⁹ | 1 / 2.2·10⁹ |
| **R3072 (128)** | 6 / 1.66·10¹⁰ | **2 / 6.6·10⁹** | 2 / 9.5·10⁹ | 1 / 5.0·10⁹ |

* Rounding to whole grids matters. Pegs-only R3072 really needs 162 cells for 256 bits, which is about 811 multiplications instead of 1001.

**ECBS-Serious** (key ≥ 256 bits; only ~282 bits are useful, mod ℓ):
* **Six-state in ECBS** uses radix τ²:
  1. Frobenius, then add ±P for the peg.
  2. Frobenius again, then add φ(P) if the cell holds a ship.
* The digit sets at each step are distinct mod τ, so the map is injective in Z[τ]. Mod ℓ this is the same heuristic as before.
* Grids and point additions per walk:

  | Encoding | Grids | Additions per walk | Change |
  |---|---|---|---|
  | three-state | 6 | 102 | — |
  | pegs only | 2 | 133 | +31% (+6% if cut to 162 cells) |
  | six-state | 2 | 167 | +64% |

* Additions are about 92% of ECBS's cost, and in the three-state design water cells cost only a cheap Frobenius. So the ships' 33.6 bits come *for free* there. That is the opposite of BS, where every cell costs a full cube.

**Recommendation** (adopted 30 Sep 2026: pegs-only is now the BS default, §4.0).
* **BS:** drop the fleet from the exponent and **use pegs only**: a d6 per cell gives a uniform trit, and the walk stays the plain ternary walk.
  - It is the most efficient option per multiplication, and the recipe doesn't change.
  - R3072 drops from 6 grids and 1.66·10¹⁰ moves to 2 grids (or 162 cells) and about 6.6·10⁹ moves per person, 2.5× less.
  - If the ships must stay for the theme, six-state is a fair compromise: 1.75× cheaper than now, 1.4× dearer than pegs only.
* **ECBS:** keep three-state if moves matter (it's the cheapest per walk). Switch to pegs only if the board count matters (6 → 2 grids for +6% to +31% work).
* **Honesty note:** in every efficient option the key is really a random ternary string, and the fleet is at most a 33.6-bit garnish per grid. Entropies assume dice or d6 placement, never human choice. The rest of the caveats in §9 (structured short exponents, √ bounds as assumptions, side channels) carry over unchanged. In the shared phase, peg hits on two-thirds of the cells make timing leaks worse unless the constant-work variant is used.
