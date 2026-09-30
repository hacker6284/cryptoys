# BS: Battleship Diffie–Hellman

Finite-field Diffie–Hellman (powers of 3 modulo a prime p), worked by hand on Battleship pegboards. The private exponent is one dice-built **ships+pegs key grid**: a free fleet (any number of ships, built by "grow until it bumps") plus a 3-state peg in every one of the 100 holes, read as "ships, then pegs" (§4). BS is the prime-field sister of **ECBS** (`../ecbs/SPEC.md`) and reuses its conventions:
* holes empty/white/red = 0/1/2;
* the colour wheel;
* fold recipes;
* the key walk (a ternary walk, one cube per key cell).

The small tiers are deliberately weak. The goal is a working, honest DH that scales up by adding boards.

**Code and evidence** live in `proofs/key_exchange/bs/` (index in its `README.md`). Each directory is a note, not a theorem: scripts with their recorded outputs beside them.
* `reference/`: the peg recipes (`bspegs.py`, colours only), the integer reference (`bsref.py`), the prime search (`bsparams.py`), arithmetic and malicious-value tests (`run_bs.py`), full-size multiplications (`bigmul.py`), the tier table (`tiers.py`), the toy-tier attacks (`break_small.py`, `break_t2.c`), the parity checksum (`parity_check.py`) and peg provisioning (`peg_supply.py`).
* `exchange/`: full exchanges with ships+pegs keys through the peg recipes, every tier.
* `ships-pegs/`: the key (§4): a literal implementation of BUILD and READ (`keygrid.py`), the exact entropy DP, brute force, injectivity and build checks.
* `randomizer-kit/`: the dice rules.
* `key-selection/`: why this key and not another (analysis only).

**Marks.** A measured figure is followed by the place that measures it, e.g. (`exchange/`); paths are under `proofs/key_exchange/bs/`. They are measurements, not proofs. Otherwise:
* **[lit]** = from a source that was checked.
* **[lit-mem]** = standard literature cited from memory, not re-fetched.
* **[est]** = an estimate.
* **[unverified]** = a plausible claim that was not checked.

**Dice.** The key's dice and what each roll decides are in §4.2 (checked in `randomizer-kit/` and `ships-pegs/`).
* **Optional everywhere:** the **rainbow queue**: throw a cup of same-shape dice, one per rainbow colour (red, orange, yellow, green, blue, purple). Each roll the recipe asks for takes the next colour still in the tray, and that die goes back in the cup once read. When none are left, throw the cup again. It is exact because the colour order is fixed before the throw and no die is read twice.
* Dice remain a source, not storage. Unused dice lying in the tray are allowed physical state; a die is never moved until it is used.

---

## No-paper rule (hard constraint)

**Nothing in BS may rely on paper.** Every register and every piece of state must live in physical grids, pegs and ships. A **kit** is half a classic Hasbro set: one player's ocean (ship) grid, target grid, 5-ship fleet, 42 red pegs and 84 white pegs. **1 game set = 2 kits** (4 grids, 2 fleets, 84 red and 168 white pegs [lit: Hasbro contents list]).

**Audit.** These are the places the earlier text relied on paper or off-board state, and what they became:

| Earlier text | Now |
|---|---|
| §1 A1: the fleet could be "marker pieces or a sketch" | The key always sits on its own grid (an ocean grid holding the key's ships and pegs) and is counted per player. |
| §6: idle registers as paper "photographs" | Removed. Every register lives on grids and is counted in the holes. |
| §6: the long toll "could be a printed card" | Removed. The toll is a register on grids (it was already counted). |
| Implicit: loop counters and positions in your head (which key cell you're on, which hole of B, A and the strip you're laying at) | **Cursor ships** plus a **10-hole control lane** (below). |
| Implicit: "pair off the whites" parity and the sub-step of the cell in your head | Pegs in the control lane. |
| §3 B9 and §9: "hash K" and "compare a short hash aloud" | BS now ends with K on the grid; hashing is outside BS. Key confirmation is done physically (§9). |
| Public values as "W/R/. strings" | The other player copies your published register peg by peg into their Y register (Y is free at that point; own A stays in X until copied). The trits may be read aloud, but they are never stored anywhere except pegs. |

Unchanged: dice are a randomness source, not storage. The two-peg toy tolls are part of the recipe (like "drop it n back and n−k back"), not state.

**Control state, made physical.**
* **Control lane:** 10 holes per player.
  - One peg in holes 1–6 marks the cell sub-step: square, cube product, hit-multiply 1, hit-multiply 2 (holes 5–6 spare).
  - Hole 7 is the parity bit (white = odd).
  - Hole 8 is the phase: empty = public walk, white = check, red = shared walk.
  - Hole 9 is the "accumulator started" flag.
  - Hole 10 is the key's lane peg, used while building and while reading (§4.2, §4.3).
  - Fold progress needs no marker ("always the highest peg" is visible).
* **Cursors:** 4 cursors (key-walk cell, B hole, A hole, strip hole), each a pair of ships laid flat against a grid's frame. One ship points at the row, the other at the column; the ship type names the cursor.
  - That is 8 ships per player (pieces are not counted, see below).
  - **Finger rule:** you may keep your place with a finger while laying, but **before you take your hands off, park the cursor ships**, so the table is always a complete record.
  - Parking costs only O(n) moves per multiplication, which is negligible. Moving the cursors on *every* peg instead would add about 2n² moves per multiplication, roughly doubling all hand times.
* **Only grids count.** Pegs and ship pieces (the cursor ships and the key's ships) are unlimited, because extra ones can be bought, and they are not counted. **Game sets per player** = ⌈grids/4⌉.
  - Peg provisioning, measured peak pegs in use per player (registers only): T1 46 red / 47 white; T2 79 / 80; T6 236 / 217 (`reference/peg_supply.py`). For big tiers it is ~0.36 per workspace hole of each colour, plus the key's ~33 ± 5 of each colour per key grid (≈ 67 pegs per grid, §4.7).
  - Ship provisioning: the 8 cursor ships, plus the key's ≈ 31.6 ships per grid on average (D 18.8, S 5.5, C 5.6, B 1.5, A 0.23; at most 50 D, 33 S or C, 25 B, 20 A).
* **The key** is one **key grid**: an ocean grid holding a dice-built free fleet and a dice-rolled peg in every hole (§4). It is its own grid and is counted.
* **T1:** the arithmetic still fits on one grid, exactly (90 register holes + the 10-hole control lane). With the key grid, a T1 player needs **2 grids = 1 game set**.

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
* **Key: one ships+pegs key grid** (§4): dice put a free fleet and a 3-state peg in every hole (BUILD, §4.2), and the grid is read as a ternary string, ships then pegs (READ, §4.3). **306.33 bits Shannon / 283.28 bits min-entropy per grid**, with zero aliasing, so **one key grid covers every tier up to R3072** even when sized by min-entropy.
* **Exponentiation:** a left-to-right cube-and-multiply walk over that string (B7). Public-phase hits are free nudges, because multiplying by g = 3 is a shift (B6).
* **Received-value check** (Wong §5.4): square the received number first and reject 0 and 1 (B8). The shared secret is K = 3^(2ab).

**Tiers (details in §7).** One ships+pegs key grid in every tier, no paper. Security is the minimum of NFS, rho on q, and the key's √ bound. Moves are per person; hand time assumes 1 move per second.

| Tier | Grids per player (workspace + key) | Game sets | p | Security | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|
| **T1 skiff** | **2 (1 + 1)** | **1** | 3¹⁸ − 3² − 1 (29 bits) | ≈ 2^14; **broken in 0.00 s** | 4.87·10⁵ | 135 h / 17 days |
| **T2 frigate** | **3 (2 + 1)** | **1** | 3³⁵ − 3²⁹ − 1 (56 bits) | ≈ 2^27; **broken in 3.3 s** | 1.66·10⁶ | 19 days / 58 days |
| T6 demo | 7 (6 + 1) | 2 | 159 bits | ~2^31 [est] | 1.97·10⁷ | 228 days / 22 months |
| R1024 | 37 (36 + 1) | 10 | 1024 bits | 80 | 7.74·10⁸ | 25 years / 74 years |
| R2048 | 73 (72 + 1) | 19 | 2048 bits | 112 | 3.07·10⁹ | 97 years / 292 years |
| **R3072 serious** | **108 (107 + 1)** | **27** | 3072 bits | **128** | 6.84·10⁹ | **217 years / 650 years** |

Only grids count (No-paper rule). In T1, T2 and T6 the key wraps mod q (injectivity fails, §4.6); those tiers are capped by q.

**Verified** (details and pointers in §8)
* p and q are prime (Miller–Rabin with 50 rounds, plus BPSW; also deterministic Miller–Rabin for T1 and T2), and 3^q ≡ 1 (mod p), for T1, T2, T6, R512, R1024, R2048 and R3072.
* The peg recipes compute exactly what Python computes:
  - multiply: 300/300 (T1, T2) and 100/100 (T6);
  - multiply with nudge: 300/300 and 100/100;
  - tidy: every edge value;
  - full-size multiplications at 1024, 2048 and 3072 bits: 3/3 each.
* **End-to-end exchanges with ships+pegs keys through the peg recipes, in every tier:** T1 ×20, T2 ×5, T6 ×2, R512 ×1, R1024 ×1, R2048 ×1, R3072 ×1, each party's key built with the §4.2 dice and read by §4.3. In every one the public values equal pow(3, e, p), both parties get the same K, and K = pow(3, 2·e_A·e_B, p) (`exchange/`).
* **Ships+pegs key:** exhaustive injectivity on 7 small grids, 20,000 built 10×10 grids round-trip, 3,000 two-page keys decode, and the build matches the exact model (§4.5, §4.2; `ships-pegs/`).
* **Received-value check:**
  - It rejects 0, 1, p−1 and p+1.
  - A non-residue is accepted but squared into the subgroup.
  - A victim who skips the check leaks e mod 2 to a p−1 attacker (4/4 trials).

**Caveats, in one breath**
* This is ~180× more hand work than ECBS for similar security. Finite-field DH is simply worse by hand than ECDH.
* The long-toll prime family fixes the top half of the digits. I know no attack on that, but nobody has reviewed it [est].
* The key is a short, structured exponent: e ∈ [3^M, 2·3^M) with M ≤ 233 (one key grid). Security rests on the standard short-exponent assumption with a safe prime, and on the √ heuristic for the ship part, which is a sum of per-ship terms (§4.9, §9).
* NFS precomputation is per-prime and amortises over all users of that prime (Logjam).
* Hand work leaks the key to watchers, one wrong peg ruins the result, and there is no authentication.

---

## 1. Explicit assumptions

* **A1. "One board" = one 10×10 peg grid of 100 holes**, holding every working register and all scratch space.
  - The key is *not* in those holes. It sits on its own key grid (an ocean grid with the key's ships and pegs). Under the no-paper rule that key grid is counted, so T1 is 2 grids per player.
* **A2. The key grid is its own ocean grid** (ships plug into its holes, §4.1). Workspace grids carry no key. Cursor ships (8 per player) lie against the frames (no-paper rule).
* **A3. A "move"** is one peg placed, one peg lifted, or one hole's peg swapped for another colour.
  - One carry is one more move.
  - Moving a register costs two moves per peg: lift and place.
  - Hand time assumes 1 move per second with no errors. Real humans are slower; multiply by 2–3 [est].
* **A4. Keys come from fair dice by the BUILD (§4.2), never from humans.** Every entropy figure assumes fair dice and the rule followed exactly. None of them applies to human-chosen fleets.
* **A5. Security is classical.** Shor's algorithm breaks every tier; that is out of scope.
* **A6. Standard hardness assumptions.** CDH and DLP in the order-q subgroup of F_p* are as hard as the best known algorithms (NFS, rho). For the long-toll primes, I additionally assume the fixed top half gives NFS no special advantage [est, §9].
* **A7. Work is done out of sight.** The pattern of work reveals the key (§9).
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
  - Safe primes of this shape for n = 16…44 exist only at **n = 18 (k = 2), 30 (k = 4, 12), 31 (k = 1), 35 (k = 29)** (`reference/bsparams.py`). There are none at n = 20 or 40, which is why the rows don't line up with 10-hole rows (§6).
* **Long tolls (real tiers).**
  - c = (first ⌈n/2⌉ ternary digits of π) + j, where j is the smallest offset that makes p a safe prime (`reference/bsparams.py`).
  - π = 10.0102110122…₃, so every long toll begins **W . . W . R W W . W R R R R …**
  - This is "nothing up my sleeve", like RFC 7919, whose primes fix the top and bottom 64 bits and take the middle from e [lit].
  - Anyone can regenerate every parameter with `bsparams.py`. That matters because trapdoored SNFS primes are a real thing (Fried–Gaudry–Heninger–Thomé, EUROCRYPT 2017 [lit]).

### 2.2 Why a safe prime with g = 3
* **The subgroups** of F_p* for p = 2q + 1 have orders 1, 2, q and 2q. The only small subgroups are {1} and {±1}.
* **3 generates the order-q subgroup.** p ≡ 3 (mod 4) (q is odd) and p ≡ 2 (mod 3), so p ≡ 11 (mod 12), and then by quadratic reciprocity (3/p) = +1. So 3 is a quadratic residue, and since 3 ≠ 1 its order is exactly q. 3^q ≡ 1 holds for every tier (`reference/params_output.txt`).
* **Multiplying by g is a one-hole shift.** That is why public-phase hits cost nothing (the nudge, B6).
* **Short exponents are fine with a safe prime.** Exponents are short: e < 2·3^M with M ≤ 233 for the one key grid (§4.4), far below q in the real tiers. van Oorschot–Wiener (EUROCRYPT '96) show that short exponents are dangerous when p − 1 has medium-sized factors, and that safe primes "preclude this particular attack" because a partial Pohlig–Hellman decomposition yields only one bit [lit]. Here even that bit is gone, because g is in the order-q subgroup.

### 2.3 Concrete parameters

| Tier | n (trits) | p | p bits | Toll | Checks (`reference/params*_output.txt`) |
|---|---|---|---|---|---|
| T1 | 18 | 3¹⁸ − 3² − 1 = 387,420,479; q = 193,710,239 | 29 | white at holes 0, 2 | p and q prime (deterministic MR + BPSW); 3^q = 1 |
| T2 | 35 | 3³⁵ − 3²⁹ − 1 = 49,962,914,721,634,823; q = 24,981,457,360,817,411 | 56 | white at holes 0, 29 | same |
| T6 demo | 100 | 3¹⁰⁰ − (π₅₀ + 4383) | 159 | 50 trits, 40 pegs | MR-50 + BPSW; 3^q = 1 |
| R512 | 323 | 3³²³ − (π₁₆₂ + 108769) | 512 | 162 trits | same |
| R1024 | 646 | 3⁶⁴⁶ − (π₃₂₃ + 1052835) | 1024 | 323 trits, 230 pegs | same |
| R2048 | 1292 | 3¹²⁹² − (π₆₄₆ + 176296) | 2048 | 646 trits, 448 pegs | same |
| **R3072** | **1938** | **3¹⁹³⁸ − (π₉₆₉ + 1453486)** | **3072** | 969 trits, 663 pegs | same |

* π_t is the integer whose base-3 digits are the first t ternary digits of π.
* The full decimal values of p, q and c are in `reference/params.json` and `reference/params_323.json`.
* In every big tier, q is a *probable* prime: Miller–Rabin with 50 rounds plus BPSW, with no ECPP certificate. p follows from q by Pocklington in principle (not checked).

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
  - In the *public phase* on a hit cell (white or red), lay every copy of the second product one hole higher (white hit) or two holes higher (red hit). That multiplies by 3 or 9 = g or g² for free.
* **B7. Key walk (the exponentiation).** The key is a string of cells (§4.3: the ship pass, then the peg pass). A **hit** is a white or red cell; a plain cell is 0.
  1. Walk the cells in that order. The walk cursor (2 ships) sits on the key grid's frame.
  2. Before the first hit, do nothing (the accumulator is 1).
  3. At the first hit, start the accumulator X:
     - *Public phase:* a lone white peg at hole 1 (white hit) or hole 2 (red hit).
     - *Shared phase:* a copy of the base C (white), or C × C (red).
     - The key's start marker (§4.3) is a white hit before the first cell, so X always starts there, and every cell after it cubes.
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
  1. Alice walks her key grid with g = 3 and publishes A (tidy, n trits read as W/R/. from hole 0). Bob does the same and publishes B.
  2. Each checks and squares the other's number (B8).
  3. Each walks their own key grid over the square (B7, shared phase): K = (B²)^a = (A²)^b = 3^(2ab).
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

## 4. The key: ships + pegs

One key grid holds a dice-built free fleet **and** a 3-state peg (empty/white/red) in every one of its 100 holes. Two rules:
* **BUILD** ("one hole at a time: ship, then peg", §4.2) fills the grid with dice.
* **READ** ("ships, then pegs", §4.3) turns the grid into an exponent.

### 4.1 Grid, pieces and physical assumption

* **Grid and order.** One 10×10 grid (the **key grid**, any ocean grid). Reading order is row A to J, holes 1 to 10. A ship's **first hole** is the one you reach first in reading order: its left end if it lies across, its top end if it lies down. Its **last hole** is the other end; the holes in between are **middle** holes.
* **Pieces.**
  - Every kind has its own model (D2, S3, C3, B4, A5), so Sub ≠ Cruiser.
  - A piece plugs into exactly its L holes and visibly lies across or down.
  - It has a **visible bow** (which end points where).
  - Pieces are unlimited, like pegs, and are not counted (only grids count, No-paper rule). Usage is in the No-paper rule.
* **Physical assumption** (from the Hasbro rules: 2002, 2011 and Retro editions [lit]). Ships sit in the ocean-grid holes and **cover** the grid holes under them, and each ship cell has its own peg hole. So a covered cell's peg goes in the ship's own hole and a sea cell's peg goes in the grid hole: **every one of the 100 cells takes exactly one 3-state peg**, on top of the layout.
  - **[Assumption to check on your set]** White pegs fit ship holes as well as red ones.

### 4.2 BUILD: "one hole at a time: ship, then peg"

> **Lay the walk cursor (2 ships on the frame) at A1.** At the cursor hole:
> 0. **At the start of each row, throw the row cup:** the five d10s (red, orange, yellow, green, blue). Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each (red holes 1–2, …, blue 9–10).
> 1. **If no ship covers this hole, decide it with "grow until it bumps"** (below).
> 2. **Peg it from its row-cup die.** Picture the number on a phone keypad (1 2 3 / 4 5 6 / 7 8 9). **The row the number sits in gives the peg for the pair's first hole; its column gives the peg for the pair's second hole.** Top row or left column: no peg. Middle row or middle column: white. Bottom row or right column: red. (So 6, middle row and right column, is white then red.) Put the peg in the ship's hole if a ship covers this hole, otherwise in the grid hole. The die goes back in the cup after its second hole.
>    - **Zero-reroll fallback:** roll a d6 for the peg instead, 1–2 no peg, 3–4 white, 5–6 red.
> 3. **Move the cursor to the next hole** (reading order). After J10, park it off the grid.
>
> **Letting go.** Finish the hole before you let go (the rule is in step 1 below); the cursor is then parked at the hole you are about to start. **The one exception is the gap between steps 1 and 2:** you may let go there if you first stand a **white peg in control-lane hole 10** ("ship decision made"). Lift it when you move the cursor.

**Step 1: grow until it bumps** (at the cursor hole, when no ship covers it)

> **Finish the hole, including all growth rolls and the Sub/Cruiser roll, before you let go.** A ship waiting for a growth roll looks exactly like a finished one of its current length, so a build resumed from the board would stop it short.
>
> A heading "has room for a Destroyer" when the next hole that way is on the grid and not under a ship.
> - **If neither heading has room:** it is **sea**, with no roll.
> - **If both have room, roll the hole die (d12): 1–4 sea, 5–8 across, 9–12 down.**
> - **If only one has room, roll the hole die: 1–6 sea, 7–12 a ship in the open heading.**
> - **Sea:** leave the hole as it is (sea leaves no mark; the cursor is the record).
> - **A ship:**
>   1. **Bow:** read the same hole die: **odd, bow at this hole; even, bow at the far end.** Turn each piece to match as you lay or swap it.
>   2. **Lay a Destroyer** from this hole in that heading.
>   3. **Grow it with the d6:** while there is room for one more hole, roll. From 2 holes it **grows on 4–6**. From 3 holes, and from 4, it grows **only on a 6**.
>      - **Growing means swapping the physical piece for the next longer ship, lying over the same holes plus the next one in its heading:** Destroyer → a 3-holer (Sub or Cruiser) → Battleship → Carrier.
>      - While a ship grows, the piece on the board *is* its current length. Nothing on the board says whether it is still growing; that is why you finish the hole first.
>   4. **It stops growing** when a roll fails, or with no roll at all when it **bumps**: the next hole is off the grid or under a ship.
>   5. **A 3-holer:** roll the d6: **1–3 Sub, 4–6 Cruiser.** Swap in that piece if the one lying there is the other.
>
> **Ships may touch**, side by side or end to end, as in Hasbro's rules. They never overlap: a ship only ever grows into open holes.

* **Why the d12 is exact.** The former wording rolled sea on 1–2, then a heading on 1–3 / 4–6, and "rolled again for this hole" if not even a Destroyer fitted. That is rejection sampling. Sea has weight 1/3 and each heading 1/3 if it has room. After renormalising:
  - both headings open: 1/3, 1/3, 1/3 (the d12 thirds);
  - one heading open: 1/2, 1/2 (the halves);
  - none open: sea.
  - The bow is an independent fair bit. On a d12, odd/even splits every third (2 + 2) and every half (3 + 3) evenly, so it is independent of the hole decision.
  - Checked exactly, with Fractions: all 25 room states, and whole builds on 2×3, 3×3, 2×5 and 3×4 (64,557 layouts) are identical to the former rule (`randomizer-kit/`, part B).
  - The former wording (d6 sea roll, heading roll, roll again, d6 bow) gives the same distribution and remains valid.
* **All-d6, zero-reroll fallback** (equally exact):
  - The hole die is a d6: **1–2 sea, 3–4 across, 5–6 down**. If only one heading has room: **1–3 sea, 4–6 that heading**.
  - Roll a **separate d6 for the bow**: 1–3 bow at this hole.
  - Do **not** take the bow from a d6's odd/even. In the halves 1–3 / 4–6 it splits 2 : 1.
* **Why the row cup is exact.** Faces 1–9 correspond one-to-one to pairs of trits (3 × 3). A 0 is re-thrown on its own face only, which is rejection sampling. So every hole gets an exactly uniform, independent trit. The d6 fallback also gives exactly uniform trits.
* **Hands-off:** the row-cup d10s still in the tray show which hole pairs of the current row are unfinished (colour ↔ pair).
* **The cursor is the record.** With the finish-the-hole rule, a build is only ever left at a hole boundary or in the step 1 → 2 gap. Every hole before the cursor is finished (ship decided, growth and Sub/Cruiser rolls included, and peg rolled). The cursor hole's ship decision is finished if lane hole 10 holds a white peg and not started otherwise. Every hole after it has no peg. So "no peg" never has to mean "sea decided", and a white peg always means a white key digit.
  - A ship laid at the cursor covers only the cursor hole and holes after it, none of which has a peg yet. Pegs behind the cursor are never in a ship's way, because ships grow only right or down.
  - Build simulated with random let-go and resume at every allowed point, resuming from the board alone: the joint layout × peg distribution matches the exact model, chi-square 1,327.7 on 1,376 df (2×2, 400k builds) and 101,368 on 101,330 df (2×3, 300k builds) (`ships-pegs/combined.py`).
  - The literal dice of this section (`ships-pegs/keygrid.py`), d12 + row cup and the all-d6 fallback: layout and peg chi-squares against the exact model on 2×2, 2×3, 3×2, 1×5 and 5×1 all within |z| < 2 (`ships-pegs/keygrid_check.py`).
* So a resumed build needs only what is on the table: the pieces, the pegs, the cursor, the lane peg and the row-cup dice in the tray. The layout dice use only thirds, halves, odd/even on the d12, and "a six".

### 4.3 READ: "ships, then pegs"

> **Walk the grid twice in a row without stopping the arithmetic.**
> 1. **Ship pass:** the fleet walk below, including the start "as if a white hit before A1". Ignore the pegs.
> 2. **Peg pass:** go back to A1 and walk it one cell per hole in reading order: no peg = plain, white = white, red = red. Ignore the ships. A peg in a ship's hole counts just like one in a grid hole.
>
> **Several grids:** read them as pages, each page ships then pegs. There is one start marker for the whole key.
>
> *Mnemonic: "first read the fleet, then read the shots."*

**The ship pass: the fleet walk**

> **Walk the key grid in reading order, one cell per hole, but start as if there had been a white hit just before hole A1.** At each hole:
> - **No ship:** a **plain** cell.
> - **A ship's first hole:** **white** if the ship lies **across**, **red** if it lies **down**.
> - **A ship's middle hole:** a **plain** cell.
> - **A ship's last hole:** **white** if the ship **points back** (its bow is at its first hole), **red** if it **points on** (the bow is right here).
>   Then, **if it is a Sub or a Cruiser, walk one more cell for this hole: plain for the Sub (it dives), white for the Cruiser.**
>
> *Mnemonic: "the start says which way it lies, the end says which way it points; Subs dive, Cruisers fly a flag."*

* "A cell" is exactly B7: cube the accumulator.
  - In the public phase, a white or red cell is the free nudge (1 or 2 holes).
  - In the shared phase, a white cell means multiply by C once, a red cell twice.
* "Start as if there had been a white hit": the public phase starts X as a lone white at hole 1; the shared phase starts X = C. After that, every hole cubes, including leading sea holes. This start marker is what makes keys of different lengths impossible to confuse.
* **Bookkeeping (no paper).** The walk cursor (2 ships on the frame) marks the hole. Control-lane hole 10 marks where you are within it: **empty** = ship pass; **red** = ship pass, Sub/Cruiser extra cell still to do; **white** = peg pass. At the end of a page, lift the lane peg, then put the cursor on the next grid's frame at A1.
* The key pegs and ships stay put for both walks and are cleared only at the end.

### 4.4 Exponent

* e = 3^M + Σ tⱼ·3^(M−1−j) over the string (ship cells ‖ peg cells [‖ next page …]), with tⱼ ∈ {0, 1, 2} = plain/white/red and M = Σ over pages (100 + #3-holers + 100) ≤ 233 per page.
* Equivalently, for one page, e = 3^100·E_fleet + P with 0 ≤ P < 3^100 (P is the peg digits), where E_fleet is the ship pass's own exponent (the fleet walk read alone, start marker included).
* The key grid, read this way, *is* e written in ternary, most significant cell first. (Inside registers, hole 0 is least significant. The walk is Horner's rule, so the two orders are opposite. Don't mix them up.)

### 4.5 No aliasing

* **The ship pass decodes.** Scan the holes in reading order, remembering which holes are already known to be covered:
  - At a hole not known to be covered: plain means sea; white/red means a ship starts here across/down, so its next hole is covered.
  - At a covered hole, plain means the ship goes on (mark its next hole). White or red ends it, giving the bow. The number of holes so far gives the kind: 2 D, 4 B, 5 A; for 3, read the extra cell to tell S from C.
  - So the ship-pass cell string determines the layout.
* **The page decodes.**
  - (i) The start marker puts e in [3^M, 2·3^M), so e determines M and the digit string.
  - (ii) Within a page the ship pass is self-delimiting: the decoder knows after hole J10 exactly how many cells it has used (100 plus one per 3-holer), and the next 100 cells are the peg pass, one per hole in reading order. So e determines each page's layout and pegs. **Aliasing loss = 0 bits.**
* **Checks:**
  - Every layout × every peg pattern on 1×2, 2×1, 2×2, 1×5, 2×3, 3×2 and 1×7 gives a distinct e, and decode is the identity (785,133 keys on 1×7) (`ships-pegs/combined.py`).
  - 20,000 built 10×10 grids round-trip (`ships-pegs/combined.py`, and again with the literal dice in `keygrid_check.py`); 3,000 two-page keys decode to both grids (`combined_multi.py`).
  - The ship pass alone: every layout on 1×2, 2×2, 1×5, 2×3, 3×3, 2×5, 3×4 and 4×4 (3,996,513 layouts on 4×4) gives a distinct exponent, and decode(encode) is the identity (`ships-pegs/read_rule.py`).

### 4.6 BS injectivity mod q

* Distinct keys give distinct exponents (§4.5). They are guaranteed to give distinct **group elements** when **2·3^M < q**, with M ≤ 233G + (marker).
* That allows G ≤ 1 at R512, ≤ 2 at R1024, ≤ 5 at R2048, ≤ 8 at R3072 (`reference/tiers.py`, `injective_mod_q_max_grids`). The one grid used holds in every real tier.
* **T1, T2 and T6: fails.** Every page has at least 200 cells, and 3^200 already exceeds q in those tiers (q ≈ 2^27.5, 2^54.5, 2^157.5). So e wraps mod q and injectivity mod q is not guaranteed. Those tiers are capped by log₂ q anyway (§7): the key's entropy mod q is at most log₂ q (27.5 bits for T1).

### 4.7 Entropy and cost per grid

* **Entropy:** the pegs are rolled independently of the layout, so every measure adds exactly; pegs add 100·log₂3 = 158.50 bits.

  | Part | Shannon H | Collision H₂ | Min-entropy H∞ |
  |---|---|---|---|
  | Layout ("grow until it bumps") | 147.83 | 145.49 | 124.78 |
  | Pegs | 158.50 | 158.50 | 158.50 |
  | **Grid total** | **306.33** | **303.99** | **283.28** |

  - Layout figures: exact DP over 5^10 profile states, cross-checked against brute force on small grids and by Monte Carlo (`ships-pegs/build_dp.py`, `brute_build.py`, `viterbi.py`). The layout's min-entropy is lower because heavy grids exist: the most likely layout (p = 2^−124.78) is columns of down-ships separated by sea.
  - Totals: `ships-pegs/combined.py`.
* **Walk:** 211.10 cells on average (largest seen 222, at most 233); 203.35 hit units (shared phase: white = 1 multiplication, red = 2). **1,048.8 multiplications per grid per person** = 4·211.10 (two walks × a 2-multiplication cube per cell) + 203.35 (shared hits) + 1 (check) = 3.42 per Shannon bit and 3.70 per min-entropy bit (`ships-pegs/combined.py`, 20,000 built grids; the literal dice give 211.08 cells and 203.26 hit units, `keygrid_check.py`).
* **Build:** 156 dice reads (100.5 layout + 55.5 peg d10s, 5.5 of them void 0s), about 31 throws, ≈ 265 moves (≈ 88 ship moves + ≈ 66.7 pegs + 110 cursor moves) (`ships-pegs/combined.py`, `keygrid_check.py`). Using the lane marker at every hole adds up to 200 more. Pieces: ≈ 31.6 ships and ≈ 67 pegs per grid. The build is negligible next to the walk.

### 4.8 Grids by tier

* **√ bound per grid:** 153.2 bits (Shannon) or 141.6 bits (min-entropy).
* **One key grid covers R1024–R3072 even when sized by min-entropy** (283.3 ≥ 256; `ships-pegs/combined.py`). R512 (target ~57) and the toy tiers need no more than one grid either; the toy tiers are capped by q (§4.6).
* So every tier uses **exactly one key grid** (§7).

### 4.9 Attacks on the key

* I use "a key of entropy H costs about 2^(H/2)", the √ heuristic, for both Shannon and min-entropy.
* The ship part is a sum of per-ship terms, so a ship-split meet-in-the-middle is the natural structured attack, and the √ bound is heuristic. I know no attack better than √ [heuristic].
* The peg part is 100 independent uniform trits (P in §4.4).

### 4.10 Why a ternary walk (cube) and not binary (square)

* Squaring per cell would cost about 1.9× less.
* But with digits {0, 1, 2} in base 2, the cells-to-exponent map is not injective. For example, two red cells in a row equal two white cells one place higher (2·2ʷ + 2·2^(w−1) = 2^(w+1) + 2ʷ).
* The resulting entropy loss was not measured. So I chose honesty over speed.
* A base-4 walk (square twice) is injective but costs the same as cubing.

---

## 5. Received-value check (Wong §5.4)

* **The attack it stops.** If Bob sends an element of a small subgroup, Alice's "shared key" lives in that subgroup and leaks her exponent modulo its order (Lim–Lee).
  - With a safe prime the only small subgroups are {1} and {±1}. So the worst leak is one bit, e mod 2. A non-residue would also leak that bit through the Legendre symbol of K.
  - **Demonstrated** (`reference/run_bs.py`): with the check skipped, B = p − 1 gives K = ±1, and K = 1 exactly when e_A is even (4/4 trials).
* **The fix (B8).** Square first; reject 0 and 1.
  - This clears the cofactor 2, like ECBS's "clear the cofactor 5", at the cost of one multiplication.
  - **Tested** (`reference/run_bs.py`): 0, 1, p − 1 and p + 1 (a non-canonical 1) are all rejected in T1, T2 and T6. A non-residue is accepted, and its square lies in the order-q subgroup.
* **Why not the full check B^q = 1?** It would need a walk over the n-trit public exponent q: about 5,000 multiplications at 3072 bits, about 5× one person's whole exchange (≈ 1,049 multiplications, §4.7). The square-first variant gives the same protection for honest protocols.
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

**T2 on two workspace grids (n = 35), plus 1 key grid.** Stack the workspace grids to get 20 rows of 9 plus a 20-hole column; 10 of those holes are the control lane. A register is 4 rows, with the last hole unused.

| Rows | Contents |
|---|---|
| 1–4 | X |
| 5–8 | Y |
| 9–16 | Strip: 72 holes, exactly 2n + 2 |
| 17–20 | C |

* The fold for T2 is "drop it 35 holes back and 6 holes back". A peg high in the strip therefore folds several times in a chain, which the simulation includes.

**Real tiers:** 5n + (toll length) + 10 holes of workspace, plus the separate key grid.
* Three registers X, Y and C, a 2n-hole strip, a toll register on grids, and the control lane.
* Chain grids in reading order to form each register.
* R3072 workspace: 3 × 1938 + 3876 + 969 + 10 = 10,669 holes = 107 grids, plus 1 key grid = 108 grids per player.
* Cursor ships (8 per player) lie against the frames of whichever grids they point into.
* No paper anywhere; nothing is stored off the grids.

---

## 7. Tier table

Figures: `reference/tiers.py` (`tiers_output.txt`), from the key figures in `ships-pegs/combined.py` and the exchanges in `exchange/`. This is the ships+pegs key (one key grid) under the no-paper rule.
* **NFS:** the NIST SP 800-57 equivalences where tabulated (1024/2048/3072 bits → 80/112/128) [lit-mem]. Otherwise the L_p[1/3, 1.923] formula, shifted to match NIST at 1024 bits [est]. The formula is meaningless below ~128 bits.
* **Rho on q:** Pollard rho, ≈ √(πq/4). Pohlig–Hellman adds nothing, because p − 1 = 2q and g has prime order q.
* **Key √:** 141.6 bits per key grid by min-entropy (153.2 by Shannon), the √ heuristic of §4.9, capped at log₂(q)/2.
* **Security** is the minimum of the three.
* **Grids** = workspace ⌈(5n + toll + 10)/100⌉ + 1 key grid. **Game sets** = ⌈grids/4⌉ (only grids count).
* **Mults per person** = 1,048.8 = 4 × 211.10 cells (2 walks × a 2-multiplication cube per cell, from the start marker on) + 203.35 hit multiplications in the shared walk + the check squaring; the mean over 20,000 built grids (`ships-pegs/combined.py`).
* **Moves per mult** is measured in full exchanges with ships+pegs keys at every tier (`exchange/`; runs per tier in §8). **Moves per person** = 1,048.8 × moves per mult. Hand time at 1 move per second.

| Tier | Grids per player (workspace + key) | **Game sets** | n / p bits | NFS | Rho on q | Key √ | **Security** | Mults per person | Moves per mult | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|---|---|---|---|---|
| T1 skiff | 2 (1 + 1) | **1** | 18 / 29 | trivial | 2^13.8 | 2^14.0 cap | **≈ 2^14**; BSGS: 0.00 s | 1,049 | 464 | 4.87·10⁵ | 135 h / 17 days |
| T2 frigate | 3 (2 + 1) | **1** | 35 / 56 | trivial | 2^27.3 | 2^27.5 cap | **≈ 2^27**; rho: 3.3 s | 1,049 | 1,587 | 1.66·10⁶ | 19 days / 58 days |
| T6 demo | 7 (6 + 1) | **2** | 100 / 159 | ~2^31 [est] | 2^78.8 | 2^79.0 cap | **~2^31** | 1,049 | 18,798 | 1.97·10⁷ | 228 days / 22 months |
| R512 | 19 (18 + 1) | **5** | 323 / 512 | ~2^57 [est] | 2^255 | 2^141.6 | **~2^57** | 1,049 | 182,772 | 1.92·10⁸ | 6.1 years / 18 years |
| R1024 | 37 (36 + 1) | **10** | 646 / 1024 | 80 | 2^511 | 2^141.6 | **80** | 1,049 | 738,353 | 7.74·10⁸ | 25 years / 74 years |
| R2048 | 73 (72 + 1) | **19** | 1292 / 2048 | 112 | 2^1023 | 2^141.6 | **112** | 1,049 | 2,929,632 | 3.07·10⁹ | 97 years / 292 years |
| **R3072** | **108 (107 + 1)** | **27** | **1938 / 3072** | **128** | 2^1535 | 2^141.6 | **128** | **1,049** | **6,520,198** | **6.84·10⁹** | **217 years / 650 years** |

**Tiers:** R3072 (128-bit) is the top tier; 192- and 256-bit tiers (R7680, R15360) are out of scope as overkill for this toy. Every tier's key fits on one key grid.

Reading the table:
* In T1, T2 and T6 the key wraps mod q (§4.6), so its √ bound is the q cap; one key grid is still the minimum.
* The measured exchanges agree with the table: mean moves per person T1 4.89·10⁵; T2 1.66·10⁶; T6 1.97·10⁷; R512 1.89·10⁸; R1024 7.86·10⁸; R2048 3.01·10⁹; R3072 6.75·10⁹ (`exchange/`); single runs vary with the key's length and hit count.
* Both people work in parallel, so wall-clock time equals the per-person time.
* Scaling: with W workspace grids, n ≈ (100W − 10)/5.5 (long toll). Add the one key grid.
* Grid counts include the 10-hole control lane and the separate key grid (no-paper rule).
* **Real-world yardsticks for the weak tiers:**
  - A 512-bit DH prime was precomputed in about a week on 2,000–3,000 cores (~10 core-years). After that, each individual log took a median 70 s (Logjam, Adrian et al., CCS 2015) [lit].
  - The prime-field DLP record is 795 bits, about 3,100 core-years (Boudot et al., 2019/2020) [lit].
  - R1024 is plausibly within nation-state reach, the Logjam authors' estimate for 1024-bit primes [lit].

### 7.1 No-paper resources per player

The per-player grids and game sets are in the §7 table. Only grids count; pegs and ship pieces are provisioned, not counted (No-paper rule, which also gives the measured peaks).

---

## 8. Verification results

Paths are under `proofs/key_exchange/bs/`.

* **Parameters** (`reference/params_output.txt`, `params_323_output.txt`): every tier's p and q passed Miller–Rabin with 50 rounds and BPSW (sympy). T1 and T2 also passed deterministic Miller–Rabin (first 12 prime bases, valid below 3.3·10²⁴). 3^q ≡ 1 (mod p), p ≡ 11 (mod 12).
  - **Search effort:** R3072 took 4,113 candidates after sieving (27 s); R2048 took 502 and R1024 took 3,010.
* **Arithmetic** (`reference/run_output.txt`, `bigmul_output.txt`): operands are arbitrary register contents, including non-canonical values ≥ p.

  | Tier | Multiply | Multiply + nudge | Worst case (all-red × all-red, nudge 2) | Tidy |
  |---|---|---|---|---|
  | T1 | 300/300 | 300/300 | OK | 313/313, including all 10 values in [p, 3¹⁸) |
  | T2 | 300/300 | 300/300 | OK | 506/506 |
  | T6 | 100/100 | 100/100 | OK | 306/306 |

  - Full-size peg multiplications plus tidy with the real long tolls: R1024, R2048 and R3072 at 3/3 each. That took 1.1 s of Python per R3072 multiplication.
* **Exchanges with ships+pegs keys through the peg recipes** (`exchange/`): both parties build a key grid with the §4.2 dice (`ships-pegs/keygrid.py`), read it by §4.3, and run B9 with the peg recipes.

  | Tier | Exchanges | All correct | Mults per person | Moves per mult | Moves per person (mean) | Key cells (mean) |
  |---|---|---|---|---|---|---|
  | T1 skiff | 20 | yes | 1,053.4 | 464 | 4.89·10⁵ | 211.9 |
  | T2 frigate | 5 | yes | 1,047.9 | 1,587 | 1.66·10⁶ | 210.8 |
  | T6 demo | 2 | yes | 1,048.8 | 18,798 | 1.97·10⁷ | 211.8 |
  | R512 | 1 | yes | 1,034.5 | 182,772 | 1.89·10⁸ | 212.5 |
  | R1024 | 1 | yes | 1,065.0 | 738,353 | 7.86·10⁸ | 214.5 |
  | R2048 | 1 | yes | 1,027.0 | 2,929,632 | 3.01·10⁹ | 209.5 |
  | R3072 | 1 | yes | 1,036.0 | 6,520,198 | 6.75·10⁹ | 209.0 |

  In every run:
  - the public values equal pow(3, e, p) and lie in the order-q subgroup;
  - K_A = K_B = pow(3, 2·e_A·e_B mod q, p) = pow(B², e_A, p);
  - K is canonical.
* **Ships+pegs key** (`ships-pegs/`):
  - Entropy: layout H / H₂ / H∞ = 147.83 / 145.49 / 124.78 bits by exact DP, cross-checked by brute force and Monte Carlo; + 158.50 for the pegs (`build_dp.py`, `brute_build.py`, `viterbi.py`, `combined.py`).
  - Injectivity: exhaustive on 1×2, 2×1, 2×2, 1×5, 2×3, 3×2 and 1×7 (every layout × every peg pattern); 20,000 built 10×10 grids round-trip; 3,000 two-page keys decode (`combined.py`, `combined_multi.py`). Ship pass alone exhaustive up to 4×4 (`read_rule.py`).
  - Build: the board-only one-pass BUILD with random let-go/resume at the allowed points matches the exact joint model (chi-square 1,327.7 on 1,376 df at 2×2; 101,368 on 101,330 df at 2×3; `combined.py`). The literal §4.2 dice match it too, for the d12 + row cup and for the all-d6 fallback (`keygrid_check.py`). The d12 hole die equals the former rule exactly (`randomizer-kit/`, part B).
  - Walk: 211.10 cells, 203.35 hit units, 1,048.8 multiplications per grid (20,000 built grids; `combined.py`).
* **Malicious values** (`reference/run_output.txt`): 0, 1, p − 1 and p + 1 were rejected in all tiers. A non-residue was accepted and squared into the subgroup. The unchecked victim leaked e mod 2 in 4/4 trials.
* **Attacks on the toy tiers** (`reference/break_small_output.txt`), on public keys from ships+pegs key grids: T1 fell to baby-step/giant-step in Python in 0.00 s. T2 fell to Pollard rho in C in 3.3 s (9.19·10⁷ iterations; the time varies with the key). In both, Eve's K equalled the real K.
* **Parity check** (`reference/parity_check_output.txt`): it passes 300/300 on correct multiplications. It catches 63–66% of single wrong pegs injected while laying and 64–69% injected after folding (theory: 2/3).
* **Where the moves go** (R3072 multiplication, `reference/bigmul_output.txt`): 43% are carries; α = moves/n² ≈ 1.76 (T1 1.41, T2 1.35, long tolls 1.76–1.84); the fold is ~1,300 lifts, each laying a 663-peg toll.

---

## 9. Security analysis and caveats (pedantic)

1. **Toy tiers are broken, and I demonstrated it.**
   * T1: q ≈ 2^27.5, broken instantly.
   * T2: q ≈ 2^54.5, broken in 3.3 s.
   * Their two-peg primes are also SNFS-shaped, which doesn't matter at this size.
   * T6 (159 bits) should fall to NFS in minutes to hours with CADO-NFS [est; not attempted].
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
   * e ∈ [3^M, 2·3^M) with M ≤ 233 (one key grid): e < 2·3^233 ≈ 2^370, in a group of order 2^3071 at R3072. That is a standard short-exponent DH setting, but e is not uniform on that interval.
     - With a safe prime, short exponents don't leak through Pohlig–Hellman [lit, van Oorschot–Wiener].
     - Key strength by the √ heuristic: 141.6 bits (min-entropy) or 153.2 bits (Shannon) per grid, against targets of 80, 112 and 128 (§4.8).
     - The ship part is a sum of per-ship terms. The ship-split meet-in-the-middle is the natural attack (§4.9), and I have no proof that cleverer structured-key attacks don't exist [unverified]. At toy sizes this doesn't matter, because q caps everything.
5. **g = 3 and a base-3 exponent.**
   * A = ∏ (3^(3^(M−1−j)))^(dⱼ): a product of public table entries chosen by the key trits.
   * For the peg pass that is just a generic string of 100 uniform trits. For the ship pass, it is the per-ship structure the meet-in-the-middle exploits. I know no further weakness [est].
6. **Received values:** checked by square-first (B8). Tested, see §5.
7. **The shared secret is K = 3^(2ab).**
   * Any hashing of K happens outside BS (no-paper rule). K's "entropy" to Eve is bounded by CDH hardness, not by log₂ q.
   * K = 1 would need 2ab ≡ 0 (mod q), which has negligible probability. In T1 it is about 10⁻⁸.
8. **Side channels.**
   * *Public phase:* nearly uniform work (two multiplications per cell), but a watcher can see *where* copies are laid (the nudge).
   * *Shared phase:* hits cost one or two extra multiplications, so timing reveals the key.
   * Work out of sight. A constant-work variant does one "multiply by 1, C or C²" on every cell.
     - With a stored C² register (one more register) that is 1 multiplication per cell: 211.10 per grid, against 203.35 hit units on average (`ships-pegs/combined.py`).
     - It adds about a third to the shared phase if every cell does two multiplications instead [est].
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
    * "no better attack on fleet-structured exponents" (the key's ship pass);
    * that white pegs fit ship holes as well as red ones (§4.1);
    * hand-time assumptions (1 move/s, no errors);

---

## 10. Cost, and comparison with ECBS

* **R3072 per person:** 1,048.8 multiplications of 1938-trit numbers at 6.52 M moves each (measured in the R3072 exchange, `exchange/`) gives **6.84·10⁹ moves** (§7). That is ~217 years non-stop, or ~650 years at 8 h/day. ECBS (§4) needed 3.9·10⁷ moves per person for ~2^136. **BS is ~180× more work for 128 bits.**
* **Where it goes:**
  - ~80% cubing in the two walks (2 × ~211 cubes × 2 multiplications);
  - ~20% shared-phase hit multiplications (203.35 per grid, about 1 per cell);
  - within a multiplication, ~43% of moves are carries, and the long-toll fold is about a third of all moves (33% at R3072, 34% at R1024; `reference/bigmul_output.txt`).
* **ECBS §3 estimated ~1.3·10⁹ moves per 3072-bit exponentiation.** BS's figure is ~3.4·10⁹ (half of a person's exchange), for three reasons:
  - the ~211-cell ternary walk needs ~420 (public) to ~630 (shared) multiplications per walk, versus ~380 for a 256-bit binary exponent;
  - carries;
  - the long-toll fold.
* **Possible savings (none simulated):**
  - Karatsuba, −25 to −45% [est];
  - storing C² to avoid double multiplies on red hits [not estimated for this key].
* **Verdict:**
  - BS is a correct, honest, fully specified DH that runs on Battleship kit.
  - It is a fine teaching toy at 1–2 boards: textbook DH, a visible toll fold, a visible small-subgroup check, and a live demonstration that the result is broken in seconds.
  - At real sizes it is theoretically hand-doable only on multi-century timescales. For hand-scale security, ECBS is the better design by about two orders of magnitude.
