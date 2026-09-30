# Free-fleet key: a 10×10 grid full of ships as a BS / ECBS private key

Follow-up to `FREE_FLEET.md`. There are two rules:
- **READ** ("the fleet walk"): turns a grid full of ships into an exponent.
- **BUILD** ("grow until it bumps"): fills the grid at random with dice (a d12 hole die plus d6s).

**Randomizer kit adopted (2026-09-30, approved by Zachary).** Key randomness now follows `RANDOMIZER_KIT.md` (verified by `kit/randomizer_kit.py`):
- **BUILD (§3.1, §8.5):** the d12 **hole die** replaces the sea roll, the heading roll, "roll again for this hole" and the bow roll. The layout distribution is **identical** (proven exactly for every room state), and there are no whole-hole re-rolls. Growth and Sub/Cruiser are still read on a d6. An all-d6 zero-reroll version is given too.
- **Pegs (§8.5):** the d10 **row cup**, with a d6 per hole as the zero-reroll fallback.
- **Optional everywhere:** the **rainbow queue**: throw a cup of same-shape dice, one per rainbow colour (red, orange, yellow, green, blue, purple). Each roll the recipe asks for takes the next colour still in the tray, and that die goes back in the cup once read. When none are left, throw the cup again. It is exact because the colour order is fixed before the throw and no die is read twice.
- **No entropy, cost-per-bit or tier figure changes.** Only roll counts change (§3.2, §8.5).

Every number below was computed by the scripts in `/workspace/bs/key/` (list in §7).
Note: `BS.md` is in this directory (`kx-specs/bs/BS.md`). ECBS is `../ECBS_SPEC.md`.

## 0. Summary

| per 10×10 key grid | pegs-only (d6: 1–2 empty, 3–4 white, 5–6 red) | **free fleet** (grow-until-it-bumps + fleet walk) |
|---|---|---|
| Key entropy: Shannon / collision (Rényi-2) / min-entropy | 158.50 / 158.50 / 158.50 bits | **147.83 / 145.49 / 124.78 bits** (exact DP) |
| Aliasing loss (different grids giving the same key) | 0 | **0**: the walk is proven injective and checked exhaustively (§2.4) |
| Ceiling if the layouts were exactly uniform | – | 150.19 bits (count A) |
| Walk cells (each one a BS cube) | 100 | 111.07 on average (100 + one per Sub/Cruiser; at most 133) |
| BS multiplications per grid per person (both walks + check) | 494.5 | 548.7 |
| **Multiplications per key bit** | 3.12 | 3.71 per Shannon bit (**×1.19**); 4.40 per min-entropy bit (**×1.41**) |
| Build (randomizer kit, 2026-09-30) | row cup: 55.5 d10 reads (d6 fallback: 100 rolls), ≈ 67 pegs placed | 100.5 dice reads, no re-rolls (former wording: ≈ 190 rolls), ≈ 110 moves (ships laid/swapped/turned + ≈ 22 miss pegs) |
| Ship pieces per grid (mean) | 0 | D 18.8, S 5.5, C 5.6, B 1.5, A 0.23 |

- **Bottom line for BS.** The themed key costs about 1.19× pegs-only per Shannon bit. At R1024/R2048/R3072 it needs the same 2 key grids (+10 % multiplications) if you size it by Shannon entropy. It needs 3 grids at R3072 (+65 %) if you size it by min-entropy.
- **Ships + pegs (§8).** A peg in every hole on top of the fleet: 306.33 / 303.99 / 283.28 bits per grid, read as "ships, then pegs", 1,048.8 multiplications = 3.42 per Shannon bit (×1.10 vs pegs-only). One grid covers R1024–R3072 even by min-entropy. Trimmed pegs-only is still the cheapest per bit.
- **Bottom line for ECBS.** Only a *single* fleet grid at Serious is certified injective, and one grid is far below the 256-bit target. Keep pegs-only for ECBS (§2.3).

## 1. Assumptions (pedantic)

1. **Grid and order.** One 10×10 grid (the "fleet grid", any ocean grid). Reading order is row A to J, holes 1 to 10. A ship's **first hole** is the one you reach first in reading order: its left end if it lies across, its top end if it lies down. Its **last hole** is the other end; the holes in between are **middle** holes.
2. **Pieces.**
   - Every kind has its own model, so Sub ≠ Cruiser.
   - A piece plugs into exactly its L holes and visibly lies across or down.
   - It has a **visible bow** (which end points where). This is why count A and the 2×2 opposite-destroyer case are not ambiguous (§2.4).
   - Pieces are unlimited, because extra fleets can be bought. The mean usage is ≈ 19 destroyers per grid, and the maximum possible is 50 D, 33 S or C, 25 B, 20 A.
   - Under BS's accounting, which counts fleets, a free-fleet key needs many fleets' worth of ships. I assume that doesn't matter.
3. **Randomness.**
   - Fair dice (randomizer kit, 2026-09-30, approved by Zachary): a d12 hole die, d6s for growth and Sub/Cruiser, d10s for pegs. They are rolled one at a time or taken from a rainbow queue. Dice are a source, not storage. Unused dice lying in the tray are allowed physical state and are never moved until used.
   - Every entropy figure assumes fair dice and the rule followed exactly. None of them applies to human-chosen fleets.
4. **No paper.**
   - BUILD needs no cursor. A white **miss peg** goes in every sea hole, so the next open hole is always the first hole that has neither a ship nor a peg.
   - While a ship grows, the piece lying on the board *is* the current length.
   - READ uses BS's walk cursor: 2 ships on the frame, parked before you let go. Control-lane hole 10 (spare in BS) holds a peg while you do a Sub/Cruiser's extra cell.
5. **BS injectivity needs 2·3^M < q**, with M ≤ 134·G (G = number of key grids).
   - True for R512 and up.
   - False for T1, T2 and T6: there e wraps mod q, so injectivity mod q is not guaranteed, but those tiers are capped by log₂ q anyway.
6. **Key strength.** I use "a key of entropy H costs about 2^(H/2)", BS's √ heuristic, as BS §4 does. I give it for both Shannon and min-entropy.
   - A ship-split meet-in-the-middle is the natural structured attack, as for BS's three-state fleets.
   - I know no attack better than √ [heuristic].
7. The work is done out of sight (as in BS A7).

## 2. READ: the fleet walk

### 2.1 As a player says it (BS)
> **Walk the fleet grid in reading order, like a pegs-only key grid, but start as if there had been a white hit just before hole A1.** At each hole:
> - **No ship** (a miss peg or nothing): a **plain** cell.
> - **A ship's first hole:** **white** if the ship lies **across**, **red** if it lies **down**.
> - **A ship's middle hole:** a **plain** cell.
> - **A ship's last hole:** **white** if the ship **points back** (its bow is at its first hole), **red** if it **points on** (the bow is right here).
>   Then, **if it is a Sub or a Cruiser, walk one more cell for this hole: plain for the Sub (it dives), white for the Cruiser.**
>
> *Mnemonic: "the start says which way it lies, the end says which way it points; Subs dive, Cruisers fly a flag."*

- "A cell" is exactly BS B7: cube the accumulator.
  - In the public phase, a white or red cell is the free nudge (1 or 2 holes).
  - In the shared phase, a white cell means multiply by C once, a red cell twice.
- "Start as if there had been a white hit": the public phase starts X as a lone white at hole 1; the shared phase starts X = C. After that, every hole cubes, including leading sea holes. This start marker is what makes keys of different lengths impossible to confuse (§2.4).
- Several key grids are walked like pages, one after another, with a single start marker for the whole key.
- **Exponent:** e = 3^M + Σ_j t_j·3^(M−1−j), with t_j ∈ {0, 1, 2} = plain/white/red and M = 100 + (number of Subs and Cruisers).
- **Optional transcription.** Walk the grid once, laying the cells as pegs into a 2-grid key strip: a white marker peg first, then one peg or gap per cell, then a parked stop ship. The unchanged pegs-only B7 walk over that strip gives the same e.
  - It costs ≈ 70 pegs and 2 extra grids per fleet grid; M + 1 ≤ 134 < 200 holes.
  - It is only worth it if you want to clear the fleet grid before the walk.

### 2.2 Costs of the walk (grow-until-it-bumps fleets, 20,000 simulated grids)
- Cells per grid: mean 111.07, largest seen 121, largest possible 133.
- Hit units per grid: 103.4 (shared phase: white = 1 multiplication, red = 2); non-zero cells per grid: 68.8.
- BS per grid per person: 4·111.07 (two walks × a 2-multiplication cube per cell) + 103.4 (shared hits) + 1 (check) = **548.7 multiplications**. Pegs-only: 494.5 (BS formula 500G − 5.5).
- Walk bookkeeping (cursor steps plus 2 control-peg moves per Sub/Cruiser) is a few hundred moves, which is negligible.

### 2.3 ECBS version
- **Same cells:** Frobenius, then add +P for white, −P for red, nothing for plain. The start marker means "start the accumulator at P".
- **Serious (n = 179):** digit differences are ≤ 2 and one grid uses ≤ 134 positions, which is within Lemma A's certified 175 (`read_rule.py` checks B² < ℓ exactly).
  - So one fleet grid is **injective mod ℓ**, and H∞(k) = 124.78 bits exactly.
  - A second grid (up to 268 positions) is **not certified**. It also exceeds n, so Frobenius aliasing occurs in principle.
  - With one fleet grid, the certified budget leaves ≤ 41 peg cells, giving ≤ 189.8 bits < 256.
- **Hobby, Toy, Demo:** the fleet's 111+ cells exceed both n and the certified lengths (55 / 19 / 3). That aliasing is **not measured**.
- **Cost:** 0.465 point additions per Shannon bit against pegs-only's 0.421 (×1.11), plus 111 Frobenius per grid against 100.
- **Verdict:** ECBS should stay pegs-only. The fleet walk is a BS option.

### 2.4 No aliasing: proof and checks
- **Decoder (`read_rule.decode`).** Scan the holes in reading order, remembering which holes are already known to be covered.
  - At a hole not known to be covered: plain means sea; white/red means a ship starts here across/down, so its next hole is covered.
  - At a covered hole:
    - Plain means the ship goes on (mark its next hole).
    - White or red ends it, giving the bow. The number of holes so far gives the kind: 2 D, 4 B, 5 A; for 3, read the extra cell to tell S from C.
  - So the cell string determines the layout.
- **The start marker** puts e in [3^M, 2·3^M), so e also determines M, and therefore the string.
- **Opposite destroyers in a 2×2 block**, which look identical under "(kind, part)" labels: across-pair = cells W W W R, down-pair = R R W R. They are different.
- **Checks, all run in `read_rule_results.txt`:**
  - Every layout on 1×2, 2×2, 1×5, 2×3, 3×3, 2×5, 3×4 and 4×4 (3,996,513 layouts on 4×4) gives a distinct exponent, and decode(encode) is the identity.
  - 20,000 exactly uniform 10×10 layouts and 20,000 built layouts round-trip.
  - 3,000 two-grid keys decode.
- **Aliasing loss = 0 bits.** (The "Sub = Cruiser" variant in §5 deliberately gives up 11.07 bits.)

## 3. BUILD: grow until it bumps

### 3.1 As a player says it (randomizer kit, 2026-09-30, approved by Zachary; `RANDOMIZER_KIT.md` §4.2)
> **Go to the first open hole in reading order** (no ship, no miss peg). A heading "has room for a Destroyer" when the next hole that way is on the grid and not under a ship.
> - **If neither heading has room:** it is **sea**, with no roll.
> - **If both have room, roll the hole die (d12): 1–4 sea, 5–8 across, 9–12 down.**
> - **If only one has room, roll the hole die: 1–6 sea, 7–12 a ship in the open heading.**
> - **Sea:** put a white miss peg in the hole.
> - **A ship:**
>   1. **Bow:** read the same hole die: **odd, bow at this hole; even, bow at the far end.** Turn each piece to match as you lay or swap it.
>   2. **Lay a Destroyer** from this hole in that heading.
>   3. **Grow it with the d6:** while there is room for one more hole, roll. From 2 holes it **grows on 4–6**. From 3 holes, and from 4, it grows **only on a 6**.
>      - **Growing means swapping the physical piece for the next longer ship, lying over the same holes plus the next one in its heading:** Destroyer → a 3-holer (Sub or Cruiser) → Battleship → Carrier.
>      - While a ship grows, the piece on the board *is* its current length.
>   4. **It stops growing** when a roll fails, or with no roll at all when it **bumps**: the next hole is off the grid or under a ship.
>   5. **A 3-holer:** roll the d6: **1–3 Sub, 4–6 Cruiser.** Swap in that piece if the one lying there is the other.
> - Repeat until every hole holds a ship or a miss peg.
>
> **Ships may touch**, side by side or end to end, as in Hasbro's rules. They never overlap: a ship only ever grows into open holes.

- **Why this is the former rule exactly.** The former wording rolled sea on 1–2, then a heading on 1–3 / 4–6, and "rolled again for this hole" if not even a Destroyer fitted. That is rejection sampling. Sea has weight 1/3 and each heading 1/3 if it has room. After renormalising:
  - both headings open: 1/3, 1/3, 1/3 (the d12 thirds);
  - one heading open: 1/2, 1/2 (the halves);
  - none open: sea.
  - The bow is an independent fair bit. On a d12, odd/even splits every third (2 + 2) and every half (3 + 3) evenly, so it is independent of the hole decision.
  - Checked exactly, with Fractions: all 25 room states, and whole builds on 2×3, 3×3, 2×5 and 3×4 (64,557 layouts) are identical to the former rule [`kit/randomizer_kit.py`, part B].
  - The former wording (d6 sea roll, heading roll, roll again, d6 bow) gives the same distribution and remains valid.
- **All-d6, zero-reroll version** (equally exact):
  - The hole die is a d6: **1–2 sea, 3–4 across, 5–6 down**. If only one heading has room: **1–3 sea, 4–6 that heading**.
  - Roll a **separate d6 for the bow**: 1–3 bow at this hole.
  - Do **not** take the bow from a d6's odd/even. In the halves 1–3 / 4–6 it splits 2 : 1.
- Everything that is "in progress" is a piece or a peg on the board. The dice use only thirds, halves, odd/even on the d12, and "a six".

### 3.2 Entropy (exact)
Measured with `build_dp.py`, a transfer-matrix DP over 5^10 profile states. It is cross-checked against brute force on 2×3 … 5×3 grids, and by a Monte Carlo run: E[−log₂ P] = 147.853 ± 0.019.

- **Shannon H = 147.834 bits.** That is 2.35 bits below the uniform ceiling of 150.19 and 10.66 below pegs-only.
- **Collision (Rényi-2) H₂ = 145.494 bits.**
- **Min-entropy H∞ = 124.780 bits** (`viterbi.py`). The most likely grid (p = 2^−124.78) is columns of down-ships separated by sea: lowercase = down, `.` = sea.
  ```
  .b.b.b.b..      Why this is the heaviest grid: a sea hole whose right-hand neighbour is
  .b.b.b.b..      already covered cannot start an across ship, so its roll is less spread
  .b.b.b.b..      out (the "roll again" boost). Each such hole costs about 1 bit instead of
  .bbbbbbbb.      about 1.6.
  ..b.b.b.b.
  ..b.b.b.b.
  .sbsbsbsb.
  .s.s.s.s..
  dsdsdsdsd.
  d.d.d.d.d.
  ```
- **The physical procedure matches the modelled distribution.** Chi-square of 300,000 simulated builds: 2×3 110.8 on 138 df, 3×3 3096 on 3072, 3×4 64234 on 64556 (`sim_bump.py`).
- **Build effort per grid** (randomizer kit, 2026-09-30, approved by Zachary):
  - **100.5 dice reads**: 52.0 hole d12s, 37.4 growth d6s and 11.1 Sub/Cruiser d6s. There are no re-rolls, and 1.67 holes per grid are sea with no roll.
  - With rainbow queues of 6 d12s and 6 d6s, that is ≈ 17 throws.
  - That is 0.68 reads per bit, against 0.35 for the pegs-only row cup (0.63 for its d6 fallback).
  - The all-d6 version needs 132.1 reads. The former wording needed 189.9 rolls, including 12.3 whole-hole re-rolls.
  - Moves are unchanged at 110.1 (≈ 22 miss pegs, ≈ 31.6 ships laid, grow swaps, turns).
  - The build is negligible next to the walk (a single R3072 multiplication is 6.6·10⁶ moves).

### 3.3 Other BUILD rules I evaluated (exact DP, bits)

| Rule (sea on 1–2 unless noted; "re-roll" = roll again for the hole) | H | H₂ | H∞ | cells |
|---|---|---|---|---|
| **grow until it bumps; re-roll if no room for 2 (recommended)** | **147.83** | **145.49** | **124.78** | 111.1 |
| same, growth 1/2, 1/6, **1/3** | 147.84 | 145.46 | 121.96 | 111.1 |
| same, growth **1/3**, 1/6, 1/6 | 147.21 | 144.62 | 123.66 | 107.8 |
| same, growth 1/2, **1/3**, 1/6 | 146.70 | 142.68 | 111.67 | 109.1 |
| grow until it bumps, **turn** it if no room | 146.73 | 142.84 | 122.51 | 111.6 |
| grow; **re-roll whenever it bumps** | 146.82 | 143.38 | 120.91 | 111.2 |
| grow; re-roll on bump, turn if no room for 2 | 146.12 | 141.80 | 122.82 | 111.8 |
| grow; if it doesn't fit, **leave the hole as sea** | 142.63 | 134.53 | 101.09 | 110.4 |
| "roll the ship's length" (1, 6 sea; 2 D; 3 S/C; 4 B; 5 A), re-roll | 126.37 | 107.91 | 77.46 | 106.3 |
| reference, not a dice rule: weights x^L, x = 0.31291, re-roll | 147.58 | 144.99 | 128.42 | 109.9 |
| exact uniform (the transfer-matrix sampler needs a table, which is forbidden) | 150.19 | 150.19 | 150.19 | 110.8 |

### 3.4 Exactly uniform by rejection: possible, but not practical
- **The only way I found to stay exactly uniform with a memorable rule** is to never re-roll. At each open hole:
  - sea has probability x;
  - each (kind, heading, bow) of length L has probability x^L;
  - anything else, including any ship that doesn't fit, means **clear the grid and start over**.
- Every finished grid then has probability x^100, so the result is exactly uniform. The acceptance rate is A·x^100.
  - The best x is 0.31291 (sea + all 20 ship options fill the die), which gives **acceptance 2^−17.43 ≈ 1 in 176,000 grids**.
  - The probabilities (x, x², …) are not d6-friendly. x = 5/16 with coins gives 2^−17.62.
  - "Roll until the runs agree" style acceptance tests are just ways of realising these x^L factors. They cannot beat A·min_q, and every local proposal I can think of is bounded the same way.
- **Verdict:** rejected. Uniformity would buy 2.35 bits of Shannon entropy and about 25 bits of min-entropy, at roughly 10⁵–10⁶ times the build effort.

## 4. Cost per key bit and tiers (BS, per person)

- **Per grid:** fleet 548.7 multiplications for 147.83 bits (Shannon), 145.49 (H₂) or 124.78 (H∞). Pegs-only: 494.5 for 158.50.
  - Multiplications per bit: **×1.19** (Shannon), ×1.21 (H₂), **×1.41** (min-entropy).
  - Public phase alone: 1.50 against 1.24 multiplications per bit (×1.21).
- **Tiers.** Grids are chosen to reach the NFS level at √(entropy). Moves use BS's measured moves per multiplication.

| Tier | Target | Pegs-only: grids / multiplications / moves | Fleet, sized by Shannon: grids / multiplications / moves | Fleet, sized by min-entropy |
|---|---|---|---|---|
| R1024 | 80 | 2 / 994 / 7.4·10⁸ | 2 / 1,096 / 8.2·10⁸ | 2 / 1,096 / 8.2·10⁸ |
| R2048 | 112 | 2 / 994 / 2.95·10⁹ | 2 / 1,096 / 3.26·10⁹ | 2 / same |
| **R3072** | 128 | **2 / 994 / 6.58·10⁹** | **2 / 1,096 / 7.26·10⁹ (+10 %)** | **3 / 1,644 / 1.09·10¹⁰ (+65 %)** |

## 5. Variants and notes
- **Sub = Cruiser variant.** Drop the extra cell and the Sub/Cruiser roll, so either piece may be used. Each grid is then exactly 100 cells with H = 136.76 bits, because the S/C roll is an independent fair bit per 3-holer, 11.07 per grid. That is 498.8 multiplications per grid, **×1.17** per Shannon bit: slightly cheaper per bit, but it breaks "Sub and Cruiser are different".
- **An optimal code would need about 93 cells per grid** (147.83 / log₂3), about 16 % fewer than the fleet walk. It would need an arithmetic code, which is not a memorable rule.
- **Security and side channels:** BS §9 applies unchanged.
  - The shared phase leaks the key through timing unless the constant-work variant is used.
  - The key is a sum of per-ship terms, so the √ bound is heuristic, as for BS's three-state fleets.
  - Heavy grids like the one in §3.2 exist, which is why the min-entropy is lower.

## 6. What a full key costs, per player (R3072, sized by Shannon)
- **Build:** 2 fleet grids, ≈ 201 dice reads with the randomizer kit (≈ 380 d6 rolls with the former wording), ≈ 220 moves, and ≈ 63 ships on average (≈ 38 D, 11 S, 11 C, 3 B, 0.5 A).
- **Walks:** 1,096 multiplications ≈ 7.26·10⁹ moves, against 6.58·10⁹ for pegs-only.
- The key grids are the fleet grids, so there are no extra grids beyond pegs-only's 2. The ships themselves are the extra cost.

## 7. Verification scripts (`/workspace/bs/key/`; randomizer kit: `kit/randomizer_kit.py`, `ecbs13_kit.py`)

| Script | What it checks | Output |
|---|---|---|
| `read_rule.py` | Encoder, decoder, exponent; exhaustive injectivity (8 grids up to 4×4); 20k uniform 10×10 round trips; ECBS Lemma A bound (Serious 175, Hobby 55 positions) | `read_rule_results.txt` |
| `read_rule.test_multi()` | 3,000 two-grid keys decode | (printed) |
| `build_dp.py` | Exact H, H₂, H∞, E[3-holers] for any local BUILD rule (5^10-state DP) | used by `run_rules.py` → `rules_*.json`, `run_rules*.log` |
| `brute_build.py` | Brute force on small grids == DP for 6 rules | `brute_build_results.txt` |
| `rules.py` | All candidate rules (§3.3) | – |
| `viterbi.py` | The single most likely grid (H∞ traceback) | `viterbi_bump_reroll.json`, `viterbi_grow.json` |
| `sim_bump.py` | Physical d6 simulation of the recommended rule: chi-square against the model, rolls, moves, cells, hits, pieces; MC Shannon | `sim_bump_results.json`, `sim_bump.log` |
| `sim_build.py` | Same for the "re-roll on bump" rule | `sim_build_results.json` |
| `costs.py` | Cost-per-bit and tier table | `costs_results.json` |

Uniform-layout facts (count A = 2^150.19, the exact sampler, 110.8 mean cells for uniform layouts) come from `/workspace/bs/free_fleet_count.py` (`FREE_FLEET.md`).

## 8. Ships + pegs: every hole also holds a peg (follow-up)

Zachary's point: ship pieces have peg holes, so a key grid can hold the free-fleet layout **and** a 3-state peg (empty/white/red) in every one of its 100 cells. All numbers below come from `key/combined.py` (output `key/combined_results.txt` / `.json`) and `key/combined_multi.py`.

### 8.1 Physical assumption (confirmed from the Hasbro rules)
- **Ships sit in the ocean-grid holes.** The 2002 edition says to fit each ship's 2 anchoring pegs into grid holes. The 2011 edition ships have pegs on the underside. Retro edition ships line up over the holes. Either way, a ship **covers** the grid holes under it.
- **Each ship cell has its own peg hole.** On a hit, the owner puts a red peg "into the hole of his hit ship directly above coordinate D-4". A ship is sunk "when all the holes in any one ship are filled".
- **Sea holes take pegs directly.** Misses are normally recorded on the target grid, and the rules say it is "not necessary" to record them on the ocean grid. That is optional, but physically possible.
- **Consequence:** a grid hole under a ship cannot take a peg, so that cell's peg goes in the ship's own hole (one per ship cell). A sea cell's peg goes in the grid hole. So **every one of the 100 cells takes exactly one 3-state peg**, on top of the layout. This matches ECBS's "one peg hole per ship cell".
- **[Assumption to check on your set]** White pegs fit ship holes as well as red ones. In the sets I know, both colours are the same peg.
- **Sources:** hasbro.com/common/instruct/BattleShip_(2002).PDF; the 2011 instructions (36934); the Retro Battleship instructions.

### 8.2 Entropy
The pegs are rolled independently of the layout, so every entropy measure adds exactly (H, H₂ and H∞ are all additive for independent parts). Pegs add 100·log₂3 = 158.496 bits.

| Layout source | Layout | + pegs | **Grid total** |
|---|---|---|---|
| Exactly uniform (count A, not buildable, §3.4) | 150.19 | 158.50 | 308.68 |
| **Grow until it bumps**, Shannon | 147.83 | 158.50 | **306.33** |
| Same, H₂ | 145.49 | 158.50 | **303.99** |
| Same, H∞ | 124.78 | 158.50 | **283.28** |

The read below is injective, so no bits are lost to aliasing.

### 8.3 READ: "ships, then pegs" (one walk, one accumulator)
> **Walk the grid twice in a row without stopping the arithmetic.**
> 1. **Ship pass:** the fleet walk of §2.1, unchanged, including the start "as if a white hit before A1". Ignore the pegs.
> 2. **Peg pass:** go back to A1 and walk it as a **pegs-only key grid**: no peg = plain, white = white, red = red. Ignore the ships. A peg in a ship's hole counts just like one in a grid hole.
>
> **Several grids:** read them as pages, each page ships then pegs. There is one start marker for the whole key.
>
> *Mnemonic: "first read the fleet, then read the shots."*

- **Bookkeeping (no paper).** The walk cursor (2 ships on the frame) marks the hole. Control-lane hole 10, spare in BS, marks where you are within it:
  - **empty** = ship pass;
  - **red** = ship pass, Sub/Cruiser extra cell still to do (this is §2's peg, now fixed as red);
  - **white** = peg pass.
  At the end of a page, lift the lane peg, then put the cursor on the next grid's frame at A1.
- **Exponent.** e = 3^M + Σ t_j·3^(M−1−j) over the string (ship cells ‖ peg cells [‖ next page …]), with M = Σ over pages (100 + #3-holers + 100) ≤ 233 per page.
- **No aliasing, proof.**
  - (i) The start marker puts e in [3^M, 2·3^M), so e determines M and the digit string.
  - (ii) Within a page, the ship pass is self-delimiting. §2.4's decoder reads holes in order and knows after hole J10 exactly how many cells it has used (100 plus one per 3-holer). The next 100 cells are then the peg pass, one per hole in reading order. So e determines each page's layout and pegs. ∎
  - Equivalently, for one page, e = 3^100·E_fleet + P with 0 ≤ P < 3^100 (P is the peg digits). Division by 3^100 recovers both.
- **Checks.**
  - Every layout × every peg pattern on 1×2, 2×1, 2×2, 1×5, 2×3, 3×2 and 1×7 gives a distinct e, and decode is the identity. The largest case is 785,133 keys on 1×7.
  - 20,000 built 10×10 grids round-trip.
  - 3,000 two-page keys decode to both grids.
- **Alternative, equally injective: interleaved single pass.** At each hole, walk *its peg cell first, then its ship cell(s)*. It decodes hole by hole because the peg cell always comes first and is always exactly one cell. Same cells, same cost, also checked exhaustively on the same grids. I prefer two passes: each pass is a walk the player already knows, and there is no mid-hole sub-step to remember.
- **ECBS.** A combined page uses up to 234 positions, which is above Lemma A's certified 175 at Serious and above n = 179. It is **not certified**, so ECBS stays pegs-only (as in §2.3).

### 8.4 Cost per key bit (BS, per person, 20,000 built grids)
- **Cells per page:** 211.10 on average (largest seen 222, largest possible 233). Hit units per page: 203.35.
- **Multiplications per page:** 4·211.10 + 203.35 + 1 = **1,048.8**.

| Key grid | Multiplications per grid | Bits per grid (H / H∞) | **Multiplications per Shannon bit** | Per min-entropy bit | Public phase per bit |
|---|---|---|---|---|---|
| Pegs-only | 494.5 | 158.50 / 158.50 | **3.12** | 3.12 | 1.26 |
| Ships-only (free fleet) | 548.7 | 147.83 / 124.78 | 3.71 | 4.40 | 1.50 |
| **Ships + pegs** | **1,048.8** | **306.33 / 283.28** | **3.42 (×1.10 vs pegs-only)** | **3.70 (×1.19)** | 1.38 |

- **Marginal view.** Adding pegs to a fleet grid costs 500 multiplications for 158.5 bits, i.e. 3.15/bit (the pegs-only rate). Adding ships to a peg grid costs 548.7 for 147.8 bits, i.e. 3.71/bit.
- So combining **saves grids, not multiplications**. Per bit, pegs-only is still the cheapest, especially when trimmed to the exact number of cells needed.
- **BS injectivity** needs 2·3^M < q, with M ≤ 233G + (marker). That is G ≤ 2 at R1024, ≤ 5 at R2048, ≤ 8 at R3072, and more at the higher tiers. Every configuration in §8.6 passes (`injective_mod_q` in the JSON).

### 8.5 BUILD: "one hole at a time: ship, then peg"
> **Lay the walk cursor (2 ships on the frame) at A1.** At the cursor hole:
> 0. **At the start of each row, throw the row cup:** the five d10s (red, orange, yellow, green, blue). Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each (red holes 1–2, …, blue 9–10).
> 1. **If no ship covers this hole, decide it with "grow until it bumps"** (§3.1: the d12 hole die, then grow with the d6, swapping in the next longer piece; ships may touch). **Sea now leaves no mark.** There are no miss pegs any more.
> 2. **Peg it from its row-cup die.** Picture a phone keypad (1 2 3 / 4 5 6 / 7 8 9): the row the number sits in gives the pair's first hole, the column gives its second. Top is no peg, middle white, bottom red. Put the peg in the ship's hole if a ship covers this hole, otherwise in the grid hole. The die goes back in the cup after its second hole.
>    - **Zero-reroll fallback:** roll a d6 for the peg instead, 1–2 no peg, 3–4 white, 5–6 red.
>
> (Randomizer kit, 2026-09-30, approved by Zachary; `RANDOMIZER_KIT.md` §5. The rule is the same as before this change, with exactly the same joint distribution.)
> 3. **Move the cursor to the next hole** (reading order). After J10, park it off the grid.
>
> **Finish a hole before you let go.** The cursor is parked at the hole you are about to start. If you must let go between steps 1 and 2, first stand a **white peg in control-lane hole 10** ("ship decision made"). Lift it when you move the cursor.

- **Why this resolves the miss-peg conflict.** In §3 the white miss peg was the only record that a sea hole was decided. Here the **cursor is that record**.
  - Every hole before the cursor is finished (ship decided and peg rolled).
  - The cursor hole is undecided unless lane hole 10 holds a white peg.
  - Every hole after it has no peg.
  So "no peg" never has to mean "sea decided", and a white peg always means a white key digit.
- **No physical conflicts.**
  - A ship laid at the cursor covers only the cursor hole and holes after it. None of those has a peg yet, so a ship never has to go over a peg.
  - "Bumps" still means only "the edge or another ship". Pegs behind the cursor are never in a ship's way, because ships grow only right or down.
  - A covered hole's ship hole is still empty when the cursor reaches it.
- **Board-only state.** `combined.step()` reads nothing but the board: ships, pegs, cursor, lane hole 10. `build_combined()` serialises the board and rebuilds it from scratch at random step boundaries ("letting go"), so there is no hidden state.
  - The joint layout × peg distribution matches the exact model (bump-rule layout probability × 3^−100): chi-square **1,327.7 on 1,376 df** (2×2, 400k builds) and **101,368 on 101,330 df** (2×3, 300k builds).
  - Example of why the lane marker is needed: a sea decision without it leaves the board exactly as before, so resuming would re-roll the hole.
- **Effort per grid:**
  - Dice reads with the randomizer kit: **156** = 100.5 layout + 55.5 peg d10s (5.5 of them void 0s). That is about **31 throws** with queues and the row cup. The former wording needed 289.9 d6 rolls (189.9 layout + 100 peg).
  - While paused, the row-cup d10s still in the tray show the unfinished hole pairs of the current row.
  - Moves: ≈ 88 ship moves (§3's 110.1 minus the ≈ 22 miss pegs) + ≈ 66.7 pegs + 110 cursor moves ≈ **265**. Using the lane marker at every hole adds up to 200 more (the simulator counts it every time: 454.8).
  - Pieces: ≈ 31.6 ships (≈ 6.3 fleets' worth) and ≈ 67 pegs per grid.

### 8.6 Tier table (BS, per person; grids sized so √(entropy) ≥ NFS target)
- **Combined page:** √ gives 153.2 bits (Shannon) or 141.6 bits (min-entropy) per grid.
- **Pegs-only:** 79.25 bits per grid.
- "Trimmed" = the last grid only partly filled (the pegs-only walk stops after the needed cells; ⌈2·target/log₂3⌉ cells, 5 multiplications each).

| Tier | Target | Pegs-only whole grids: grids / mults / moves | Pegs-only trimmed: cells / mults / moves | **Ships+pegs (Shannon and min-entropy alike): grids / mults / moves** |
|---|---|---|---|---|
| R1024 | 80 | 2 / 994.5 / 7.41·10⁸ | 101 / 499.5 / 3.72·10⁸ | **1 / 1,048.8 / 7.81·10⁸** |
| R2048 | 112 | 2 / 994.5 / 2.95·10⁹ | 142 / 704.5 / 2.09·10⁹ | **1 / 1,048.8 / 3.11·10⁹** |
| **R3072** | 128 | **2 / 994.5 / 6.58·10⁹** | 162 / 804.5 / 5.33·10⁹ | **1 / 1,048.8 / 6.94·10⁹ (+5.5 %)** |

- **One combined grid covers R1024–R3072 even when sized by min-entropy** (283.3 ≥ 256). Sized that way, the ships-only fleet key needed 3 grids at R3072.
- **Verdict.**
  - Ships + pegs fits on one key grid for every remaining tier.
  - It costs **+5 %** (R1024–R3072) over whole-grid pegs-only.
  - Pegs-only **trimmed** stays the cheapest per bit at every tier.

### 8.7 Scripts (additions)

| Script | What it checks | Output |
|---|---|---|
| `key/combined.py` | Two-pass and interleaved encoders/decoders; exhaustive injectivity (every layout × every peg pattern on 7 grids, both orders); board-only one-pass BUILD with random let-go/resume; joint chi-square on 2×2 and 2×3; 20k 10×10 round trips (both orders); cells, hits, rolls, moves; entropy sums; tier table with the BS injectivity check | `key/combined_results.txt`, `key/combined_results.json` |
| `key/combined_multi.py` | 3,000 two-page keys (ships, pegs, ships, pegs) decode to both grids | `key/combined_multi_results.txt` |
