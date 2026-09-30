# Randomizer kit for BS and ECBS keying (ADOPTED 2026-09-30, approved by Zachary)

**Status: ADOPTED (2026-09-30, approved by Zachary).** The six §8 wording changes have been applied to `BS.md` (top note, No-paper rule key bullet, §0, A4, §4.0, §4.1), `../ECBS_SPEC.md` (§0 R10, §4 recipe, §8 audit, §10), `../PEGBOARD_TERNARY.md` (§2.1 sign pegs, §2.3 placement) and `FREE_FLEET_KEY.md` (top note, §0, §1, §3.1, §3.2, §6, §7, §8.5). The plain d6 per hole stays the zero-reroll fallback. Pre-adoption copies: `/workspace/bs/kit/backup_pre_adoption/`.
- Every rule below either produces **exactly the same key distribution** as the spec rule it would replace (proved or checked in code), or is labelled otherwise.
- Zachary approved all six §8 wording changes on 2026-09-30, and they have been applied (see Status).

Toychest assumption (Zachary): unlimited full polyhedral sets (d4, d6, d8, d10, percentile d10, d12, d20), coins, cups and trays.
Scripts and outputs are in `kit/` (§9).

## 0. Summary: one toy per decision type

| Decision | Spec today | **Proposed toy** | Exact? | Reads per grid/fleet (spec → kit) | Rerolls |
|---|---|---|---|---|---|
| Peg trit (pegs-only key; ECBS key; peg phase of ships+pegs) | d6 per hole (ECBS: a 3-token bag) | **Row cup: 5 rainbow d10s, two holes per die, "phone keypad" read** | yes (9 faces ↔ 3×3) | 100 → **55.5** per 100 holes | d6 0 → d10 **10 % of reads void** (5.5 per 100 holes) |
| Ship build: sea / across / down | d6 sea (1–2), then d6 heading, and roll the whole hole again if that heading has no room | **Hole die: d12, thirds (or halves when one heading is blocked), odd/even = bow** | **yes, identical distribution** (all 25 room states, exact) | sea + heading + bow: 141.4 → **52.0** | 12.3 whole-hole re-rolls → **0** |
| Ship build: grow (from 2 on 4–6, from 3 and 4 on a 6), Sub/Cruiser (1–3 Sub) | d6 each | **Unchanged d6 reads**, taken from a rainbow d6 queue | spec | 48.6 → 48.5 | 0 |
| ECBS §1.3 themed placement: heading + row/column, along-coordinate, signs | coin + d10 + d10 (off-grid re-roll), coin per ship cell | **d20 (half = heading, last digit = cross coordinate) + best-fit along-die (d6/d8/d8/d10) + d8 signs (2 per die)** | yes (uniform per ship; restart unchanged) | 52.2 → **30.4** per fleet | off-grid 3.95 → **0.51** per fleet; restarts 1.57 (unchanged, algorithmic) |

- **Whole ship build (free fleet, grow until it bumps):** 190.0 reads, one d6 at a time, with 12.3 whole-hole re-rolls, become **100.5 reads (−47 %) and no re-rolls**, with the same layout distribution.
- **Ships+pegs grid (FREE_FLEET_KEY §8):** 290 d6 reads become **156 reads**: 100.5 for the build plus 55.5 for the pegs.
- **Throws:** with the batch "rainbow queue" (§2), throws drop to about one per 6 reads (build) or one per 3.8 reads (row cup).

## 1. Assumptions (pedantic)
1. **Dice.**
   - Every die is fair, and the dice in one throw land independently. This is the same assumption as FREE_FLEET_KEY A3. Every entropy figure depends on it.
   - A **throw** is one shake of one cup into the tray. A **read** is looking at one die and using it for one or two facts.
   - A die that lands cocked, or leaves the tray, is thrown again before anyone reads it.
2. **Faces.**
   - d10s are numbered 0–9. On a d10 numbered 1–10, "0" means the 10.
   - On a percentile d10 (00–90), read the tens digit, and 00 is "0".
   - A d4 is read by whatever convention the die uses: the number at the top vertex, or the number on the bottom edges. Both are uniform. The kit does not need d4s (§4.4).
3. **Colours only ever give an order, never a number.**
   - The fixed order is the **rainbow: red, orange, yellow, green, blue, purple**.
   - Reading a face and comparing ranges ("1–3", "odd", "which keypad row") is allowed. Colour-to-number arithmetic never happens.
4. **No paper.**
   - Dice lying in the tray are physical state (Zachary: allowed). A die is **never moved or turned until it is used**, and it goes back in the cup the moment it is used.
   - A knocked die is thrown again. Nobody may choose where a die goes after the throw.
   - BS's cursor ships and finger rule apply unchanged: finish the current hole, park the cursor, then let go.
5. **The work is done out of sight** (BS A7). Unused dice showing in the tray are future key material.

## 2. The rainbow queue (batching without bias)
> **Throw a cup of same-shape dice, one per rainbow colour. Whenever the recipe asks for a roll of that shape, use the next colour still in the tray, read it the way the recipe says, and put it back in the cup. When none are left, throw the whole cup again.**

- **Why it is exact (deferred decisions).**
  - The colour order is fixed before the throw, so it cannot depend on the faces.
  - Laid end to end over successive throws, the dice form an i.i.d. uniform sequence (a "tape").
  - The recipe reads the tape strictly in order and never reads an entry twice. Which question the next entry answers depends only on the board and on entries already read.
  - So every decision gets a fresh uniform die, independent of everything before it. The joint law is exactly that of rolling one die at a time.
  - Dice left unused at the end are simply returned. Unused *future* dice never influence a decision.
- **No hidden state.** The next die is "the first rainbow colour still in the tray". A pause between holes loses nothing.
- **Voids (d10 "0", along-die off the grid) are the only re-throws.** The decision to re-throw depends only on that die's own face, so the kept faces are uniform on the valid ones (rejection sampling). Nothing else is ever re-thrown or skipped.
- The draft's "dedicated-colour d6" idea is this queue with a single colour. The queue lets one throw serve six decisions.

## 3. Reading grammar (the only rules a player learns)
- **Thirds:** bottom / middle / top third of the faces = **empty / white / red** for a peg, and **sea / across / down** for the hole die.
- **Halves:** bottom half = the first choice, top half = the second.
- **A six** (d6) is the 1/6 event.
- **Odd/even is the only second fact** a die ever gives, apart from the d10 keypad. It is only used where it is exactly independent (§4.4 lists which dice qualify).
- **Phone keypad (d10):** picture 1 2 3 / 4 5 6 / 7 8 9 with 0 hanging below.
  - **The row a number sits in gives the first hole, the column gives the second.**
  - Top / middle / bottom row, and left / middle / right column, mean **empty / white / red**.
  - 0 is off the keypad, so throw that die again.

## 4. The decision types

### 4.1 Peg trits: the row cup (pegs-only key grids; ECBS pegs-only key; peg phase of ships+pegs)
> **At the start of each row, throw the five d10s (red, orange, yellow, green, blue) into the tray. Throw any 0 again until it shows 1–9. Then the dice go along the row in rainbow order, two holes each: red holes 1–2, orange 3–4, and so on to blue 9–10. For each die, the keypad row gives the first hole and the keypad column gives the second: top empty, middle white, bottom red. When both of its holes are done, the die goes back in the cup.**

- **Exact.** 1–9 map one-to-one onto (row, column) ∈ {top, middle, bottom}², so a non-void d10 is exactly two independent uniform trits. Void rate 1/10 [A: `randomizer_kit.py`].
- **Per 100 holes** [C, 20,000 runs]:
  - 50 dice, **55.5 reads**, 5.5 voids;
  - **14.6 throws** (one per row plus 0.46 re-throws of zeros).
  - For comparison, the spec d6 needs 100 reads and 0 voids (100 throws one at a time, or 16.7 with a 6-colour queue).
- **State.**
  - The dice still in the tray tell you which hole pairs of the current row are not done yet: colour ↔ pair.
  - The row itself needs BS's cursor (the row ship on the key grid's frame), or ECBS's coordinate rails. Empty holes leave no mark, so this is already true of the spec's d6 build.
- **Partial rows** (ECBS, or a trimmed BS key): throw only the dice for the holes needed. For an odd count, the last die gives only its **row** (first fact), which is uniform on its own.
- **ECBS's all-empty rule is unchanged:** if every key hole came up empty, roll the whole key again (probability 3^−m; 1/9 at Demo).
- **Alternatives checked** [A]:

  | Die | Result | Verdict |
  |---|---|---|
  | d6 thirds (spec) | Exact, 0 voids, 1 trit per read | Keep as the zero-void fallback |
  | d12 thirds | Exact trit + a spare coin that pegs can't use | No gain over d6 |
  | d20 last digit (void 10, 20) | Exact 2 trits + a teens coin, 10 % void | Same reads as the d10 but a harder read, and the coin is wasted on pegs. Rejected for trits |
  | Percentile | Is just two d10s | No gain (§4.4) |
  | ECBS token bag | Exact, 1 draw per hole | The d10 needs 45 % fewer reads |

### 4.2 Ship build "grow until it bumps": hole die d12 + growth d6s
> **At a hole no ship covers:**
> - **If neither heading has room for a Destroyer:** it is sea. No roll.
> - **If both have room:** roll the **hole die (d12)**. **1–4 sea, 5–8 across, 9–12 down.**
> - **If only one heading has room:** roll the hole die. **1–6 sea, 7–12 a ship in the open heading.**
> - **For a ship, the same die gives the bow: odd, bow at this hole; even, bow at the far end.**
> - Then **grow it exactly as now** with the d6s: from 2 holes on 4–6, from 3 and from 4 only on a 6, and stop without rolling when it bumps. **A 3-holer: 1–3 Sub, 4–6 Cruiser.**

- **Identical distribution to the spec, with no re-roll.**
  - In the spec, "roll again for this hole" is rejection sampling. Sea has weight 1/3 and each heading 1/3 × [room for 2]. After renormalising:
    - both headings open: 1/3 sea, 1/3 across, 1/3 down (the d12 thirds);
    - one heading open: 1/2 and 1/2 (the halves);
    - none open: sea.
  - The bow is an independent fair bit.
  - On a d12, odd/even is exactly balanced inside every third (2 + 2) and every half (3 + 3), so it is independent of the hole decision. **On a d6 it is not:** in the halves 1–3 / 4–6, odd/even goes 2 : 1 [A]. That is why the hole die is a d12.
  - The growth, kind and bow reads are unchanged.
  - Checked exactly (Fractions) [B]:
    - the kit's local distribution equals the spec's for **all 25 room states** (room across 1–5 × rows left 1–5);
    - whole-build distributions are identical on 2×3 (139 layouts), 3×3 (3,073), 2×5 (6,915) and 3×4 (64,557);
    - the Fraction reference equals the float model used in FREE_FLEET_KEY (3×3).
  - So H, H₂ and H∞ are exactly the FREE_FLEET_KEY values: 147.83 / 145.49 / 124.78 bits.
- **Per grid** [C, 20,000 grids]:

  | | Spec (d6 each) | Kit R (hole d6, bow d6) | **Kit (hole d12)** |
  |---|---|---|---|
  | Reads | 190.0 | 132.1 | **100.5** |
  | Whole-hole re-rolls | 12.3 | 0 | **0** |
  | Holes that are sea with no roll | – | 1.64 | 1.67 |
  | Throws, one at a time | 190 | 132 | 100.5 |
  | Throws with queues (6 d12 + 6 d6) | – | 22 | **≈ 17** (52.0 d12 reads / 6 + 48.5 d6 reads / 6, plus ≤ 2 at the end) |

- **Kit R** (a hole d6 read in thirds, 1–2 sea / 3–4 across / 5–6 down, or halves when blocked, plus a separate d6 for the bow) is also exact and keeps every read on a d6. It is the choice if a d12 feels foreign.
- **Hands-off.** Finish the hole, then park the cursor. The queue dice that are left carry over to the next hole.

### 4.3 ECBS §1.3 themed fleet placement (BS §4.1 themed variant, T1/T2)
> **For each ship, largest first (5, 4, 3, 3, 2):**
> 1. **Roll the d20.** Bottom half (1–10) lies across, top half (11–20) lies down. The **last digit** (0 = 10) is its row if across, its column if down.
> 2. **Roll the along-die for its first hole, re-rolling any number that would hang it off the grid.** The along-die is the smallest die that can still put the far end in hole 10: **Carrier d6, Battleship d8, Sub and Cruiser d8, Destroyer d10.**
> 3. **If it overlaps an earlier ship, pick up the whole fleet and start again** (unchanged).
> 4. **Signs:** go along the ship cells in walk order, one d8 per two cells. **Bottom half white, top half red for the first cell; odd white, even red for the second.**

- **Exact.**
  - d20: (half, last digit) takes each of the 2 × 10 values exactly once.
  - Along-die with off-grid rejection: uniform on the 11 − L valid starts.
  - So each ship is uniform on its 2·10·(11 − L) placements, exactly as with the spec's coin + d10s [D: checked for every L, both dice].
  - The full restart keeps the fleet exactly uniform over legal labelled fleets. Acceptance 0.389 (2.57 attempts), unchanged.
  - d8 (half, parity) is uniform on 2 × 2.
- **Per fleet** [D, 100–200k fleets]:

  | | Spec | Kit |
  |---|---|---|
  | Reads | 52.2 (35.2 placement + 17 sign coins) | **30.4** (21.4 + 9) |
  | Off-grid re-rolls | 3.95 | **0.51** |

  Off-grid re-roll rate per along-roll:

  | Ship | Spec d10 | Kit along-die |
  |---|---|---|
  | Carrier | 40 % | **0** (d6) |
  | Battleship | 30 % | 12.5 % (d8) |
  | Sub, Cruiser | 20 % | **0** (d8) |
  | Destroyer | 10 % | 10 % (d10) |

- **The restarts (1.57 per fleet) are the dominant waste.** They are part of the algorithm: retrying only the colliding ship biases toward sparse grids (PEGBOARD §2.3), so they stay.

### 4.4 The requested checks

| Toy / rule | Exact? | Memorable? | Verdict |
|---|---|---|---|
| **d8 as three coins** (top half; top pair of its half; odd/even) | Yes, 2×2×2 | The 2nd fact ("3–4 or 7–8") is not natural. | Use **two facts only** (half + odd/even, exact 2×2), as the sign die. |
| **d4, 2 bits** (top half 3–4; odd/even) | Yes | Reading conventions differ between d4 styles | Not needed; the d8 gives the same two facts on a flat top face. |
| **d12 as trit + coin** (thirds 1–4/5–8/9–12; odd/even) | Yes, 3×2. Halves + odd/even also exact (2×2). A third fact (bottom/top pair of the third) is exact 3×2×2 but not memorable | Yes | **Adopted as the hole die**, because both of its modes stay exact. |
| **d6 thirds + odd/even** | Yes, 3×2 | Yes | Exact, but **d6 halves + odd/even is 2:1** [A]. So the d6 can't carry the bow in the blocked-heading case. |
| **d20 last digit** (void 10, 20): keypad trits + teens coin | Yes, 18 = 9×2 | Moderate | Not for trits (same reads as a d10). A **void-free** d20 split, half + last digit, is adopted for §4.3. |
| **Percentile d10 + d10** | Only as two separate d10 keypad reads (4 trits, each die voided on 0). Using 81 of the 100 two-digit numbers needs base-3 arithmetic, which is forbidden | – | Nothing beyond two d10s. A percentile die can stand in as a sixth d10 colour. |
| **Coins in batches** | Exact if the coins are distinguishable and read in a fixed order (e.g. by value) | Coins roll off, land on edge, and need a denomination order | **Not needed.** Every 1/2 decision is absorbed as a second fact (heading into thirds, bow into d12 parity, signs into d8) or read on a d6 (Sub/Cruiser). |
| **"Dedicated-colour d6" for 1/3 and 1/6** | Yes | Yes | The 1/3 merges with the heading (thirds); the 1/6 growth stays "a six" on the d6 queue. |

## 5. The ships+pegs build (FREE_FLEET_KEY §8.5) with this kit
> **At each row: throw the row cup (and throw zeros again). At each hole, cursor on it:**
> 1. **If no ship covers it, use the hole die** (§4.2), and grow any new ship with the d6 queue.
> 2. **Peg it from the row cup:** the die of this hole's pair, keypad row for the pair's first hole, column for its second. Put the peg in the ship's hole or the grid hole.
> 3. **Return the d10 after its second hole, then move the cursor.**

- Everything is the same distribution as §8.5, because pegs and ships use separate dice and each rule is exact.
- **Per grid:** 100.5 build reads plus 55.5 peg reads = **156 reads**, about **31 throws** with queues, and 5.5 d10 voids. The spec is 290 d6 reads, one at a time.
- **State while paused:** board, cursor, row-cup dice in the tray (the pending pairs of this row), queue dice in the tray, and FREE_FLEET_KEY §8.5's lane marker if you let go mid-hole.

## 6. Per-tier kits and effort (per player)
Dice counts don't grow with the tier: cups are thrown again as needed. Only throws and reads grow. Key sizes are the spec's (BS §4.0/§7; ECBS §4.1). The ships+pegs row is FREE_FLEET_KEY §8 (proposed; one grid in every BS tier).

| Tier | Spec key | Cells / fleets | Kit | Throws / reads / voids (row cup) |
|---|---|---|---|---|
| BS T1 | 1 pegs-only grid | 100 | row cup | 14.6 / 55.5 / 5.5 |
| BS T2 | 1 pegs-only grid | 100 | row cup | 14.6 / 55.5 / 5.5 |
| BS R1024, R2048, R3072 | 2 pegs-only grids | 200 | row cup | 29.3 / 111.1 / 11.1 (162 trimmed cells: 24.6 / 90.0 / 9.0) |
| BS T1 / T2 themed | 1 / 2 fleets (§1.3) | 1 / 2 fleets | fleet dice (§4.3) | reads 30.4 / 60.8 (spec 52.2 / 104.4) |
| BS ships+pegs (proposed) | 1 grid, every tier | 100 + fleet | row cup + build tray | ≈ 31 throws / 156 reads / 5.5 voids |
| ECBS Demo | pegs-only | 2 | 1 d10 of the row cup | 1.11 / 1.11 / 0.11 (+ all-empty re-roll, 1/9) |
| ECBS Toy | pegs-only | 16 | row cup (5 + 3 dice) | 2.77 / 8.89 / 0.89 |
| ECBS Hobby | pegs-only | 51 | row cup (26 dice, last one row only) | 8.43 / 28.9 / 2.9 |
| ECBS Serious | pegs-only | 162 | row cup (81 dice; the last row has 2 holes = 1 full die) | 24.6 / 90.0 / 9.0 |

**Cup sizes:**
- **Row cup:** 5 d10s, one per rainbow colour except purple. One throw is one row.
- **Build tray:** 6 d12s and 6 d6s, the full rainbow. Minimum is 1 d12 + 1 d6, thrown one at a time.
- **Fleet dice:** d20, a d6, a d8 and a d10 as along-dice, and a sign d8.

## 7. For Scrounger (per player; double it for two players)
- **8 polyhedral sets** (7 dice each: d4, d6, d8, d10, percentile d10, d12, d20):
  - **one each in red, orange, yellow, green, blue, purple**;
  - **one white**;
  - **one black**.
  Choose plainly different, opaque colours; purple must not be confusable with blue. Faces should be numerals (d6 pips are fine). d10s should be numbered 0–9.
- **What gets used:**
  - **Row cup:** the d10s of red, orange, yellow, green, blue (5). The purple d10 and the percentile d10s are spares.
  - **Build tray** (free-fleet and ships+pegs builds only): the six rainbow d12s and the six rainbow d6s.
  - **Themed §1.3 fleet** (BS T1/T2 themed only):
    - white d20 (heading + cross coordinate);
    - black d6, black d8, black d10 (along-dice: Carrier; Battleship and 3-holers; Destroyer);
    - white d8 (signs).
  - Unused (d4s, other d20s): spares.
- **Cups:** 2 (a row cup, and a build/fleet cup).
- **Trays:** 2 rimmed, felt-lined dice trays, big enough that 12 dice lie flat without touching. The tray is where the queue waits.
- **Coins:** none needed.
- **Nothing else:** pegs, grids and cursor ships are already in the BS/ECBS kits.

## 8. Spec changes (approved by Zachary and applied 2026-09-30)
1. **BS §4.0 key generation:** "a d6 per hole" → the row cup (§4.1). The distribution is the same (uniform trits). The d6 stays valid as the zero-void fallback.
2. **ECBS §4 recipe:** the bag draw (white / red / destroyer) → the row cup. Same uniform trits; the all-empty re-roll is kept.
3. **FREE_FLEET_KEY §3.1 / §8.5 build wording:** sea + heading + "roll again for this hole" + bow → the d12 hole die (thirds/halves, odd = bow). **Same distribution, proven.** Growth and Sub/Cruiser wording stay the same.
4. **ECBS §1.3 / BS §4.1 themed placement:** coin + d10 + d10 + 17 coins → d20 + along-die + sign d8s. Same per-ship uniformity; the full restart is kept.
5. **Optional everywhere:** the rainbow queue (§2) as a batching rule.
6. **Not proposed (these would change distributions):** turning instead of re-rolling, dropping the restart, or other entropy trade-offs (see FREE_FLEET_KEY §3.3).

## 9. Scripts (`kit/`)

| Script | What it checks | Output |
|---|---|---|
| `randomizer_kit.py` | A: every face rule enumerated (exact uniformity, void rate, bits per read, the d6 halves+parity counterexample). B: kit hole rules equal the spec's local distribution for all 25 room states, and exact whole-build equality on 4 grids, cross-checked with the FREE_FLEET_KEY model. C: reads/throws/voids per grid (spec, kit R, kit d12, row cup at 2/16/51/100/162/200 holes). D: §1.3 per-ship uniformity for both along-dice, and reads/rerolls/restarts | `randomizer_kit_results.txt`, `.json` |
| `ecbs13_kit.py` | The proposed §1.3 kit end to end: d20 split and d8 exactness, reads 30.4, re-rolls 0.51, acceptance 0.389 | `ecbs13_kit_results.txt`, `.json` |
