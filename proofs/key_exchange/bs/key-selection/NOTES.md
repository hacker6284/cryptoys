<!-- Owns: the record of how the BS key design was chosen (the comparison of candidate keys). Maintenance rules: ../../../../DOCS.md. -->
# BS key selection: why the key is ships + pegs

Status: **a note, not a theorem.** Nothing here is proved in Lean. The figures are copied from the scripts and drafts listed under "Sources"; the only new figure is the correction in §1 note 1. The chosen key is normative in [`primitives/key_exchange/bs/SPEC.md`](../../../../primitives/key_exchange/bs/SPEC.md) §4. Every other key below is analysis only and is not an option of the spec.

## 0. Metric

**The deciding metric is space: the fewest key grids per player.** Time, moves and multiplications do not count. They are listed below for the record only.

Security target per tier: the NFS level (R1024 80, R2048 112, R3072 128 bits). A key grid is sized so that √(key entropy) ≥ the target (the √ heuristic used throughout BS). The toy tiers (T1, T2, T6) are capped by q, so any one grid reaches their cap.

## 1. Bits per grid

| Key (one 10×10 grid) | Shannon H | Collision H₂ | Min-entropy H∞ | √ bound per grid | Aliasing loss |
|---|---|---|---|---|---|
| Pegs-only: a uniform trit in every hole | 158.50 | 158.50 | 158.50 | 79.25 (exact √ split / kangaroo, no slack) | 0 |
| Themed three-state fleet: one standard 5-ship fleet + 17 sign pegs | 51.81 (34.81 + 17)¹ | 51.81¹ | 51.81¹ | 25.9 generic¹; ship-split MITM ≈ 26.6 | 0 in BS (plain ternary numeral, injective while 3^(100G) < q) |
| Free fleet alone: grow until it bumps + fleet walk | 147.83 | 145.49 | 124.78 | not tabulated (H/2 heuristic) | 0 |
| **Ships + pegs: free fleet + a peg in every hole** | **306.33** | **303.99** | **283.28** | **153.2 (H) / 141.6 (H∞)** | **0** |

¹ **Correction: the 33.6-bit fleet figure is stale.** The former spec (Appendix A) and the six-state spike (Appendix B) give a standard fleet 33.6 bits (Shannon; 33.49 Rényi-2, ≤ 29.9 min-entropy). That is the entropy of the *covered-cell pattern*, which assumed ship labels are invisible (ECBS §1.1). Under the current counting every kind has its own visible piece (Sub ≠ Cruiser, §4.1 of the spec), and the full-restart placement is exactly uniform over labelled placements, so the standard fleet is **log₂ 30,093,975,536 = 34.81 bits** by all three measures (`../ships-pegs/free_fleet_count.py`, `run.log`: "standard fleet … log2=34.808756"). The dependent figures become: themed 50.6 → **51.81** bits per fleet, √ bound 25.3 → **25.9**; six-state 192.1 → **193.3** bits per grid, √ 96.1 → **96.65**; the six-state ship bit 0.155 → **0.161** bits per multiplication. Which figure applies depends on the read: the former themed and six-state reads saw only covered/uncovered, and 33.6 is what those reads encoded; 34.81 is the fleet's own entropy under the current counting, the best any read of it can do (the ships+pegs fleet walk reads labels, bows and all). The comparison here uses 34.81, the themed key's best case. The ship-split MITM figure 26.6 already counted labelled placements. Nothing in the comparison changes except the themed grid count at R3072 (6 → 5, §2). The appendices are kept verbatim; each stale figure there is marked "[stale, see §1 note 1]".

Also evaluated in the six-state spike (Appendix B): six-state cells (standard fleet + a peg in every cell), 193.3 bits (corrected from 192.1, note 1), √ ≈ 96.65 per grid; and a d6 per cell with no fleet shape, 258.5 bits, which needs 2 grids per key grid without paper.

## 2. Key grids per tier

| Tier (target) | Pegs-only | Themed three-state | Free fleet alone (by H / by H∞) | Six-state | d6 per cell | **Ships + pegs** |
|---|---|---|---|---|---|---|
| T1 | 1 | 1 | not tabulated (capped by q) | 1 | 1 | **1** |
| T2 | 1 | 2 | not tabulated (capped by q) | 1 | 1 | **1** |
| T6 | 1 | not tabulated | not tabulated (capped by q) | 1 | 1 | **1** |
| R512 (~57) | 1 | not tabulated | not tabulated | not tabulated | not tabulated | **1** |
| R1024 (80) | 2 (1 grid gives 79.25, just short) | 4 | 2 / 2 | 1 | 1 (2 physical) | **1** |
| R2048 (112) | 2 | 5 | 2 / 2 | 2 | 1 (2 physical) | **1** |
| **R3072 (128)** | 2 | 5 (6 before note 1) | 2 / **3** | 2 | 1 (2 physical) | **1** |

* Pegs-only trimmed to the exact cells needed (101 / 142 / 162 cells at R1024 / R2048 / R3072) still spills into a second grid in every real tier.
* Themed fleet count rule: G = ⌈NFS security / 25.9⌉ (4 / 5 / 5 at 80 / 112 / 128 bits; with the stale 25.3 it was 4 / 5 / 6). The toy-tier counts are the themed tier table's (T1 2 grids = 1 workspace + 1 key; T2 4 = 2 + 2).
* Per-player totals at R3072 (107 workspace grids + key grids): pegs-only 109, themed 112 (113 before note 1), free fleet 109 by H / 110 by H∞, ships+pegs **108**.
* The "toy tiers are capped by q, so 1 grid suffices for every encoding" line is the spike's (Appendix B §4).

**Result.** Ships + pegs is the only candidate that needs **one physical key grid in every tier**, sized by Shannon or by min-entropy (283.3 ≥ 2 × 128). It saves one grid per player at R1024–R3072 against pegs-only and the free fleet sized by H, two against the free fleet sized by H∞ at R3072, and three to four against the themed fleets.

## 3. For the record: costs that did not decide it

Per person, per key; moves at the measured moves per multiplication.

| Tier | Pegs-only whole grids: mults / moves | Pegs-only trimmed | Free fleet by H | Free fleet by H∞ | **Ships + pegs** |
|---|---|---|---|---|---|
| R1024 | 994.5 / 7.41·10⁸ | 499.5 / 3.72·10⁸ | 1,096 / 8.2·10⁸ | 1,096 / 8.2·10⁸ | **1,048.8 / 7.81·10⁸** |
| R2048 | 994.5 / 2.95·10⁹ | 704.5 / 2.09·10⁹ | 1,096 / 3.26·10⁹ | same | **1,048.8 / 3.11·10⁹** |
| R3072 | 994.5 / 6.58·10⁹ | 804.5 / 5.33·10⁹ | 1,096 / 7.26·10⁹ | 1,644 / 1.09·10¹⁰ | **1,048.8 / 6.94·10⁹ (+5.5 %)** |

* All columns use the moves per multiplication of random full-size products (`../reference/bigmul.py`), so they compare like with like. The SPEC tier table now uses the moves per multiplication measured in full ships+pegs exchanges (`../exchange/`), 0.9–1.6 % lower: 7.74·10⁸ / 3.07·10⁹ / 6.84·10⁹ at R1024 / R2048 / R3072.
* Themed three-state at R3072: 6 grids, 1.66·10¹⁰ moves (former tier table; 5 grids after note 1, not re-costed).
* Multiplications per Shannon bit: pegs-only 3.12, free fleet 3.71 (×1.19), ships + pegs 3.42 (×1.10); per min-entropy bit 3.12 / 4.40 / 3.70.
* Combining ships and pegs **saves grids, not multiplications**. Per bit, pegs-only is still the cheapest, especially when trimmed. That does not count here.
* At T1–R512 ships + pegs uses the same one grid as pegs-only and about 2.1× its multiplications (1,048.8 against 494 per person).

## 4. ECBS is not affected

ECBS keeps its own pegs-only key. A combined ships+pegs page uses up to 234 positions, above Lemma A's certified 175 at Serious and above n = 179, so it is not certified there; a single free-fleet grid is certified injective at Serious but is far below the 256-bit target.

## Sources

Paths are relative to this directory.

| Figure | Source |
|---|---|
| Ships + pegs entropy, walk, build, injectivity | `../ships-pegs/combined.py` → `combined_results.txt/.json`; `combined_multi.py` → `combined_multi_results.txt`; SPEC-literal dice: `../ships-pegs/keygrid_check.py` |
| Ships + pegs moves per person | `../exchange/` (full exchanges) and `../reference/tiers.py` |
| Free fleet alone: entropy (exact DP), walk, tiers | `../ships-pegs/build_dp.py`, `brute_build.py`, `viterbi.py`; `costs.py` → `costs_results.json` (here) |
| Free fleet read rule, injectivity | `../ships-pegs/read_rule.py` → `read_rule_results.txt` |
| Uniform-layout ceiling 150.19 bits; standard fleet 34.81 bits | `../ships-pegs/free_fleet_count.py` → `run.log`, `results_exact.json`, `results_mc.json` |
| ECBS Lemma A positions (§4) | `ecbs_lemma_a.py` → `ecbs_lemma_a_results.txt` (here) |
| Themed fleet dice (face rules, full-restart placement) | `themed_kit.py` → `themed_kit_results.json`, `ecbs13_kit.py` → `ecbs13_kit_results.json` (here) |
| Pegs-only and themed tier tables, themed fleet entropy, six-state spike | earlier BS drafts, **not in this tree**: `pegsonly.py`, `tiers.py` (themed), `fleet_entropy.py`, `sixstate.py`, `sixstate_sim.py`; their figures survive only as the verbatim text in Appendices A and B |
| Dice rules of the chosen key | [`../randomizer-kit/`](../randomizer-kit/README.md) |

---

## Appendix A. Former BS SPEC key sections (verbatim, removed from the spec)

The text below is the former `primitives/key_exchange/bs/SPEC.md` §4.0–§4.2 and the themed tier table from §7, kept as analysis. Section references inside it are to the former spec, and paths to the former layout (`free-fleet/` is now `../ships-pegs/`; `bs/` scripts are in `../reference/` or, for the dropped keys, not in this tree). The `[run]` marks are the former spec's.

#### 4.0 Default: pegs-only key grids (no paper)
* **Generation** (randomizer kit, 2026-09-30, approved by Zachary; `proofs/key_exchange/bs/randomizer-kit/`): each key grid is a 10×10 grid of 100 holes, filled row by row. The walk cursor's row ship marks the row being filled, because empty holes leave no mark.
  - **Row cup (default):** "At the start of each row, throw the five d10s (red, orange, yellow, green, blue) into the tray. Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each: red holes 1–2, orange 3–4, and on to blue 9–10. Picture a phone keypad (1 2 3 / 4 5 6 / 7 8 9, with 0 hanging below): the row a number sits in gives the first hole, the column gives the second. Top is empty, middle white, bottom red. When both of its holes are done, the die goes back in the cup."
  - **Exact.** Faces 1–9 correspond one-to-one to pairs of trits (3 × 3). A 0 is re-thrown on its own face only, which is rejection sampling. So every hole gets an exactly uniform, independent trit.
  - **Cost per grid:** 50 dice, 55.5 d10 reads, 14.6 throws. 10 % of reads are void 0s (5.5 per grid) [run: `proofs/key_exchange/bs/randomizer-kit/randomizer_kit.py`].
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

#### 4.1 Optional themed variant: three-state fleet key (toy tiers; ECBS §1 reused)

* **Placement:** the ECBS §1.3 full-restart dice procedure, read with the randomizer kit (2026-09-30, approved by Zachary; `proofs/key_exchange/bs/randomizer-kit/`). For each ship, largest first (5, 4, 3, 3, 2):
  1. **Roll the d20.** Bottom half (1–10) lies across, top half (11–20) lies down. The **last digit** (0 = 10) is its row if across, its column if down.
  2. **Roll the along-die** for its first hole, re-rolling any number that would hang it off the grid. The along-die is the smallest die that can still put the far end in hole 10: **Carrier d6, Battleship d8, Sub and Cruiser d8, Destroyer d10.**
  3. **If it overlaps an earlier ship, pick up the whole fleet and start again** from the Carrier (acceptance 0.389, unchanged). Ships may touch; they may not overlap.
  4. **Signs:** go along the ship cells in walk order, one d8 per two cells. For the first cell, bottom half (1–4) is white and top half red. For the second cell, odd is white and even red.
  - **Exact:** each ship is uniform on its 2·10·(11 − L) placements, exactly as with the former coin + d10s, and the restart keeps the fleet uniform. The entropy figures below stand.
  - **Cost per fleet:** 30.4 reads instead of 52.2, and 0.51 off-grid re-rolls instead of 3.95 [run: `proofs/key_exchange/bs/randomizer-kit/ecbs13_kit.py`].
  - The former coin + d10 + coin-per-cell procedure gives the same distribution and remains valid.
* **Exponent:** e = Σⱼ dⱼ·3^(M−1−j) over the M = 100G cells in walk order, with dⱼ = 0 (water), 1 (white) or 2 (red).
  - **The fleet boards, read in order, are e written in ternary**, most significant cell first. (Inside registers, hole 0 is least significant. The walk is Horner's rule, so the two orders are opposite. Don't mix them up.)
  - Because digits are < 3, the map from signed fleets to e is **injective** as long as 3^(100G) < q. That holds in every real tier, so ECBS's entropy counts carry over exactly.
* **Entropy per fleet [run, from ECBS]:** 33.6 bits of covered-cell pattern (Shannon) + 17 sign bits = **50.6 bits**. *[Stale fleet figure: see §1 note 1.]*
  - The collision (Rényi-2) entropy is 33.49 + 17 = 50.49 bits [run, `fleet_entropy.py`], so birthday-style attacks don't get a discount. *[Stale fleet figure: see §1 note 1.]*
  - Min-entropy is ≤ 29.9 + 17 bits (the most frequent covered pattern seen arises from 30 labelled placements). *[Stale fleet figure: see §1 note 1.]*
* **Attacks on the key set**, taking the smallest of these:
  - The generic bound 2^(entropy/2) ≈ 2^(25.3G).
  - ECBS's ship-split meet-in-the-middle, about 2^(26.6G). e is a *sum of per-ship terms*, so Eve tabulates 3^(e₁) over half-fleets and matches against A·3^(−e₂).
  - Kangaroo on the interval [0, 3^(100G)], about 2^(79G), which is irrelevant.
* **Fleet count rule (themed variant; shown for comparison, since real tiers use pegs-only):** G = ⌈(NFS security) / 25.3⌉. That gives 4 fleets for 80-bit, 5 for 112, 6 for 128, 8 for 192 and 11 for 256. *[Stale fleet figure: see §1 note 1.]*
* **Toy tiers:** 3^(100G) > q, so e wraps mod q. The fleet's 50.6 bits collapse to log₂ q (27.5 bits for T1). *[Stale fleet figure: see §1 note 1.]*
* **Why a ternary walk (cube) and not binary (square).**
  - Squaring per cell would cost about 1.9× less.
  - But with digits {0, 1, 2} in base 2, the fleet-to-exponent map is not injective. For example, a horizontal destroyer pegged red-red equals the same destroyer one cell to the left pegged white-white (2·2ʷ + 2·2^(w−1) = 2^(w+1) + 2ʷ).
  - I did not measure the resulting entropy loss [not run]. So I chose honesty over speed.
  - A base-4 walk (square twice) is injective but costs the same as cubing.

#### 4.2 Optional variant: free-fleet key (a grid full of ships)

* **What it is:** a key grid filled at random with **any number of ships** (kinds D2, S3, C3, B4, A5). Two rules:
  - **READ** ("the fleet walk") turns a grid full of ships into an exponent.
  - **BUILD** ("grow until it bumps") fills the grid at random with dice: a d12 hole die plus d6s.
  - Pegs-only (§4.0) stays the default. **This is a BS option only:** for ECBS only a *single* fleet grid at Serious is certified injective, and one grid is far below the 256-bit target, so ECBS stays pegs-only.
* **Grid and order.** One 10×10 grid (the **fleet grid**, any ocean grid). Reading order is row A to J, holes 1 to 10. A ship's **first hole** is the one you reach first in reading order: its left end if it lies across, its top end if it lies down. Its **last hole** is the other end; the holes in between are **middle** holes.
* **Pieces.**
  - Every kind has its own model, so Sub ≠ Cruiser.
  - A piece plugs into exactly its L holes and visibly lies across or down.
  - It has a **visible bow** (which end points where).
  - Pieces are unlimited, because extra fleets can be bought. The mean usage is ≈ 19 destroyers per grid, and the maximum possible is 50 D, 33 S or C, 25 B, 20 A.
  - Under BS's accounting, which counts fleets, a free-fleet key needs many fleets' worth of ships. I assume that doesn't matter.
* **No paper.**
  - BUILD needs no cursor. A white **miss peg** goes in every sea hole, so the next open hole is always the first hole that has neither a ship nor a peg.
  - While a ship grows, the piece lying on the board *is* the current length.
  - READ uses the walk cursor: 2 ships on the frame, parked before you let go. Control-lane hole 10 (spare) holds a peg while you do a Sub/Cruiser's extra cell.
* **Dice.** Fair dice: a d12 hole die, d6s for growth and Sub/Cruiser, d10s for pegs, rolled one at a time or taken from a rainbow queue. Every entropy figure assumes fair dice and the rule followed exactly. None of them applies to human-chosen fleets.

**READ: the fleet walk**

> **Walk the fleet grid in reading order, like a pegs-only key grid, but start as if there had been a white hit just before hole A1.** At each hole:
> - **No ship** (a miss peg or nothing): a **plain** cell.
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
* Several key grids are walked like pages, one after another, with a single start marker for the whole key.
* **Exponent:** e = 3^M + Σⱼ tⱼ·3^(M−1−j), with tⱼ ∈ {0, 1, 2} = plain/white/red and M = 100 + (number of Subs and Cruisers).
* **No aliasing.** Scan the holes in reading order, remembering which holes are already known to be covered:
  - At a hole not known to be covered: plain means sea; white/red means a ship starts here across/down, so its next hole is covered.
  - At a covered hole, plain means the ship goes on (mark its next hole). White or red ends it, giving the bow. The number of holes so far gives the kind: 2 D, 4 B, 5 A; for 3, read the extra cell to tell S from C.
  - So the cell string determines the layout. The start marker puts e in [3^M, 2·3^M), so e also determines M, and therefore the string. **Aliasing loss = 0 bits.**
  - Checked: every layout on 1×2, 2×2, 1×5, 2×3, 3×3, 2×5, 3×4 and 4×4 (3,996,513 layouts on 4×4) gives a distinct exponent, and decode(encode) is the identity; 20,000 exactly uniform and 20,000 built 10×10 layouts round-trip; 3,000 two-grid keys decode [run: `proofs/key_exchange/bs/free-fleet/read_rule.py`].
* **BS injectivity needs 2·3^M < q**, with M ≤ 134·G (G = number of key grids). True for R512 and up. False for T1, T2 and T6: there e wraps mod q, so injectivity mod q is not guaranteed, but those tiers are capped by log₂ q anyway.
* **Optional transcription.** Walk the grid once, laying the cells as pegs into a 2-grid key strip: a white marker peg first, then one peg or gap per cell, then a parked stop ship. The unchanged pegs-only B7 walk over that strip gives the same e. It costs ≈ 70 pegs and 2 extra grids per fleet grid (M + 1 ≤ 134 < 200 holes), so it is only worth it if you want to clear the fleet grid before the walk.

**BUILD: grow until it bumps**

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

* **Why the d12 is exact.** The former wording rolled sea on 1–2, then a heading on 1–3 / 4–6, and "rolled again for this hole" if not even a Destroyer fitted. That is rejection sampling. Sea has weight 1/3 and each heading 1/3 if it has room. After renormalising:
  - both headings open: 1/3, 1/3, 1/3 (the d12 thirds);
  - one heading open: 1/2, 1/2 (the halves);
  - none open: sea.
  - The bow is an independent fair bit. On a d12, odd/even splits every third (2 + 2) and every half (3 + 3) evenly, so it is independent of the hole decision.
  - Checked exactly, with Fractions: all 25 room states, and whole builds on 2×3, 3×3, 2×5 and 3×4 (64,557 layouts) are identical to the former rule [run: `proofs/key_exchange/bs/randomizer-kit/randomizer_kit.py`, part B].
  - The former wording (d6 sea roll, heading roll, roll again, d6 bow) gives the same distribution and remains valid.
* **All-d6, zero-reroll fallback** (equally exact):
  - The hole die is a d6: **1–2 sea, 3–4 across, 5–6 down**. If only one heading has room: **1–3 sea, 4–6 that heading**.
  - Roll a **separate d6 for the bow**: 1–3 bow at this hole.
  - Do **not** take the bow from a d6's odd/even. In the halves 1–3 / 4–6 it splits 2 : 1.
* Everything that is "in progress" is a piece or a peg on the board. The dice use only thirds, halves, odd/even on the d12, and "a six".

**Entropy and cost (fleet alone, per grid)**

* **Shannon H = 147.83 bits, collision (Rényi-2) H₂ = 145.49 bits, min-entropy H∞ = 124.78 bits** (exact DP over 5^10 profile states, cross-checked against brute force on small grids and by Monte Carlo) [run: `proofs/key_exchange/bs/free-fleet/build_dp.py`, `brute_build.py`, `viterbi.py`].
  - That is 2.35 bits below the uniform ceiling of 150.19 and 10.66 below pegs-only.
  - The min-entropy is lower because heavy grids exist: the most likely grid (p = 2^−124.78) is columns of down-ships separated by sea.
* **Walk:** 111.07 cells per grid on average (at most 133); 548.7 multiplications per grid per person, against 494.5 for pegs-only. That is **×1.19** per Shannon bit and **×1.41** per min-entropy bit.
* **Build:** 100.5 dice reads per grid (52.0 hole d12s, 37.4 growth d6s, 11.1 Sub/Cruiser d6s), with no re-rolls; ≈ 17 throws with rainbow queues of 6 d12s and 6 d6s. The all-d6 fallback needs 132.1 reads [run: `proofs/key_exchange/bs/randomizer-kit/randomizer_kit.py`, part C].
* **Grids by tier:** at R1024, R2048 and R3072 it needs the same 2 key grids as pegs-only (+10 % multiplications) if sized by Shannon entropy, and 3 grids at R3072 (+65 %) if sized by min-entropy.
* **Attacks:** the key is a sum of per-ship terms, so a ship-split meet-in-the-middle is the natural structured attack, and the √ bound is heuristic, as for the themed fleets (§4.1). I know no attack better than √.

**Ships + pegs: every hole also holds a peg**

* **Physical assumption** (confirmed from the Hasbro rules: 2002, 2011 and Retro editions). Ships sit in the ocean-grid holes and **cover** the grid holes under them, and each ship cell has its own peg hole. So a covered cell's peg goes in the ship's own hole and a sea cell's peg goes in the grid hole: **every one of the 100 cells takes exactly one 3-state peg**, on top of the layout.
  - **[Assumption to check on your set]** White pegs fit ship holes as well as red ones.

> **BUILD: "one hole at a time: ship, then peg." Lay the walk cursor (2 ships on the frame) at A1.** At the cursor hole:
> 0. **At the start of each row, throw the row cup:** the five d10s (red, orange, yellow, green, blue). Throw any 0 again until it shows 1–9. The dice go along the row in rainbow order, two holes each (red holes 1–2, …, blue 9–10).
> 1. **If no ship covers this hole, decide it with "grow until it bumps"** (the d12 hole die, then grow with the d6, swapping in the next longer piece; ships may touch). **Sea now leaves no mark.** There are no miss pegs any more.
> 2. **Peg it from its row-cup die.** Picture a phone keypad (1 2 3 / 4 5 6 / 7 8 9): the row the number sits in gives the pair's first hole, the column gives its second. Top is no peg, middle white, bottom red. Put the peg in the ship's hole if a ship covers this hole, otherwise in the grid hole. The die goes back in the cup after its second hole.
>    - **Zero-reroll fallback:** roll a d6 for the peg instead, 1–2 no peg, 3–4 white, 5–6 red.
> 3. **Move the cursor to the next hole** (reading order). After J10, park it off the grid.
>
> **Finish a hole before you let go.** The cursor is parked at the hole you are about to start. If you must let go between steps 1 and 2, first stand a **white peg in control-lane hole 10** ("ship decision made"). Lift it when you move the cursor.

* **The cursor is the record.** Every hole before the cursor is finished (ship decided and peg rolled). The cursor hole is undecided unless lane hole 10 holds a white peg. Every hole after it has no peg. So "no peg" never has to mean "sea decided", and a white peg always means a white key digit.
  - A ship laid at the cursor covers only the cursor hole and holes after it, none of which has a peg yet. Pegs behind the cursor are never in a ship's way, because ships grow only right or down.
  - The joint layout × peg distribution matches the exact model: chi-square 1,327.7 on 1,376 df (2×2, 400k builds) and 101,368 on 101,330 df (2×3, 300k builds) [run: `proofs/key_exchange/bs/free-fleet/combined.py`].

> **READ: "ships, then pegs." Walk the grid twice in a row without stopping the arithmetic.**
> 1. **Ship pass:** the fleet walk above, unchanged, including the start "as if a white hit before A1". Ignore the pegs.
> 2. **Peg pass:** go back to A1 and walk it as a **pegs-only key grid**: no peg = plain, white = white, red = red. Ignore the ships. A peg in a ship's hole counts just like one in a grid hole.
>
> **Several grids:** read them as pages, each page ships then pegs. There is one start marker for the whole key.
>
> *Mnemonic: "first read the fleet, then read the shots."*

* **Bookkeeping (no paper).** The walk cursor (2 ships on the frame) marks the hole. Control-lane hole 10 marks where you are within it: **empty** = ship pass; **red** = ship pass, Sub/Cruiser extra cell still to do; **white** = peg pass. At the end of a page, lift the lane peg, then put the cursor on the next grid's frame at A1.
* **Exponent:** e = 3^M + Σ tⱼ·3^(M−1−j) over the string (ship cells ‖ peg cells [‖ next page …]), with M = Σ over pages (100 + #3-holers + 100) ≤ 233 per page.
* **No aliasing.** The start marker puts e in [3^M, 2·3^M), so e determines M and the digit string. Within a page the ship pass is self-delimiting: the decoder knows after hole J10 exactly how many cells it has used (100 plus one per 3-holer), and the next 100 cells are the peg pass. So e determines each page's layout and pegs. Checked: every layout × every peg pattern on 1×2, 2×1, 2×2, 1×5, 2×3, 3×2 and 1×7 gives a distinct e (785,133 keys on 1×7); 20,000 built 10×10 grids round-trip; 3,000 two-page keys decode [run: `proofs/key_exchange/bs/free-fleet/combined.py`, `combined_multi.py`].
* **BS injectivity** needs 2·3^M < q, with M ≤ 233G + (marker): G ≤ 2 at R1024, ≤ 5 at R2048, ≤ 8 at R3072.
* **Entropy per grid:** the pegs are rolled independently of the layout, so every measure adds exactly; pegs add 100·log₂3 = 158.50 bits. **Grid total: 306.33 bits Shannon, 303.99 H₂, 283.28 H∞.**
* **Cost per grid:** 211.10 cells on average (at most 233); **1,048.8 multiplications** = 3.42 per Shannon bit (**×1.10** vs pegs-only) and 3.70 per min-entropy bit (×1.19). Build: 156 dice reads (100.5 layout + 55.5 peg d10s, 5.5 of them void 0s), about 31 throws, ≈ 265 moves.
* **Grids by tier:** one combined grid covers R1024–R3072 even when sized by min-entropy (283.3 ≥ 256), at **+5 %** (R3072: +5.5 %) over whole-grid pegs-only. Pegs-only **trimmed** stays the cheapest per bit at every tier.

#### Former §7: themed three-state tier table

| Tier | Grids (workspace + key) | Fleets (key + cursors) | Game sets | Security | Moves per person | Non-stop / 8 h per day |
|---|---|---|---|---|---|---|
| T1 | 2 (1 + 1) | 3 | 2 | ≈ 2^14 | 1.72·10⁵ [run] | 48 h / 6 days |
| T2 | 4 (2 + 2) | 4 | 2 | ≈ 2^27 | 1.33·10⁶ [run] | 15 days / 46 days |

## Appendix B. Former BS SPEC "Spike: six-state cells" (verbatim, removed from the spec)

Physically, a cell has 6 states: ship or no ship, times peg none/white/red. BS and ECBS currently use only 3 of them: water, ship + white, ship + red.

**Scripts:** `bs/sixstate.py` (arithmetic) and `bs/sixstate_sim.py` (peg simulation). Outputs are in `sixstate_output.txt` and `sixstate_sim_output.txt`.

**1. Entropy per grid.**
* Setup: a dice-placed standard fleet, plus an independent uniform peg (none/white/red) in **every** cell. Water holes take pegs; that is what white miss pegs are for. Roll a d6 per cell: 1–2 none, 3–4 white, 5–6 red.
* Pegs and ships are independent, so the entropies add exactly: H = H(covered pattern) + 100·log₂3 = 33.6 + 158.5 = **192.1 bits per grid** [run]. That is 3.8× the current 50.6. *[Stale fleet figure: see §1 note 1.]*
* Don't use log₂(placements × 3¹⁰⁰) = 34.8 + 158.5. Ship labels are invisible, so only the covered pattern counts (ECBS §1.1). *[Stale fleet figure: see §1 note 1.]*
* The ships contribute only 33.6 of the 192.1 bits (33.5 by Rényi-2). **Pegs alone give 158.5 bits per grid.** *[Stale fleet figure: see §1 note 1.]*

**2. Does it remove the ship-sum meet-in-the-middle?**
* No, and nothing can. In a DLP group, Eve can always split a product-structured key into two halves and match (BSGS-style). Generic-group lower bounds say about √ is also the floor [lit-mem, Shoup 1997].
* The current design's real problem was never that the meet-in-the-middle beats √(keys). It gives 2^26.6 against 2^25.3 per fleet. The problem is that there are only 2^50.6 keys. *[Stale fleet figure: see §1 note 1.]*
* Six-state raises the per-grid bound from 2^25.3 to **2^96.1**. The best split (ships plus 40 peg trits against 60 peg trits) costs about 2^97.3 [run]. *[Stale fleet figure: see §1 note 1.]*
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
* The ship bit costs 100 extra squarings per grid to encode 33.6 bits, i.e. 0.155 bits per multiplication. That is **worse than simply walking more peg cells**. *[Stale fleet figure: see §1 note 1.]*
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

* Additions are about 92% of ECBS's cost, and in the three-state design water cells cost only a cheap Frobenius. So the ships' 33.6 bits come *for free* there. That is the opposite of BS, where every cell costs a full cube. *[Stale fleet figure: see §1 note 1.]*

**Recommendation** (adopted 30 Sep 2026: pegs-only is now the BS default, §4.0).
* **BS:** drop the fleet from the exponent and **use pegs only**: a d6 per cell gives a uniform trit, and the walk stays the plain ternary walk.
  - It is the most efficient option per multiplication, and the recipe doesn't change.
  - R3072 drops from 6 grids and 1.66·10¹⁰ moves to 2 grids (or 162 cells) and about 6.6·10⁹ moves per person, 2.5× less.
  - If the ships must stay for the theme, six-state is a fair compromise: 1.75× cheaper than now, 1.4× dearer than pegs only.
* **ECBS:** keep three-state if moves matter (it's the cheapest per walk). Switch to pegs only if the board count matters (6 → 2 grids for +6% to +31% work).
* **Honesty note:** in every efficient option the key is really a random ternary string, and the fleet is at most a 33.6-bit garnish per grid. Entropies assume dice or d6 placement, never human choice. The rest of the caveats in §9 (structured short exponents, √ bounds as assumptions, side channels) carry over unchanged. In the shared phase, peg hits on two-thirds of the cells make timing leaks worse unless the constant-work variant is used. *[Stale fleet figure: see §1 note 1.]*
