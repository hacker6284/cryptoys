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
| Themed three-state fleet: one standard 5-ship fleet + 17 sign pegs | 51.81 (34.81 + 17)¹ | 51.81¹ | 51.81¹ | 25.9 generic¹; ship-split MITM ≈ 26.6 | 0 in BS: a plain ternary numeral, injective while 3^(100G) < q |
| Free fleet alone: grow until it bumps + fleet walk | 147.83 | 145.49 | 124.78 | not tabulated (H/2 heuristic) | 0 |
| **Ships + pegs: free fleet + a peg in every hole** | **306.33** | **303.99** | **283.28** | **153.2 (H) / 141.6 (H∞)** | **0** |

¹ **Correction: the 33.6-bit fleet figure is stale.** The former spec's themed variant (§4.1) and its six-state spike, in #146, commit 9e6b625, `kx-specs/bs/BS.md`, give a standard fleet 33.6 bits (Shannon; 33.49 Rényi-2, ≤ 29.9 min-entropy). That is the entropy of the *covered-cell pattern*, which assumed ship labels are invisible: only covered versus uncovered cells could be read. Under the current counting every kind has its own visible piece (Sub ≠ Cruiser, §4.1 of the spec), and the full-restart placement is exactly uniform over labelled placements, so the standard fleet is **log₂ 30,093,975,536 = 34.81 bits** by all three measures (`../ships-pegs/free_fleet_count.py`, `run.log`: "standard fleet … log2=34.808756"). The dependent figures become: themed 50.6 → **51.81** bits per fleet, √ bound 25.3 → **25.9**; six-state 192.1 → **193.3** bits per grid, √ 96.1 → **96.65**; the six-state ship bit 0.155 → **0.161** bits per multiplication. Which figure applies depends on the read: the former themed and six-state reads saw only covered/uncovered, and 33.6 is what those reads encoded; 34.81 is the fleet's own entropy under the current counting, the best any read of it can do (the ships+pegs fleet walk reads labels, bows and all). The comparison here uses 34.81, the themed key's best case. The ship-split MITM figure 26.6 already counted labelled placements. Nothing in the comparison changes except the themed grid count at R3072 (6 → 5, §2). The former text is not copied here. It is in #146, commit 9e6b625, `kx-specs/bs/BS.md`, where its 33.6-bit figures stand uncorrected.

Also evaluated in the six-state spike ("Spike: six-state cells" in #146, commit 9e6b625, `kx-specs/bs/BS.md`): six-state cells, a standard fleet + a peg in every cell, 193.3 bits (corrected from 192.1, note 1), √ ≈ 96.65 per grid; and a d6 per cell with no fleet shape, 258.5 bits, which needs 2 grids per key grid without paper.

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
* Themed fleet count rule: G = ⌈NFS security / 25.9⌉ (4 / 5 / 5 at 80 / 112 / 128 bits; with the stale 25.3 it was 4 / 5 / 6). The toy-tier counts are the former themed tier table's: T1 2 grids = 1 workspace + 1 key; T2 4 = 2 + 2. Source: §7 of #146, commit 9e6b625, `kx-specs/bs/BS.md`.
* Per-player totals at R3072 (107 workspace grids + key grids): pegs-only 109, themed 112 (113 before note 1), free fleet 109 by H / 110 by H∞, ships+pegs **108**.
* The "toy tiers are capped by q, so 1 grid suffices for every encoding" line is the spike's: #146, commit 9e6b625, `kx-specs/bs/BS.md`.

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

## 5. Design choices kept out of the spec

Moved here from `primitives/key_exchange/bs/SPEC.md` (DHH's #152 review: the spec states the rules, and the options that lost are argued here). Section numbers in this part are the spec's.

**Why plain ternary and not balanced** (SPEC §3).
* Balanced ternary (red = −1) makes subtraction free, but BS never subtracts.
* It would clash with the exponent digits, where red must mean *two* (multiply by the base twice): a −1 digit would need the base's inverse, which costs a whole extra exponentiation for a received base.
* It would also make the canonical-form test sign-dependent.
* Plain ternary keeps red as "two clicks" everywhere.

**Why the d12 is exact** (SPEC §4.2). The former wording rolled sea on 1–2, then a heading on 1–3 / 4–6, and "rolled again for this hole" if not even a Destroyer fitted. That is rejection sampling. Sea has weight 1/3 and each heading 1/3 if it has room. After renormalising:
* both headings open: 1/3, 1/3, 1/3 (the d12 thirds);
* one heading open: 1/2, 1/2 (the halves);
* none open: sea.
* The bow is an independent fair bit. On a d12, odd/even splits every third (2 + 2) and every half (3 + 3) evenly, so it is independent of the hole decision.
* Checked exactly, with Fractions: all 25 room states, and whole builds on 2×3, 3×3, 2×5 and 3×4 (64,557 layouts) are identical to the former rule (`../randomizer-kit/`, part B).

**Dice layouts dropped from the spec** (SPEC §4.2; Zachary's decision on #152: one recipe, the row-cup d10s with the keypad rule).
* *One d6 per peg* (formerly the "zero-reroll fallback": 1–2 no peg, 3–4 white, 5–6 red). It is exact, since a d6 splits into thirds, and never needs a re-throw. But it costs one read per hole (100 per grid) instead of one d10 per pair (≈ 55.5 reads with the re-thrown zeros, SPEC §4.7).
* *All-d6 ship decision* (formerly the "all-d6 fallback"): a d6 hole die (1–2 sea, 3–4 across, 5–6 down; with one heading open, 1–3 sea, 4–6 that heading) plus a separate d6 for the bow. The bow needs its own die because a d6's odd/even splits the halves 1–3 / 4–6 two to one. It has the same distribution as the d12 (`../randomizer-kit/` part B; `alld6_check.py` here, which runs the layout of `alld6.py` through the checks of `../ships-pegs/keygrid_check.py`), at one more read per ship.
* *The former d6 wording* (d6 sea roll, heading roll, roll again, d6 bow) is a third way to the same distribution. It is the rule the older scripts simulate (`bump_reroll` in `../ships-pegs/rules.py`, `combined.py`), which is why it stays in the evidence. It is no longer an option.
* All three are exact. They were dropped so the spec has one recipe, not because any of them is wrong. Since dice in the tray now carry no meaning (unread dice are thrown again after a let-go), no layout is needed as a way around a half-used die.

**Why a ternary walk (cube) and not binary (square)** (SPEC §3 B7, the former §4.10).
* Squaring per cell would cost about 1.9× less.
* But with digits {0, 1, 2} in base 2, the cells-to-exponent map is not injective. For example, two red cells in a row equal two white cells one place higher: 2·2ʷ + 2·2^(w−1) = 2^(w+1) + 2ʷ.
* The resulting entropy loss was not measured. So I chose honesty over speed.
* A base-4 walk (square twice) is injective but costs the same as cubing.

**Why not the full check B^q = 1?** (SPEC §5, B8.) It would need a walk over the n-trit public exponent q: about 5,000 multiplications at 3072 bits, about 5× one person's whole exchange (≈ 1,049 multiplications, SPEC §4.7). The square-first variant gives the same protection for honest protocols.

## 6. No-paper audit

Moved here from the No-paper rule of `primitives/key_exchange/bs/SPEC.md` (DHH's #152 review). These are the places where earlier text relied on paper or off-board state, and what each became. Section numbers in the left column are those of the earlier text; the right column points to the current spec.

| Earlier text | Now |
|---|---|
| §1 A1: the fleet could be "marker pieces or a sketch" | The key always sits on its own grid (an ocean grid holding the key's ships and pegs) and is counted per player. |
| §6: idle registers as paper "photographs" | Removed. Every register lives on grids and is counted in the holes. |
| §6: the long toll "could be a printed card" | Removed. The toll is a register on grids (it was already counted). |
| Implicit: loop counters and positions in your head (which key cell you're on, which hole of B, A and the strip you're laying at) | **Cursor ships** plus a **10-hole control lane** (below). |
| Implicit: "pair off the whites" parity and the sub-step of the cell in your head | Pegs in the control lane. |
| §3 B9 and §9: "hash K" and "compare a short hash aloud" | BS now ends with K on the grid; hashing is outside BS. Key confirmation is done physically (§9). |
| Public values as "W/R/. strings" | The other player calls your published register hole by hole and copies it into their own Y register (§3.1). Nothing is stored except pegs. |

## Sources

Paths are relative to this directory.

| Figure | Source |
|---|---|
| Ships + pegs entropy, walk, build, injectivity | `../ships-pegs/combined.py` → `combined_results.txt/.json`; `combined_multi.py` → `combined_multi_results.txt`; SPEC dice: `../ships-pegs/keygrid_check.py` |
| Ships + pegs moves per person | `../exchange/` (full exchanges) and `../reference/tiers.py` |
| Free fleet alone: entropy (exact DP), walk, tiers | `../ships-pegs/build_dp.py`, `brute_build.py`, `viterbi.py`; `costs.py` → `costs_results.json` (here) |
| Free fleet read rule, injectivity | `../ships-pegs/read_rule.py` → `read_rule_results.txt` |
| Uniform-layout ceiling 150.19 bits; standard fleet 34.81 bits | `../ships-pegs/free_fleet_count.py` → `run.log`, `results_exact.json`, `results_mc.json` |
| ECBS Lemma A positions (§4) | `ecbs_lemma_a.py` → `ecbs_lemma_a_results.txt` (here) |
| Themed fleet dice (face rules, full-restart placement) | `themed_kit.py` → `themed_kit_results.json`, `ecbs13_kit.py` → `ecbs13_kit_results.json` (here) |
| Pegs-only and themed tier tables, themed fleet entropy, six-state spike | earlier BS drafts, **not in this tree**: `pegsonly.py`, `tiers.py` (themed), `fleet_entropy.py`, `sixstate.py`, `sixstate_sim.py`; their figures survive only in the former text, #146, commit 9e6b625, `kx-specs/bs/BS.md` |
| Dice rules of the chosen key | [`../randomizer-kit/`](../randomizer-kit/README.md) |
| The dropped all-d6 layout against the exact model | `alld6.py`, `alld6_check.py` → `alld6_check_results.txt/.json` (here) |
