<!-- Owns: the design analysis behind MegaDreifach v3's card phase (ZP26): the v2 baseline, the constraints, every variant tried and why each losing variant was dropped, with numbers and log references. Not normative; the rule is primitives/hash/megadreifach/v3/SPEC.md. Maintenance rules: ../../../../DOCS.md. -->
# MegaDreifach v3 card phase: design analysis

This is the analysis behind [SPEC v3](../../../../primitives/hash/megadreifach/v3/SPEC.md). It is evidence, not a proof of security.

The normative rule is in SPEC v3 §5. **ZP26** (§12.5–§12.7) is that rule. **Every other variant here was rejected and is not part of any spec:**
- NRk52 (§4);
- SBR26 and the other §11 rules;
- the per-card scrambles and the board registers ZB, ZH and ZE (§12);
- ZP13 and ZP0F0E26 (§13).

§11–§13 are the study write-up of 2026-10-01/02. §1–§9 are a condensed summary of the earlier part of the same study. Their numbering is kept, because §11–§13 cite it.

**Where the numbers come from.** Every study figure here was measured with out-of-tree code, and its log in `logs/` is a record of the run, not a result the repo checks. The [README](README.md#out-of-tree-study-code) says why. The only in-tree, reproducible statistics are the ZP26 battery of §12.9, which the harness in `harness/` runs on the sudoc JS build of the v3 sudo.

**Tags.**
- **PROVED**: checked by a named test of the v3 sudo (`primitives/hash/megadreifach/v3/megadreifach.sudo`).
- **ARGUED**: a written argument, not machine-checked.
- **OUT-OF-TREE**: measured with out-of-tree code. Seeded, with n and a 95% CI (Wilson intervals; for 0 hits, the exact one-sided 95% bound). The log is a record, not a repo-checked result.
- **IN-TREE**: measured by `harness/zp26_stats.mjs` on the sudoc JS build; the log's first line is the command that reproduces it (§12.9).
- **HEUR**: a heuristic or an extrapolation.

**Tests.** Write W(h) for the face-turn word a block turns from start h; the block output is h·W·h. The tests look at a quotient of two W's. Ideal is a uniform element of G: P(fix ≥ 2) = .264241, mean fixed pieces 1, mean moved 49.1667, per-slot "fixed with orientation 0" 1/60.

| Test | Start | Quotient |
| --- | --- | --- |
| **D1** (free start, left) | uniform h; g a uniform 2-edge flip | Q = W(h)⁻¹W(gh) |
| **D1′** (free start, right) | same samples | Δ = W(hg)W(h)⁻¹ |
| **D2** (secret start) | uniform h; swap cards 51 and 52 | W⁻¹W″ |
| **D3** (telescoping) | IV or uniform; card pairs at 51/52 | positions equal, output collisions |
| **Merge** | IV or uniform; adjacent swaps at positions 1, 2, 13, 26, 27, 39, 50, 51 | state equal right after the swapped pair, output collisions |

- "exact prediction" means W unchanged (D1) or Δ = id (D1′).
- D1 and D1′ have the same law for conjugacy-invariant statistics (ARGUED, §4.1). Pooling them is HEUR.
- "adv" is the observed rate minus the ideal.

## 1. Baseline: v2 is distinguishable (OUT-OF-TREE)

**What v2 reads** (`logs/mdw_base_coverage.log`; seeds 30,000,000 + 1000·k + chunk; 100,000 blocks per row).
- A C36 = v2 block reads **41.17 of 50 pieces on average** (range 32–50), from uniform h or IV-COOK12.
- The card phase alone reads 32.3.
- Exactly 1 block in 100k read all 50.
- No slot is structurally missed; a missed piece is a random piece.

**Why it matters (ARGUED; v2 SPEC §8).** An unread piece never steers W. Flipping two unread edges of h therefore leaves W unchanged, and the output is predictable exactly.

**v2's free-start distinguisher** (`logs/mdfix_d1prime.log`; 1M pairs; seeds 20,036,000 + chunk):
- exact prediction (Δ = id) **5.18%** [5.14%, 5.23%];
- P(fixE ≥ 2) .3438, adv **+.0796**;
- P(fixC ≥ 2) .3192, adv **+.0550**;
- mean moved 46.36 against 49.17;
- every histogram and cycle-type χ² has p = 0.

So v2's compression is far from a PRF. This is the distinguisher v3 must kill.

## 2. What the constraints force (summary)

The constraints: exactly h·W·h, colour names only, no grips.

1. **DM shape (ARGUED).** If every turn is a face turn of puzzle A chosen from reads of A, then E(h) = W·h and y = h·W·h. A free-start observer learns W = h⁻¹yh⁻¹, as in v2.
2. **Slot reads cannot give coverage.** 52 slot reads see about 32 of 50 pieces. Reads must be **by piece identity**: "find the piece with these colours".
3. **One edge plus one corner per card.** One piece per card cannot cover all 50 (OUT-OF-TREE enumeration, `logs/mdw_naming_enum.log`: at most 44 of 50 over 4 start rules × 2 directions × 210 position sets).
   - The rule that works: on the card's colour face, start at the lowest-ranked neighbour and go clockwise; suit k names the edge toward the k-th neighbour and the corner at its clockwise end.
   - With it, the 48 non-King cards name all 30 edges and all 20 corners (PROVED: sudo test "coverage").
4. **Every read is an injective function of the piece's state (PROVED: sudo test "read words").** Read a named piece by "turn the face carrying its card-coloured sticker +1, then the face now carrying its other named sticker +1". For every piece and every ordered pair of its colours, its 60 states give 60 distinct two-turn words.
5. **A register is needed (OUT-OF-TREE, `logs/mdw_probe_merge.log`; seeds 36,000,000+; 200k trials each).** Without one, colour-named steps commute locally. A swap of cards 51/52 then merges states:

| Card turn | Merge rate |
| --- | --- |
| fixed face | 6.3e-4 |
| register from the deck | 5.0e-5 |
| **register R = the face turned last** | **0** (≤ 1.5e-5) |

   With no grip, a merge in a single pass is a collision.
6. **Fixed-slot blank rounds (the colour analogue of F3) decay slowly in D2** (`logs/mdw_scan_d2.log`): +.022 at 36 rounds. Re-reading by name works much better.

## 4. NRk52, the first finalist (rejected; OUT-OF-TREE)

**The rule.** Card step: turn face (rank + R) mod 12 by +k, or for a King the face opposite R by +k; then the edge pair and the corner pair as in §2.4. R = the face carrying the corner's n-sticker. The deck is dealt **twice**. 520 turns, 676 clicks, 208 finds.

**Results** (`logs/mdw_final_NRk52_{d1,d2,d3,merge}.log`, `logs/mdw_final_NRk52_d1L_rep.log`). Clean on:
- D2 at 1M;
- D3 at 400k;
- merge at 400k;
- 0 exact predictions.

### 4.1 Dedicated 8M run: a real free-start corner bias

The run: `logs/mdw_d1big_NRk52_8M.log`, seeds 38,652,000 + c.
- **D1 + D1′ averaged:** P(fixC ≥ 2) adv **+.00060 ± .00022**; mean fixC +.00168 ± .00049; mean moved −.00152 ± .00045.
- **Histograms:** fixC-hist p = 1.1e-6 (D1) and 5.1e-4 (D1′).
- **Null control:** an 8M control is clean (`logs/mdw_d1big_ctrl_8M.log`).
- **More passes do not help:** a third pass gives +.00061 ± .00043 (`logs/mdw_d1big_NRk104_2M.log`).
- **Where it sits:** about 80% of the excess is on the corners named by the last two cards, so it is an end-of-W effect (`logs/mdw_d1big_diag_NRk52_2M.log`). The second-to-last card's corner shows an excess of +.00137, at z ≈ 7.6.

**D1 and D1′ have the same law (ARGUED).** g ↦ h·g·h⁻¹ is a bijection of the 2-edge flips, and Δ(h, g) = W(h)·Q(h, h·g·h⁻¹)·W(h)⁻¹. The identity was also checked exactly on 20k samples with out-of-tree code (`logs/mdw_d1big_conj.log`).

**Why rejected.** The bias is real. Removing it, and dealing the deck once, led to §11 and §12.

## 5. Properties of the named-pair card step (P1–P5)

For P1, only the naming is PROVED: the sudo test "coverage" checks that this naming (which v3 keeps) covers all 50 pieces; that a pass then reads every named piece is ARGUED. P2 is ARGUED from the sudo-tested read words (§2.4). P3–P5 are ARGUED.

- **P1, coverage.** Each pass reads all 50 pieces (§2.3).
- **P2, every input difference changes the turn sequence.** Common turns preserve the set of pieces whose (slot, orientation) differs between the two runs. That set is non-empty, and each of its pieces is read. At the first such read, the read words differ (§2.4).
- **P3.** Different words may still give the same element of G. That rate is measured as "exact prediction".
- **P4.** Both pieces of a card steer every step.
- **P5, no grip.** Every face is a colour, a count-up, or an opposite.

## 7. Power (normal approximation; `logs/mdfix_power.log`)

The 95% half-width on P(fix ≥ 2) is:
- ±.00086 at 1M;
- ±.00061 at 2M;
- ±.00031 at 8M;
- ±.00016 for the 16M pooled average.

The smallest advantage with 90% power is about 1.65× the half-width. Zero hits in n trials bound the rate by 3/n.

## 8. Cost of the card step

- The suit amounts of a whole deck sum to 130, so the 52 card turns cost 130 clicks.
- Every further turn in a step is 1 click.
- v2 costs 192 turns, 270 clicks, 88 slot reads and 88 re-grips.

## 9. Hand words

As in SPEC v3 §5.1–§5.2:
- colours are ranks (centre ids 0…11, A lowest);
- "count up" is on that 12-cycle;
- "turn X +n" is as in v2.

NRk52's step is SPEC v3 §5.3 steps 1–4, with the new last face being the face of the corner's n-sticker. ZP26 adds step 5.

## 11. One pass of the deck: SBR26, "edge sets the last face, then 26 echoes of the last card" (2026-10-01)

**Goal:** one change to the NRk52 card step that (a) removes the end-of-W corner bias of §4.1 and (b) needs the deck dealt only once. Everything else stays: h·W·h exactly, the unchanged 3-solve, colour names only, no grips, all 50 pieces read every pass, and a last face that can be seen or re-derived.

**Answer:**
- **(a) Fixed (OUT-OF-TREE, 8M).** The single change is a **third piece turn per card**: after the corner, turn the face now carrying the *edge's* n-coloured sticker +1, and make that the last face. No corner is parked on the last face any more.
- **(b) Only with a short tail.** One pass of the 52 cards with nothing after it is impossible: every variant fails D2 by a huge margin (see the next point). The design deals the deck once, then **keeps the 52nd card in hand and plays it 26 more times as an "echo"**, naming pieces by the current last face. No card is dealt a second time.
- **Cost against NRk52.** 468 turns against 520; 546–624 clicks (mean 585) against 676; 156 piece finds against 208.
- **Bias against NRk52.** The corner excess is gone: −0.00018 ± 0.00022 against +0.00060 ± 0.00022 (z ≈ 4.9 for the difference).
- **One caveat.** There is a possible edge residual of +0.00029 ± 0.00022 (2.6σ, not established; edge histograms are clean).

### 11.1 Why one pass alone cannot work

- **Only the last two steps differ (ARGUED).** Swap cards 51 and 52 and steps 1–50 are identical. So W = T·P and W″ = T″·P with a common prefix P, and Q = W⁻¹W″ is a conjugate of T⁻¹T″. That word has at most 4s face turns, where s is the number of turns per step: 20 for A and C, 24 for B, 12 for D.
  - As elements, such words make up at most a 2^-92 to 2^-159 fraction of G (`logs/mdw3_bound.log`).
  - This is not a bound on the conjugacy-invariant statistics, which see only classes. The failure itself is measured, not proved.
- **The measured failure (OUT-OF-TREE; `logs/mdw3_d2scan.log`, 100k pairs each, seeds 40,000,000 + 1000·j).** With no tail, D2 gives:

| Rule (m = 0) | P(fixE ≥ 2) adv | P(fixC ≥ 2) adv | Mean moved − ideal |
| --- | --- | --- | --- |
| A (NRk step, single pass) | +.656 | +.414 | −5.99 |
| B (third turn) | +.614 | +.323 | −4.95 |
| C (sum register) | +.656 | +.419 | −6.09 |
| D (3 turns per card) | +.720 | +.585 | −11.6 |

- **So some steps must follow the last card (OUT-OF-TREE).** No card may be dealt again, so those steps must take their naming from the board. They are the **echoes**.

### 11.2 Candidates

**What every candidate shares:**
- the NRk card turn: face (rank + R) +k; a King turns the face opposite R +k;
- the NRk naming: card colour, suit → edge (r, n_k) and corner (r, n_k, n_k+1).

| Step | Turns per step | Rule after the card turn | Last face R |
| --- | --- | --- | --- |
| A | 5 | NRk: edge pair, corner pair | face of the corner's n-sticker (parks the corner) |
| **B** | **6** | edge pair, corner pair, **then turn the face now carrying the edge's n-sticker +1** | **that face** (the face turned last; the edge, not the corner, sits on it) |
| C | 5 | edge pair, corner pair | (face of edge's n-sticker + face of corner's n-sticker) mod 12 |
| D | 3 | edge: n-sticker face +1; corner: n-sticker face +1 (the suggested "3 turns per card") | sum, as C |

**Tails (no second deal).** After card 52, keep it in hand and play m echoes of it:
- **Echo-F:** the echo names the held card's own edge and corner, the same two pieces every time.
- **Echo-R:** the echo names pieces on **the last face's colour**, with the held card's suit.
- Kind strings are S + step + tail, for example SBR with m = 26.

**Coverage.** The 52 card steps name 30/30 edges and 20/20 corners. So **every block reads all 50 pieces**. The naming coverage is PROVED by the sudo test "coverage" (the naming is NRk's, which v3 keeps); that these rules' blocks read every named piece is ARGUED.

### 11.3 Screen: D2 first, then merge and telescoping (OUT-OF-TREE)

**D2 scan (100k pairs each; `logs/mdw3_d2scan.log`).** Values are P(fixE ≥ 2) adv / P(fixC ≥ 2) adv.

| m | A-F | A-R | B-F | B-R | C-F | C-R | D-F | D-R |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 13 | +.0102 / +.0026 | +.0077 / −.0020 | +.0087 / +.0036 | **+.0022 / +.0023** | +.0059 / +.0016 | +.0073 / +.0007 | +.233 / +.067 | +.059 / +.006 |
| 26 | +.0079 / +.0009 | **−.0006 / −.0007** | +.0062 / −.0008 | **+.0003 / +.0009** | +.0072 / +.0039 | **+.0005 / +.0012** | +.171 / +.059 | +.022 / +.0037 |
| 52 | | | | | | | | +.0126 / +.0013 |

The 95% half-width is ±.0027 at 100k.

- **Echo-F fails (OUT-OF-TREE).** Re-reading the same two pieces leaves an edge excess (fixE-hist p ≤ 1e-7 at m = 26).
- **D fails (OUT-OF-TREE).** The 3-turn step leaves edges unmixed even with 52 echoes (fixE adv +.0126, p = 3e-75). One turn per piece gives 12 read outcomes for 60 states, against 60 two-turn words. **The suggested 3-turns-per-card step does not work.**
- **Survivors:** echo-R tails of 26 with steps A, B or C; and B-R13.

**Survivors at 400k D2, 400k merge, 400k telescoping.** Logs are `logs/mdw3_screen_<kind>_{d2,merge,d3}.log`; seeds are 42M / 43M / 44M + 100,000·j.

| | SAR26 | **SBR26** | SCR26 | SBR13 |
| --- | --- | --- | --- | --- |
| D2 P(fixE ≥ 2) / P(fixC ≥ 2) adv (±.0014) | +.0010 / +.0015 | **−.0007 / +.0003** | +.0009 / −.0002 | +.0017 / −.0013 |
| D2 mean moved − ideal (±.0028) | −.0036 | **−.0010** | −.0011 | −.0028 |
| D2 histogram p (E / C) | .60 / **.021** | .26 / .61 | .45 / .86 | .082 / .59 |
| Merge, 8 positions × IV/uniform × 25k: state equal right after the swapped pair | 1 (IV, position 39) | **0** | 2 | 0 |
| Merge: output collisions | 0 | **0** | **1** (corrected in §12.3; the original log said 0 because of a harness bug) | 0 |
| Merge: mean differing slots IV / uniform (ideal 49.1667) | 49.1684 / 49.1653 | 49.1650 / 49.1673 | 49.1674 / 49.1684 | 49.1637 / 49.1666 |
| D3, 8 cells × 50k: positions equal / collisions | 0 / 0 | **0 / 0** | 0 / 0 | 0 / 0 |

- The 0-hit 95% bounds are 7.5e-6 per merge pair and 6.0e-5 per D3 cell.
- SAR's state merge did not become an output collision, because the register still differed. **Correction (§12.3):** one of SCR26's two merges did become an output collision (uniform start, swap at 39; `logs/mdw3_screen_SCR26_merge_recount.log`, same seeds). The original 0 came from a bug in the out-of-tree harness's merge of chunk results, which dropped collision lists from later chunks. SBR never merged.

### 11.4 D1 + D1′ at 2M and the end-effect diagnostic (OUT-OF-TREE)

**D1 + D1′ at 2M** (`logs/mdw3_big2M_<kind>.log`, seeds 45,000,000 + 100,000·j + chunk). Each cell is the average of D1 and D1′ (HEUR pooling of two same-law samples); the 95% half-width is ±.00043 for P and ±.0009 for moved.

| | SAR26 | SBR26 | SCR26 | SBR13 | NRk52 (8M, §4.1) |
| --- | --- | --- | --- | --- | --- |
| P(fixC ≥ 2) adv, D1 / D1′ | +.00024 / −.00013 | −.00012 / +.00024 | +.00018 / +.00065 | +.00039 / −.00027 | +.00083 / +.00037 |
| P(fixC ≥ 2) adv, average | +.00006 | +.00006 | +.00042 | +.00006 | **+.00060 ± .00022** |
| P(fixE ≥ 2) adv, average | +.00034 | +.00043 | −.00019 | +.00047 | +.00005 |
| mean moved − ideal, average | −.00118 | −.00086 | −.00068 | −.00098 | −.00152 |
| fixC-hist p, D1 / D1′ | .22 / .77 | .56 / .089 | .81 / .07 | .06 / .25 | 1e-6 / 5e-4 |
| exact predictions (D1, D1′) | 0, 0 | 0, 0 | 0, 0 | 0, 0 | 0, 0 |

**End-effect diagnostic** (D1 left, NRk52 method of §4.1; `logs/mdw3_diag2M_SBR26_SCR26.log`, 2M, seeds 46,000,000 + c, the same seeds for both rules). The ideal for "second-to-last" is P(different piece)/60, with P(different piece) measured in the same run.

| | NRk52 (§4.1) | **SBR26** | SCR26 |
| --- | --- | --- | --- |
| extra fully fixed corners of Q (±.0008) | **+.00200** | −.00005 | +.00021 |
| extra fully fixed edges of Q (±.0010) | +.00021 | +.00086 | +.00085 |
| last step's corner coincides, excess (±.00018) | +.00022 | +.00002 | +.00004 |
| second-to-last step's corner, excess (±.00017) | **+.00137** | −.00000 | +.00001 |
| last step's edge, excess | −.00001 | −.00002 | +.00006 |
| second-to-last step's edge, excess | — | +.00015 | −.00003 |
| P(final registers equal) (ideal .08333) | .08341 | .08312 | .08374 |

- **The end-of-W signature is gone in B and C (OUT-OF-TREE).** NRk52's second-to-last corner was z ≈ 7.6; here no last-two piece is off by more than about 0.9σ.
- **The screen at 1M was consistent** (`logs/mdw3_diag_screen_1M.log`, seeds 41,000,000 for all three rules). Extra fully fixed corners: SAR −.0006, SBR +.0001, SCR −.0007 (±.0011).
- **Choosing the finalist.** SBR26 has the cleanest D2, no state merges, a corner average of +.00006 and no end signature. It is also the designer's own suggestion: a third turn sets the last face, so no corner is parked on it.

### 11.5 Finalist SBR26 (OUT-OF-TREE)

**D1 + D1′ at 8M** (`logs/mdw3_final_SBR26_big8M.log`, 8,000,000 samples, fresh seeds 47,000,000 + c, 80 chunks; 53 min).

| Statistic (95% CI) | D1 left | D1′ right | Average (HEUR) | NRk52 average (§4.1) |
| --- | --- | --- | --- | --- |
| exact prediction | 0 (≤ 3.7e-7) | 0 (≤ 3.7e-7) | | |
| **P(fixC ≥ 2)** | .26424 [.26393, .26455], adv **−.00000** | .26389 [.26359, .26420], adv −.00035 | **−.00018 ± .00022** | +.00060 ± .00022 |
| mean fixC − 1 | +.00008 ± .00069 | −.00059 ± .00069 | −.00026 ± .00049 | +.00168 ± .00049 |
| P(fixE ≥ 2) | .26459 [.26428, .26489], adv +.00035 | .26447 [.26416, .26477], adv +.00023 | **+.00029 ± .00022** | +.00005 ± .00022 |
| mean fixE − 1 | +.00059 ± .00069 | +.00072 ± .00069 | +.00066 ± .00049 | −.00005 ± .00049 |
| mean moved − ideal | −.00037 ± .00063 | −.00021 ± .00063 | −.00029 ± .00045 | −.00152 ± .00045 |
| χ² cycle type E / C | p = .65 / .79 | p = .57 / .17 | | |
| χ² fixed histogram E / C | p = .20 / .24 | p = .47 / .29 | | p (C) = 1e-6 / 5e-4 |
| per-slot "fixed, orientation 0", Σz² over 50 slots | 51.4 (p = .42); corners .01657–.01678 | 58.5 (p = .19); corners .01658–.01675 | | 129.3 (p = 6e-9) / 104.3 |
| per-slot "position fixed" (not calibrated, §4.1) | max \|z\| 3.19, Bonferroni p = .072 | Bonferroni p = .21 | | |

The paired D1 − D1′ difference in P(fixC ≥ 2) is +.00035 ± .00043, consistent with the argued equality of the two laws.

- **Corner bias removed (OUT-OF-TREE).** The difference from NRk52 in the averaged P(fixC ≥ 2) is −.00078 ± .00031 (z ≈ 4.9). The difference in mean fixC is −.0019 ± .0007.
  - The per-corner rates are no longer all above 1/60. The fixC histogram and the per-slot Σz² are clean.
  - Mean moved is consistent with ideal, against NRk52's −.0015.
- **Edges, a possible small residual (OUT-OF-TREE, not established).**
  - P(fixE ≥ 2) is +.00029 ± .00022 and mean fixE +.00066 ± .00049, both about 2.6σ.
  - But the edge histograms and edge cycle types are clean (p ≥ .20), and no single last-step edge stands out in the diagnostic.
  - Together with the 2M runs (SBR26 +.00043; SBR13 +.00047, a different tail length), a B-family edge residual of about 3e-4 is plausible (HEUR). At 95% it is ≤ .00051 in P(fixE ≥ 2).
  - It is at most about half of NRk52's corner effect. A 16M run would settle it.
- **D2 at 4M (`logs/mdw3_final_SBR26_d2_4M.log`, seeds 48,000,000 + c; 20 min). Clean.**
  - P(fixE ≥ 2) .2643 [.2639, .2647], adv +.0000; P(fixC ≥ 2) .2643 [.2638, .2647], adv +.0000.
  - Mean fixE 1.0002, fixC 1.0002 (±.0010); mean moved −.0005 ± .0009.
  - Cycle types p = .10 / .41; histograms p = .14 / .91.
- **Merge and telescoping (400k each, §11.3):** 0 state merges and 0 collisions.

**Properties of SBR26** (ARGUED; coverage as in §11.2):
- **(P1) Coverage.** The 52 card steps name, find and read all 50 pieces, so every block reads every piece. Echo reads are extra.
- **(P2) Every input difference changes W.** The card steps use NRk's injective two-turn read words for the edge and the corner, and the third turn is a further read. So the §5 argument applies unchanged: at the first read of a differing piece, the words differ.
- **(P4) Both halves steer every step.** The corner read fixes two turns. The edge read fixes three turns and the next last face, and the corner's turns can move the edge before its third read.
- **(P5) No grip.** Every face is named by colour or by colour arithmetic.
- **D1 and D1′ have the same law** (§4.1).

**Power (normal approximation).**
- The averaged 8M estimate has a 95% half-width of ±.00022 on P(fix ≥ 2). That gives 90% power at |adv| ≥ .00036, and over 99.9% power at NRk52's .0006.
- D2 at 4M: ±.00043, with 90% power at .0007.

### 11.6 Cost (ARGUED counts per block)

| Design | Deck dealt | Card steps + echoes | Turns | Clicks | Piece finds | Face look-ups | Re-grips | Memory |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| v2 (C36) | once | 52 + 36 F3 | 192 | 270 | 88 slot reads | 88 | 88 | grip |
| NRk52 | twice | 104 | 520 | 676 | 208 | 416 | 0 | last face |
| **SBR26** | **once** | **52 + 26 echoes** | **468** | **520 + 26k = 546–624 (mean 585)** | **156** | **390** | **0** | last face, and the held card |
| SBR13 (cheaper; D2 400k marginal, not a finalist) | once | 52 + 13 | 390 | 455 + 13k = 468–507 | 130 | 325 | 0 | same |

- **Clicks.** The 52 cards give 130 card clicks (§8). Each step adds 5 single clicks: 2 edge, 2 corner and the third turn. Each echo turns k clicks, where k is the held card's suit.
- **Against NRk52:** −10% turns, −13% clicks on average, −25% finds, one deal instead of two.
- **Against v2:** still about 2.2× v2's clicks. It is not cheaper than v2.

### 11.7 Hand recipe (SBR26; no grip-relative names)

Names, colours, ranks and "turn X +n" are as in §9. **Last face** = the face you turned last. It starts as the Ace face.

**Card step** (hold the card: rank r, suit amount k):
1. **Turn.** Count up from the last face by the card's rank and turn that face +k. A King turns the face **opposite** the last face +k.
2. **Name.** On the face of the card's colour (a King uses the Ace colour), the suit picks the neighbour n, exactly as in §9. The card's edge is (card colour, n); the card's corner is (card colour, n, the next neighbour clockwise).
3. **Edge.** Find the card's edge. Turn the face its card-coloured sticker is on +1, then the face its n-coloured sticker is now on +1.
4. **Corner.** Find the card's corner. Turn the face its card-coloured sticker is on +1, then the face its n-coloured sticker is now on +1.
5. **Edge again (new).** Look at the card's edge once more. Turn the face its n-coloured sticker is now on +1. **That face is the new last face.**

**Deal once.** Do the card step for all 52 cards. **Keep the 52nd card in your hand.**

**26 echoes.** Count 26 cards off the dealt pile into a counter pile without reading them. Then do one echo per counter card. An echo is the card step with the held card, with one change in steps 2–5: "the card's colour" means **the colour of the last face as it was at the start of this echo**. The suit, and the step-1 turn, come from the held card as usual.

**3-solve.** Unchanged (§9). The output is h·W·h.

**Memory.**
- *During the card pass:* the last face can be read off the board. It is the face carrying the n-coloured sticker of the top dealt card's edge (ARGUED: step 5 turns exactly that face, so the edge stays on it; v3 keeps this card pass, and its sudo test "card pass: the last face is re-derivable from the board and the top dealt card" checks it).
- *During the echoes:* it cannot be re-derived, because the echo's pieces are named by the previous last face. One colour must be carried from one echo to the next. A lapse means restarting the block. This is a small step back from NRk52, whose last face is always re-derivable.
- *Usability (HEUR):* the counter pile and the held card are the only other state, and both are visible.

### 11.8 Verdict and what is not done

- **Recommendation: SBR26.** It beats NRk52 on the corner bias (OUT-OF-TREE, z ≈ 4.9) and on cost (−10% turns, −13% clicks, −25% finds, one deal). It keeps coverage, P2, a clean D2 at 4M, and zero merges and collisions.
- **It does not meet (b) literally.** One bare pass of 52 cards fails D2 for every rule tried, including the 3-turns-per-card rule (OUT-OF-TREE, §11.1). The 26 echoes are the minimum tested that passes. They need no second deal, but they do cost turns.
- **Open:**
  - the possible edge residual (≈ 3e-4, 2.6σ; a 16M D1 + D1′ run takes about 1.8 h);
  - SBR13 at full statistics (390 turns, about 17% fewer than NRk52);
  - a way to re-derive the last face during the echoes;
  - human trials.

**Compute for §11:** about 3.4 h, with one heavy job at a time on 4 workers, with out-of-tree code.

## 12. A state-driven scramble after every card, single pass (2026-10-01)

**Goal.** Drop the second deal, and possibly the SBR third turn of §11, and add instead a short scramble after **every** card. The scramble should:
- be easy to do;
- read the current puzzle state, not the key or the card;
- move everything unpredictably.

The rest is fixed:
- one pass of the 52 cards, then the unchanged 3-solve;
- exactly h·W·h, colour names only, no grips;
- nothing to remember beyond what the board shows. The last face must stay re-derivable from the board, which SBR26's echoes fail (§11.7).

**Answer in short.**
- **A per-card scramble cannot replace the tail (OUT-OF-TREE; ARGUED reason).** Every single-pass design tried, with s = 1 to 6 scramble rounds after every card and nothing after card 52, fails D2 badly: P(fixE ≥ 2) is +0.10 to +0.50 above ideal at 416 to 1092 turns. Scramble-only tails fail too (§12.2).
- **A register read only from the board is collision-broken (OUT-OF-TREE; ARGUED mechanism).** If every quantity is read from the board, a state merge after a swapped pair of cards forces identical futures. The memory-free ZB3F0E26 gives **33 output collisions in 400k adjacent swaps** (§12.3).
- **A register read from a fixed slot biases that slot (OUT-OF-TREE).** The hybrid ZH3F0E26 uses the SBR card pass, with echoes named by the colour in a fixed edge slot.
  - It passes D2 at 400k, merge and telescoping.
  - It fails D1/D1′ at 2M: the register slot's edge is fixed with orientation 0 at .0206 against 1/60 (z = 43), and P(fixE ≥ 2) is +.0028 (z ≈ 9) (§12.4).
- **What works is ZP26: the held card's own pieces set the echo colour (OUT-OF-TREE).**
  - The card pass is SBR26's unchanged. Its last face is the face carrying the n-sticker of the top dealt card's edge, so it is already re-derivable.
  - In the 26 echoes, the echo colour is read off the board from the **held card's own edge and corner**. It is the face carrying the held edge's n-sticker, counted up by the face carrying the held corner's n-sticker.
  - So before every card step and every echo, everything needed comes from the board, the held card, the top dealt card and the counter pile. **Nothing is carried from one step to the next.**
  - Results:
    - D1 + D1′ at 2 × 8M on fresh seeds (pooled 16M per side): P(fixC ≥ 2) −.00004 ± .00016 and P(fixE ≥ 2) −.00005 ± .00016. The corner bias of NRk52 is gone, and the edge question left open by SBR26 does not show.
    - D2: 4M clean.
    - Merge and telescoping (400k each): 0 merges, 0 collisions.
    - All 50 pieces read in every block (PROVED: sudo test "coverage").
- **What it is not.** ZP26 is not a per-card scramble, and it keeps the SBR third turn. The no-third-turn versions of the board-register designs (ZB0F0E26, ZH0F0E26) failed the D2 scan on edges (+.0091, +.0099). ZP without the third turn was not tried.
- **Cost.** 468 turns and 546–624 clicks (mean 585), the same as SBR26, plus 52 register looks: the held edge and the held corner, once per echo. That is 156 piece finds + 52 looks.

### 12.1 Variants (kind = Z + register + third turn + slot + s + tail)

**What every variant shares.** The NRk card turn and naming of §11.2; the SB third turn when "3" (§11.7 step 5).

**Scramble round (state-driven).** Look at the piece in a colour-defined slot and turn, in order, the faces of the colours it shows on that slot's faces, each +1.
- Odd rounds use the corner at (Ace, 2, 3)-faces, i.e. the Ace face, its lowest-ranked neighbour and the next one clockwise: 3 turns.
- Even rounds use the edge at (Ace, 2)-faces: 2 turns.
- Slot "F" keeps these slots fixed. Slot "R" builds the same slots on the face of the board colour B instead of the Ace face.

**Registers** (the colour that step 1 counts up from, and that names the echo pieces).

| Code | Card steps | Echoes | Re-derivable? |
| --- | --- | --- | --- |
| B (board) | B = the colour on the Ace face of the edge in slot (Ace, 2), read before every step | same | yes, fully memory-free |
| H (hybrid) | last face L, as in SBR | B | yes |
| E (held edge) | L | face carrying the held card's edge's n-sticker | yes |
| **P (held pair)** | **L** | **(face of held edge's n-sticker + face of held corner's n-sticker) mod 12** | **yes** |
| L (comparison) | L | L (= SBR echo-R) | no (§11.7) |

**Tails.** N = none; E = m echoes of the held 52nd card (§11.7), named by the register; S = m further scramble rounds.

**Notes.**
- ZL3F0E26 is SBR26.
- B is uniform: each colour shows up 5 times over the 60 states of its slot (OUT-OF-TREE enumeration, printed in the logs).
- The 48 non-King card steps name 30/30 edges and 20/20 corners, so **every block reads all 50 pieces**. The naming coverage is PROVED by the sudo test "coverage" (the naming is NRk's); that these variants' blocks read every named piece is ARGUED.

### 12.2 Per-card scrambles, single pass: all fail D2 (OUT-OF-TREE; `logs/mdw4_d2scan_pass.log`, 100k pairs each, seeds 40,000,000 + 1000·j + chunk)

| Kind (no tail) | Rounds/card | Turns | P(fixE ≥ 2) adv | P(fixC ≥ 2) adv | mean moved − ideal |
| --- | --- | --- | --- | --- | --- |
| ZB0F1N | 1 | 416 | +.502 | +.269 | −2.41 |
| ZB0F2N | 2 | 520 | +.398 | +.157 | −1.34 |
| ZB0F3N | 3 | 676 | +.276 | +.096 | −0.82 |
| ZB3F2N (third turn) | 2 | 572 | +.341 | +.111 | −1.05 |
| ZB3F3N | 3 | 728 | +.231 | +.071 | −0.66 |
| ZB3R3N (relative slots) | 3 | 728 | +.214 | +.048 | −0.45 |
| ZB0F6N | 6 | 1040 | +.152 | +.050 | −0.53 |
| ZB3R6N | 6 | 1092 | +.096 | +.015 | −0.21 |

The 95% half-width is ±.0027. All histogram and cycle-type p-values are below 1e-12.

- **Why (ARGUED, as §11.1).** Swap cards 51 and 52 and everything up to step 50 is the same. So D2's quotient W⁻¹W″ is a conjugate of a word made only of the last two steps and their scrambles, T⁻¹T″. Each step has at most 6 + 3s turns, so the word has at most 4·(6 + 3s).
  - A **fixed** scramble cancels out of W⁻¹W″ entirely (ARGUED).
  - A **state-driven** one adds only O(s) more turns to this short word.
  - Mixing improves with s (the table above), but far too slowly: even 6 rounds after every card (1092 turns, twice NRk52) leave +.096.
- **Scramble-only tails fail as well** (`logs/mdw4_d2scan_memfree.log`, seeds 50,000,000 + 1000·j): 40 rounds after the last card give +.112 (ZB3R0S40) and +.203 (ZB3F0S40). A colour-slot scramble is a poor mixer: it reads one piece in a fixed region and turns that piece's own faces.
- **Scramble plus echoes does not help either.** ZB3F1E13 (one round per card plus 13 echoes, 585 turns) fails corners at +.0090 (fixC-hist p = 3.5e-12).

### 12.3 Memory-free registers: merge means collision (ARGUED mechanism; OUT-OF-TREE rate)

**Why a fully memory-free design is exposed (ARGUED).**
- If every rule reads only the board, the held card and the counter, then the rest of the block is a function of (board, remaining cards).
- So if a swapped pair of adjacent cards leaves the same board right after the pair, the two outputs are identical: a **collision**.
- The only exception is a swap at 51/52, because there the held card differs.
- The last-face register is what blocked this in NRk and SB. It carries state that the board does not show.

**Measured.**

| Run | Log | Result |
| --- | --- | --- |
| D2 scan, ZB3F0E26 | `logs/mdw4_d2scan_memfree.log` | passes: +.0005 / +.0011 |
| D2 at 400k, ZB3F0E26 | `logs/mdw4_screen_ZB3F0E26_d2.log`, seed 51,000,000 | +.0018 / −.0003 |
| Merge search, ZB3F0E26 | `logs/mdw4_screen_ZB3F0E26_merge.log`, 8 positions × IV/uniform × 25k, seeds 51,100,000 | **37 state merges and 33 output collisions in 400k adjacent swaps (8.3e-5 per pair)** |
| Telescoping, ZB3F0E26 | `logs/mdw4_screen_ZB3F0E26_d3.log` | card-phase positions equal up to 13 per 50k cell; output collisions 0 (the held card differs) |

**Not viable.** The other memory-free tails (ZB0F0E26, ZB3F0E13, ZB0F0E13) already fail D2 on edges: +.0091, +.0058, +.0207, with fixE-hist p from 2e-4 down to 2.5e-84.

**A harness bug found on the way (fixed before the later runs).** The out-of-tree harness merged the per-chunk collision lists as a numeric vector of the first chunk's length. Collisions from later chunks were therefore dropped, or the job crashed: that is what `logs/mdw4_screen_ZB3F0E26_merge2M.log` records.
- The differing-slots histogram was always right.
- Every old merge log shows bin [0–40] = .00000 (NRk52, NRr52, SAR26, SBR26, SBR13), so those zero-collision claims stand.
- **SCR26's does not.** The recount on the same seeds (`logs/mdw3_screen_SCR26_merge_recount.log`) finds **1 output collision** in 400k (uniform start, swap at 39). §11.3 is corrected.

### 12.4 Board register in the echoes only (ZH): passes the screen, fails D1 (OUT-OF-TREE)

**ZH3F0E26** uses the SBR card pass, then 26 echoes in which B (the colour on the Ace face of the edge between the Ace and 2 faces) names the pieces and sets the step-1 count. It is fully re-derivable.

| Test | Log | Result |
| --- | --- | --- |
| D2 scan, 100k | `logs/mdw4_d2scan_hybrid.log`, seeds 55,000,000 + 1000·j | +.0028 / −.0004 |
| D2, 400k | `logs/mdw4_screen_ZH3F0E26_d2.log`, seed 56,000,000 | +.0003 / −.0002, histogram p .20 / .98 |
| Merge | `logs/mdw4_screen_ZH3F0E26_merge.log` | 1 state merge, 0 collisions |
| Telescoping | `logs/mdw4_screen_ZH3F0E26_d3.log` | 1 / 0 |
| **D1 + D1′, 2M** | `logs/mdw4_screen_ZH3F0E26_big2M.log`, seeds 57,000,000 + c | **P(fixE ≥ 2) +.00280 / +.00265 (±.00061); fixE-hist p = 2e-18 / 2e-20** |

- **Where the D1 excess sits.** In D1′, edge slot 20, the register slot itself, is "fixed, orientation 0" at .0206 against .01667 (z = 43). In D1, the maximum is |z| = 4.7 at slot 39. Corners are clean (+.0000 / +.0001).
- **End diagnostic** (`logs/mdw4_diag2M_ZH3F0E26.log`, seeds 58,000,000).
  - Fully fixed edges of Q: +.0062 ± .0010.
  - Final registers equal: .0934 against .0833.
  - Second-to-last echo names a different piece only 30% of the time.
  - So the register is sticky: the slot is untouched in about (10/12)^6 ≈ 1/3 of echoes (HEUR).
- **Reading (HEUR).** A slot read depends on *which piece sits in a place*. The card steps use piece reads, which depend on *where a named piece is*. The slot read breaks that symmetry, and D1 sees it.
- Its 8M runs were cancelled after the 2M result.
- The **held-edge** register ZE3F0E26 (piece read, one piece) is also suspect at 400k (`logs/mdw4_screen_ZE3F0E26_big400k.log`, seeds 63,000,000).
  - P(fixE ≥ 2) is +.00234 / +.00160 (±.00137), with fixE-hist p = .004 / .003.
  - Dropped.

### 12.5 Finalist ZP26: echo colour from the held card's edge and corner (OUT-OF-TREE)

**Screen.**

| Test | Log, seeds | Result |
| --- | --- | --- |
| D2 scan, 100k | `logs/mdw4_d2scan_piece.log`, 62,000,000 + 1000·j | +.0022 / −.0010 |
| D2, 400k | `logs/mdw4_screen_ZP3F0E26_d2.log`, 65,000,000 | +.0002 / +.0009; histogram p .81 / .26 |
| Merge, 400k | `logs/mdw4_screen_ZP3F0E26_merge.log`, 65,100,000 | **0 state merges, 0 collisions**; mean differing slots 49.1667 / 49.1673 (ideal 49.1667) |
| Telescoping, 8 × 50k | `logs/mdw4_screen_ZP3F0E26_d3.log`, 65,200,000 | 0 / 0 |
| D1 + D1′, 400k | `logs/mdw4_screen_ZP3F0E26_big400k.log`, 64,000,000 | E +.00043 / −.00046, C +.00025 / +.00016 |
| D1 + D1′, 2M | `logs/mdw4_screen_ZP3F0E26_big2M.log`, 66,000,000 + c | E +.00003 / +.00018, C +.00038 / +.00045 (±.00061 each); all histograms p ≥ .086; per-slot Σz² p .80 / .39 |

The 0-hit bounds are 7.5e-6 per merge pair and 6.0e-5 per telescoping cell.

**End-effect diagnostic** (`logs/mdw4_diag2M_ZP3F0E26.log`, 2M, seeds 67,000,000; the "last step" is the last echo).

| Quantity | Excess |
| --- | --- |
| Last echo's corner coincides | +.00008 (±.00018) |
| Last echo's edge coincides | −.00010 |
| Second-to-last echo's corner | +.00005 |
| Second-to-last echo's edge | +.00004 |
| Final registers equal | .08329 (ideal .08333) |
| Fully fixed edges of Q | +.00029 ± .00098 |
| **Fully fixed corners of Q** | **+.00101 ± .00080 (2.5σ)** |

- There is **no end-of-W signature**, which was NRk52's.
- The corner figure is a 2.5σ flag at 2M. It was never directly re-measured. The next block looks at it only indirectly, through mean fixC and the per-corner "fixed, orientation 0" rates at 8M.
- P(different piece) between the last two echoes is .61, against SBR26's .89. So the register repeats more often than SBR's but less than ZH's (HEUR).

**D1 + D1′ at 8M + 8M** (`logs/mdw4_final_ZP3F0E26_big8M.log`, seeds 68,000,000 + c; `logs/mdw4_final_ZP3F0E26_big8M_b.log`, seeds 71,000,000 + c; 80 chunks each, about 56 min each).

| Statistic (95% CI) | run a D1 | run a D1′ | run b D1 | run b D1′ | **Pooled average of 4, 16M per side (HEUR pooling)** | SBR26 8M avg (§11.5) | NRk52 8M avg (§4.1) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| exact prediction | 0 (≤ 3.7e-7) | 0 | 0 | 0 | 0 in 32M quotients | 0 | 0 |
| **P(fixC ≥ 2) adv** (±.00031 each) | +.00015 | −.00018 | +.00003 | −.00014 | **−.00004 ± .00016** | −.00018 ± .00022 | +.00060 ± .00022 |
| **P(fixE ≥ 2) adv** (±.00031 each) | +.00032 | −.00009 | −.00005 | −.00036 | **−.00005 ± .00016** | +.00029 ± .00022 | +.00005 ± .00022 |
| mean fixC − 1 (±.00069 each) | +.00000 | −.00003 | +.00032 | −.00005 | +.00006 ± .00035 | −.00026 ± .00049 | +.00168 ± .00049 |
| mean fixE − 1 (±.00069 each) | +.00090 | −.00011 | −.00040 | −.00080 | −.00000 ± .00035 | +.00066 ± .00049 | −.00005 ± .00049 |
| mean moved − ideal (±.00063 each) | −.00035 | −.00002 | +.00009 | +.00052 | +.00006 ± .00032 | −.00029 ± .00045 | −.00152 ± .00045 |
| χ² cycle type E / C, p | .35 / .057 | .28 / .82 | .50 / .34 | .49 / .59 | | | |
| χ² fixed histogram E / C, p | .12 / .44 | .33 / .37 | .36 / .43 | .082 / .77 | | | |
| per-slot 'fixed, orientation 0' Σz² p; corner range | .65; .01660–.01675 | .20; .01658–.01679 | .97; .01660–.01673 | .18; .01655–.01674 | | | |
| per-slot 'position fixed' (not calibrated, §4.1), Bonferroni p | .042 | .0055 (corner slot 11) | 1 | .48 | | | |

- Paired D1 − D1′ difference in P(fixC ≥ 2): run a +.00033 ± .00043, run b +.00017 ± .00043. Both are consistent with the argued equality of the two laws.
- **Corners: clean (OUT-OF-TREE).** The pooled averaged P(fixC ≥ 2) is −.00004 ± .00016, and the difference from NRk52 is −.00064 ± .00027 (z ≈ 4.6). All per-corner "fixed, orientation 0" rates lie within ±.00012 of 1/60, with Σz² clean in all four.
  - **The diag 2.5σ flag was never directly re-measured (HEUR).** The 2M diag's "fully fixed corners +.00101 ± .00080" (D1) is the sum over the 20 corners of the per-corner "fixed, orientation 0" rates.
    - The 8M runs do not print that sum. They print the per-corner rates and their Σz².
    - A uniform +.00101 spread over 20 corners is +5e-5 per corner, about 1.1σ per slot at 8M. That would add roughly 24 to the corner part of Σz².
    - The observed totals over all 50 slots in D1 are 45.5 and 33.2 (ideal 50).
    - So the 8M runs make an excess that large unlikely (HEUR), but the flag itself was never directly re-measured.
  - The run-a D1′ "position fixed" Bonferroni p = .0055 is the uncalibrated statistic of §4.1 (slots are not independent). Run b gives p = .48 for the same statistic. Not a finding (HEUR).
- **Edges: settled for ZP26 (OUT-OF-TREE).** The pooled P(fixE ≥ 2) is −.00005 ± .00016 (95% upper bound +.00011), and mean fixE −.00000 ± .00035. SBR26's 2.6σ edge hint (+.00029) does not appear in this design, which shares SBR26's card pass. That suggests, but does not prove, that it was noise or specific to SBR's remembered-colour echo (HEUR).

**D2 at 4M** (`logs/mdw4_final_ZP3F0E26_d2_4M.log`, seeds 69,000,000 + c; 21 min). **Clean.**
- P(fixE ≥ 2) .2642 [.2637, .2646], adv −.0001; P(fixC ≥ 2) .2645 [.2641, .2650], adv +.0003.
- Mean fixE 1.0002, fixC 1.0007 (±.0010); mean moved −.0011 ± .0009.
- Cycle types p = .19 / .68; histograms p = .29 / .65.

**Cheaper sibling ZP13** (390 turns; screen only, not a finalist).
- D2 400k (`logs/mdw4_screen_ZP3F0E13_d2.log`, seed 70,000,000): +.0004 / +.0011, histogram p .051 / .023 (marginal).
- D1 + D1′ 400k (`logs/mdw4_screen_ZP3F0E13_big400k.log`, 70,500,000): E +.00095 / −.00006, C +.00087 / +.00025 (±.00137), histograms clean.
- It would need full statistics before use.

**Properties of ZP26.**
- **(P1) Coverage (PROVED: sudo test "coverage").** The card pass is SBR26's, so all 50 pieces are named, found and read in every block. Echo reads are extra.
- **(P2, P4, P5) (ARGUED)** hold as for SBR26 (§11.5): same card-pass words, both halves steer every step, no grip. The read words P2 rests on are PROVED (sudo test "read words").
- **Re-derivability.**
  - During the card pass, the last face is the face carrying the n-sticker of the top dealt card's edge (PROVED: sudo test "card pass: the last face is re-derivable from the board and the top dealt card").
  - At the start of every echo, the echo colour is a function of the board and the held card alone (ARGUED: the sudo's `echo_colour` takes only those two).
  - So between any two steps, the whole state needed is visible: board, dealt pile, held card, counter pile.
  - Within one echo, the echo colour must be held from the look until the echo's edge and corner have been found. Those carry that colour as a sticker, so it is a few seconds.
- **D1 and D1′ have the same law** (ARGUED, §4.1).

**Power (normal approximation).**
- Averaged D1 + D1′ at 16M: 95% half-width ±.00016 on P(fix ≥ 2). That gives 90% power at |adv| ≥ .00026; at 8M alone, .00036.
- D2 at 4M: ±.00043, with 90% power at .0007.

### 12.6 Cost per block (ZP26: PROVED by the sudo test "cost per block"; the other rows: ARGUED counts)

| Design | Deck dealt | Steps | Turns | Clicks | Piece finds | Re-grips | Carried between steps |
| --- | --- | --- | --- | --- | --- | --- | --- |
| v2 (C36) | once | 52 + 36 | 192 | 270 | 88 slot reads | 88 | grip |
| NRk52 | twice | 104 | 520 | 676 | 208 | 0 | nothing (last face re-derivable) |
| SBR26 | once | 52 + 26 echoes | 468 | 546–624 (mean 585) | 156 | 0 | **one colour across all 26 echoes** |
| **ZP26** | **once** | **52 + 26 echoes** | **468** | **546–624 (mean 585)** | **156 + 78 re-looks + 52 register looks** | **0** | **nothing** |
| ZB0F1N (per-card scramble, fails) | once | 52 | 416 | 494 | 104 + 104 slot reads | 0 | nothing |
| ZB3R6N (best per-card scramble, fails) | once | 52 | 1092 | 1170 | 104 + 676 slot reads | 0 | nothing |

- **Clicks.** 130 card clicks + 5·52 + 6·26 single clicks, which is 520 + 26k for the held card's suit k. This is the same as SBR26.
- **Register looks.** Each echo first looks at the held card's edge and corner (2 looks), then finds the echo's own edge and corner (2 finds, the "156").
- **Against SBR26:** the same turns and clicks, plus 52 looks. In exchange, nothing has to be carried.
- **Against NRk52:** −10% turns, −13% clicks, the same number of looks in total (156 + 52 = 208), and one deal instead of two.
- **Against v2:** still about 2.2× v2's clicks.
- **Counting conventions (2026-10-02 note).**
  - "156 piece finds" counts the edge and corner located in steps 3 and 4 of each of the 78 steps.
  - Step 5 also looks again at the edge found in step 3. That adds 78 re-looks. The ZP26 row includes them; the other rows and the logs' cost line leave them out (SBR26 has the same 78).
  - The logs' cost line prints `slot_reads 26`: one register read per echo, which looks at two pieces. That is the same 52 register looks.
  - The v3 sudo counts all three (156 / 78 / 52) in `em_run` and tests them (SPEC v3 §5.6).

### 12.7 Hand recipe (ZP26)

The ZP26 hand recipe is SPEC v3 §5.1–§5.4, and the normative definition is the v3 sudo. It is not restated here. In the logs, ZP26 is kind `ZP3F0E` with m = 26.

### 12.8 Verdict and what is not done

- **The idea as posed (a state-driven scramble after every card instead of a tail or second deal) does not work.**
  - OUT-OF-TREE: 8 variants, up to 6 rounds per card, all fail D2 by +.10 or more.
  - ARGUED reason: a last-two swap only changes a short end word.
  - Fully board-read registers fail differently: merges become collisions (33 in 400k), or fixed-slot reads bias that slot.
- **But the goal behind it (nothing to remember, one deal) is met by ZP26.** It makes SBR26's echoes re-derivable at no extra turns or clicks.
  - Results: corners −.00004 ± .00016 and edges −.00005 ± .00016 (pooled 16M), against NRk52's corner +.00060 ± .00022; 0 exact predictions in 32M quotients.
  - D2 4M is clean; merge and telescoping show 0 / 0; all 50 pieces are read.
- **Recommendation: ZP26 replaces SBR26** as the single-pass design.
- **Open:**
  - ZP13 at full statistics;
  - whether SBR26's own +.00029 edge hint was noise (moot if ZP26 is adopted);
  - human trials;
  - the cost is still about 2.2× v2.

**Compute for §12:** about 5.0 h, one heavy job at a time on 4 workers, with out-of-tree code. The ZB and ZH chains were stopped early (§12.3, §12.4).

### 12.9 In-tree battery on the sudoc build (IN-TREE)

The OUT-OF-TREE figures above cannot be re-run in the repo at their sizes yet (README, "Out-of-tree study code"). This is a smaller ZP26 battery, run by [`harness/zp26_stats.mjs`](harness/zp26_stats.mjs) on the sudoc JS build of the v3 sudo. The first line of each log is the command that reproduces it. Same tests as §12.5; merge and D3 count output collisions only.

| Test (ZP26, IN-TREE) | Log, seeds | Result (±: 95% half-width) |
| --- | --- | --- |
| D2, 100k | `logs/intree/zp26_d2_100k.log`, 80,000,000 + c | P(fixE ≥ 2) / P(fixC ≥ 2) adv **+.00015 / −.00103** (±.0027); mean moved −.0021 ± .0057; histogram p .44 / .79; cycle type p .45 / .062 |
| D1 + D1′, 50k (same samples) | `logs/intree/zp26_d1_50k.log`, 81,000,000 + c | D1: E +.00190, C −.00228; D1′: E +.00256, C +.00208 (±.0039 each); histogram p ≥ .47; cycle type p ≥ .48; **0 exact predictions in 100k quotients** (≤ 6.0e-5 per side) |
| Merge, 8 positions × IV/uniform × 4,000 | `logs/intree/zp26_merge_64k.log`, 82,000,000 + … | **0 output collisions in 64k adjacent swaps** (≤ 4.7e-5 per pair); mean differing slots IV / uniform in line with 49.1667 |
| D3, 4 pair classes × IV/uniform × 8,000 | `logs/intree/zp26_d3_64k.log`, 83,000,000 + … | **0 output collisions in 64k** (≤ 3.7e-4 per cell) |

- Everything is within its 95% interval; there is nothing to follow up at these sizes.
- Power: D2 at 100k has 90% power at about |adv| ≥ .0044, and D1 + D1′ at 50k at about .0064 per side. So it shows only that there is no large defect (|adv| above about .004 to .006). It would not have caught ZP13's +.0019 D2 failure or NRk52's +.0006 corner bias.
- Compute: about 29 min (D2 574 s, merge 342 s, D3 354 s, D1 464 s), at 320–370 blocks/s.
- A fixed-seed slice of all four tests (`logs/intree/zp26_ci_slice.log`) is re-run and compared in `tools/generate-demos.sh`.

## 13. Three single-pass options side by side: ZP26, ZP13, ZP26 without the third turn (2026-10-02)

**Goal.** Test all three side by side.
- **(1) ZP26:** the §12 finalist. Its logs are reused; nothing was rerun.
- **(2) ZP13:** ZP26 with 13 echoes instead of 26.
- **(3) ZP0-26 (kind `ZP0F0E`, m = 26):** ZP26 without the SBR third turn (§11.7 step 5), in both the card pass and the echoes.
  - Each step is the NRk 5-turn step (§9 steps 1–4).
  - The card-pass last face is the face carrying the n-sticker of the card's corner.
  - The echoes use the same ZP register: X = face of the held edge's n-sticker, Y = face of the held corner's n-sticker, and P = X counted up by Y's rank.

**The battery.** Each variant was to get the same battery as ZP26:
- screen: D2 400k, merge 400k, telescoping 400k;
- D2 at 4M;
- D1 + D1′ at 2 × 8M (fresh seeds);
- the end diagnostic at 2M.

The rule was to stop a variant that clearly fails.

**Result.**
- **Only ZP26 passes.**
- **ZP13 fails D2 at 4M on edges, decisively** (z ≈ 9; fixE-hist p = 7.7e-25).
- **ZP0-26 fails D2 on edges in two independent 4M runs.** The pooled 8M result is P(fixE ≥ 2) +.0008 ± .0003, with fixE-hist p = .0043 and 2.2e-6.
- Per the stop rule, neither got its 8M D1 runs. Each got one 2M D1 + D1′ run for the table instead.

### 13.1 Side-by-side (OUT-OF-TREE unless tagged)

**Cost per block** (ZP26: PROVED by the sudo test "cost per block"; ZP13 and ZP0-26: ARGUED counts).

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 (no third turn) | ref.: v2 / NRk52 / SBR26 |
| --- | --- | --- | --- | --- |
| Turns | **468** | 390 | 390 | 192 / 520 / 468 |
| Clicks (k = held suit) | 520 + 26k = 546–624, mean 585 | 455 + 13k = 468–507, mean 488 | 442 + 26k = 468–546, mean 507 | 270 / 676 / ~585 |
| Piece finds + register looks | 156 + 52 | 130 + 26 | 156 + 52 | 88 slot reads / 208 / 156 |
| Deals; carried between steps | once; nothing | once; nothing | once; nothing | — / twice, nothing / once, one colour |

**Merges and telescoping (400k each).**

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 |
| --- | --- | --- | --- |
| State merges / output collisions | 0 / 0 | 0 / 0 | 0 / 0 |
| Telescoping: positions equal / collisions | 0 / 0 | 0 / 0 | 0 / 0 |
| Seeds | 65.1M / 65.2M | 72.1M / 72.2M | 80.1M / 80.2M |

**D2, P(fixE ≥ 2) / P(fixC ≥ 2) advantage.**

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 |
| --- | --- | --- | --- |
| Screen, 400k (±.0014) | +.0002 / +.0009; histogram p .81 / .26 | +.0004 / +.0011; p .051 / .023 | +.0009 / +.0005; p .27 / .94 |
| **4M (±.00043)** | **−.0001 / +.0003**; histogram p .29 / .65; cycle type .19 / .68 | **+.0019 / −.0001**; fixE-hist p **7.7e-25**; mean fixE +.0055 ± .0010; moved −.0026 ± .0009 | **+.0006 / +.0000**; fixE-hist p **.0043**; cycle type E p .0022; mean fixE +.0018; moved −.0014 ± .0009 |
| 4M replicate (±.00043) | — | — | **+.0010 / +.0000**; fixE-hist p **2.2e-6**; mean fixE +.0028 ± .0010; moved −.0015 |
| Pooled (HEUR) | | | 8M: fixE adv **+.0008 ± .0003**, mean fixE +.0023 ± .0007 |

**D1 + D1′, P(fixC ≥ 2) / P(fixE ≥ 2) advantage averaged over the two sides (HEUR pooling).**

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 |
| --- | --- | --- | --- |
| Size | **16M per side** (2 × 8M) | 2M per side | 2M per side |
| Corners | **−.00004 ± .00016** | +.00021 ± .00043 | +.00013 ± .00043 |
| Edges | **−.00005 ± .00016** | +.00002 ± .00043 | +.00015 ± .00043 |
| Histograms and per-slot Σz² | all clean | all clean (p ≥ .37; Σz² p .83 / .43) | all clean (p ≥ .14; Σz² p .86 / .57) |
| Exact predictions | 0 in 32M | 0 in 4M | 0 in 4M |

**End diagnostic, 2M.**

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 |
| --- | --- | --- | --- |
| Last / second-to-last corner excess (±.00018) | +.00008 / +.00005 | not run (cancelled) | +.00022 / −.00014 |
| Last / second-to-last edge excess | −.00010 / +.00004 | | +.00014 / +.00005 |
| Fully fixed corners / edges of Q | +.00101 ± .00080 / +.00029 ± .00098 | | +.00050 ± .00080 / −.00012 ± .00098 |
| Final registers equal (ideal .08333) | .08329 | | .08384 |

**Verdict.**

| | **(1) ZP26** | (2) ZP13 | (3) ZP0-26 |
| --- | --- | --- | --- |
| Verdict | **passes everything; recommended** | **fails D2 (edges), decisively** | **fails D2 (edges), replicated; D1 and diag clean** |

**Logs.**
- **ZP26:** §12.5 (`logs/mdw4_screen_ZP3F0E26_*`, `logs/mdw4_final_ZP3F0E26_{big8M,big8M_b,d2_4M}.log`, `logs/mdw4_diag2M_ZP3F0E26.log`).
- **ZP13:** `logs/mdw4_screen_ZP3F0E13_d2.log`, `logs/mdw5_screen_ZP3F0E13_{merge,d3,big2M}.log`, `logs/mdw5_final_ZP3F0E13_d2_4M.log` (seeds 70M, 72.1M, 72.2M, 74M, 73M).
- **ZP0-26:** `logs/mdw5_screen_ZP0F0E26_{d2,merge,d3,big2M}.log`, `logs/mdw5_final_ZP0F0E26_d2_4M.log`, `logs/mdw5_final_ZP0F0E26_d2_4M_rep.log`, `logs/mdw5_diag2M_ZP0F0E26.log` (seeds 80M, 80.1M, 80.2M, 82M, 81M, 85M, 84M).

### 13.2 Reading

- **Edges are the weak spot of both cheaper options (OUT-OF-TREE).** They are the same failure mode seen throughout §11–12: B-F, D, ZB0/ZH0, and the edge hints in SBR13 and ZP13's own screen.
  - **ZP13: 13 echoes are not enough** to mix the edges after the last cards. A 400k screen (±.0014) could not see an excess of +.0019 with only modest histogram p-values. 4M can.
  - **ZP0-26: removing the third turn** removes the extra edge read in every step and echo. A residual of about +.0008 in P(fixE ≥ 2) survives 26 echoes.
    - It replicates across two independent 4M runs: z ≈ 2.7 and 4.6, pooled z ≈ 5.
    - The corners are clean.
  - Why the third turn matters (HEUR): it is the only turn steered by the edge *after* the corner's turns. Without it, the edge read words have only 12 outcomes per step against 60 edge states, as in §11.3's analysis of D.
- **No register or collision problem in any of the three (OUT-OF-TREE).** Merge and telescoping give 0 / 0 at 400k each (0-hit 95% bound 7.5e-6 per pair, 6.0e-5 per cell).
- **No end-of-W signature where measured (OUT-OF-TREE).** In ZP26 and ZP0-26, the last-two-card excesses are all within ±.00022, about the 95% half-width of ±.00018 per item allowing for multiplicity (HEUR). ZP13's diag was cancelled after its D2 failure.
- **D1 does not see the cheaper options' defect (OUT-OF-TREE, 2M).** Both are clean on D1 + D1′ at 2M. The defect is in D2's last-two-card swap, which is sensitive to how well the tail mixes the end of the card pass.
- **Coverage.** The card pass naming is NRk's, so every block reads all 50 pieces. The naming coverage is PROVED by the sudo test "coverage" (all three use it). That every block reads all 50 pieces is checked by the sudo for ZP26 only, through `em_run`'s finds; for ZP13 and ZP0-26 it is ARGUED.
- **Last face readable from the board** (PROVED for ZP26 by the sudo test; ARGUED for ZP13 and ZP0-26).
  - In the card pass, it is the face carrying the n-sticker of the top dealt card's edge (ZP26, ZP13) or corner (ZP0-26, as in §9).
  - In the echoes, P is re-read from the held card's edge and corner before every echo.

### 13.3 Recommendation

- **Keep ZP26 (§12.7 hand recipe).** It is the only one of the three that passes the full battery:
  - 16M D1 + D1′ clean on corners and edges;
  - D2 4M clean;
  - 0 merges and collisions;
  - no end signature.
- **The cheaper options save 78 turns (−17%) but cost hash quality.** The saving is about 98 clicks for ZP13 and 78 for ZP0-26. Each shows an edge excess in D2 of 1e-3 to 2e-3 (for ZP0-26 in two independent 4M runs; OUT-OF-TREE) in P(fixE ≥ 2): 3–8× the 95% half-width at 4M. Neither is recommended.
- **If a cheaper single pass is wanted later (HEUR):** something between 13 and 26 echoes with the third turn (for example ZP20, 442 turns) is the natural next candidate. Dropping the third turn is not.

**Power.**
- D2 at 4M: ±.00043 on P(fix ≥ 2), with 90% power at .0007. ZP13's +.0019 and ZP0-26's pooled +.0008 (8M, ±.0003, 90% power at .0005) are both above these.
- The 2M D1 + D1′ runs (±.00061 per side) are a screen only: 90% power at about .0010.

**Compute for §13:** about 2.5 h (screens about 20 min; D2 4M × 3, 81 min; diag 15 min; 2M D1 × 2, 35 min), one heavy job at a time, with out-of-tree code. Cancelled under the stop rule: the ZP13 diag and the 8M runs for ZP13 and ZP0-26.
