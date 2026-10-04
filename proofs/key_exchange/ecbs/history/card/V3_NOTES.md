# PLAYER_CARD_v3: evidence (scratch; nothing committed, drafts in kx-specs untouched)

Protocol (Zachary, adopted): send C = [a]P and A = pi(C) - C. Receiver: C on the curve; rebuild A from C
with one chord add; reject if A is empty (run empty, i.e. C one of the 5 points of E(GF(3))); reject
unless the rebuilt A matches peg for peg; walk the key over A. Shared key = (lambda-1)ab*P.

Code (new, v2 scripts left as they were): `homes_v3.py` (v3 board: control row, one ladder/tally, root
strip and mini key homes, certificate, calling), `card_sim_v3.py` (full exchanges vs PARI),
`soundness_v3.py` (field + peg level), `extras_v3.py` (grid/control bookkeeping, base-point share),
`calling_check.py` (calling rule: resume from the board, stale pegs, coordinates).
Python: `python`. Outputs: `card_sim_v3_{Toy,Hobby,Serious}.json/.txt`,
`card_sim_v3_Toy_Hobby_Serious_storeP.json`, `soundness_v3_{field,peg}_*.json` (+ `sf3_*.txt`,
`sp3_*.txt`), `extras_v3.json`, `calling_check.json`. Moves use the drafts' convention (place/lift/drop 1, slide 2 per peg,
clear 1 per peg). Control-row moves are counted separately. Calls move no pegs, so they are counted as holes called.

## Card schedule (as simulated)
Base point (root strip in the across; W R W R in key cells 1-4) -> roll -> walk -> finish (C in across/up)
-> call their C into base bands -> curve test -> certificate of own across/up in place (phase peg white)
-> certificate of the base bands in place, reject if empty (phase peg red) -> call their A into bottom
and gap, compare with base bands -> clear bottom, gap, then own across/up -> walk key over base bands -> fold.
Calls follow BS PR #152 s3.1 as revised after DHH's review (re-run 1 Oct; the field-level soundness has no calling step and was not re-run):
- Before calling, clear the homes named. The sim asserts each receiving home is empty when calling starts.
- Stand a peg in the calling hole (control-row hole 16, "calling in progress"). Put the cursor ships on hole 0 of the first home.
- Call the matching hole of the sender's published band aloud by grid and coordinate ("grid 2, A1"). Go hole 0 to n-1
  in number order, with no early stop, never calling the key grids or row J.
- Lay the answer in the cursor hole, then move the cursor ships to the NEXT hole to call (BUILD's resume convention).
- After the last hole, park the ships off the board and lift the calling peg.
- Each call is driven only by the board: the phase hole picks which bands (C or A), and the cursor picks the band and hole.
  Every session lets go at 3 random points, and the board is checked to show exactly what has been copied.

## Full exchanges vs PARI (every run)
| | Toy | Hobby | Serious |
|---|---|---|---|
| exchanges (people), re-run with the revised calling | 10 (20) | 6 (12) | 4 (8) |
| base point by rule = P | 20/20 | 12/12 | 8/8 |
| sent C = [a]P | 20/20 | 12/12 | 8/8 |
| sent A = [(lambda-1)a]P = pi(C)-C | 20/20 | 12/12 | 8/8 |
| receiver's rebuilt A = sender's A; curve test passed | 20/20 | 12/12 | 8/8 |
| both shared points agree and = [(lambda-1)ab]P | 10/10 | 6/6 | 4/4 |
| folded key = spec s6 reference fold, both sides | 20/20 | 12/12 | 8/8 |
| band peak (also counting bands being lifted) | 7 (7) | 7 (7) | 7 (7) |
| peak per phase: base pt / walk / calls / curve / make / rebuild / shared | 7/7/6/7/7/7/7 | same | same |
| highest workbench hole / workbench | 66/72 | 174/180 | 534/540 |
| holes called per receiver (4 bands x n), all in number order, each naming a hole of the sender's band | 92 | 236 | 716 |
| cursor-ship steps per receiver (control moves) | 94 | 238 | 718 |
No home clash in any run: every result and every called answer landed in an empty home (asserted). Stale pegs
cleared at calling start in the honest flow: 0 (the homes are already empty; the rule is a safeguard).
lambda - 1 is nonzero mod l at all three tiers (checked), so (lambda-1)ab*P is still uniform on <P>\{O}.

Negative control (`extras_v3.py`): if C and A were both published at once, each receiver would still hold
its own C and A. That leaves 3 empty homes for 4 called bands, so it does not fit. That is why A is called after
both players have certified.

## Moves per person, whole exchange including the base point (mean, measured; ranges are over sampled keys)
| phase | Toy | Hobby | Serious |
|---|---|---|---|
| base point (incl. W R W R walk) | 23,400 | 105,759 | 734,962 |
| own walk + finish | 52,302 | 765,780 | 19,437,484 |
| laying called answers | 61 | 156 | 473 |
| curve test | 879 | 4,213 | 30,658 |
| make own certificate | 7,176 | 44,250 | 363,624 |
| rebuild theirs + compare + clears | 7,238 | 44,404 | 364,102 |
| shared walk + finish + fold | 50,767 | 750,246 | 19,356,465 |
| **total per person** | **141,822** (100,208-170,550) | **1,714,807** (1.36-1.97 M) | **40,287,769** (37.2-44.0 M) |
| check (curve + make + rebuild) share | 10.8 % | 5.4 % | 1.9 % |
| base point share | 16.5 % | 6.2 % | 1.8 % |
| control-row + cursor moves (extra) | 1,302 | 3,367 | 10,564 |
| ladder build, once per kit | 65 | 173 | 533 |

## Soundness (receiver verdicts: accept / curve / empty / mismatch)
Field level, PARI elements, the card's steps written out literally (ladder-and-tally inversion included):
| class | Toy | Hobby | Serious |
|---|---|---|---|
| honest C, correct A | 5000 accept | 3000 accept | 1000 accept |
| C outside <P> (kP+T or random), correct A | 5000 accept, A in <P> 5000 | 3000 / 3000 | 1000 / 1000 |
| C outside <P>, wrong A (A=C, -A, non-subgroup) | 5000 mismatch | 3000 mismatch | 1000 mismatch |
| C = each of the 4 nonzero order-5 points x 4 A's (incl. empty bands) | 16 empty | 16 empty | 16 empty |
| A not matching (random subgroup pt, -A, one peg changed, C, non-subgroup) | 5000 mismatch | 3000 mismatch | 1000 mismatch |
| C off the curve, A = the card formulas on C | 5000 curve | 3000 curve | 1000 curve |
| ... of those, would pass with no curve test | 5000 | 3000 | 1000 |
| ladder inversion wrong | 0 / 5000 | 0 / 3000 | 0 / 1000 |
Every accepted A equalled PARI's pi(C) - C and lay in <P>. For every on-curve C sampled, "run empty", pi(C) = C and 5C = O
held or failed together (asserted).
Peg level (homes_v3 boards, receiver holding its own A while rebuilding, C and A now called in from a sender board
under the revised calling rule): Toy 30, Hobby 15, Serious 6 per
class (order-5: 4 points x 2 A's = 8): identical verdicts in every class, band peak 7 throughout.
**"C outside the subgroup" is accepted when its certificate is right.** That is by design: the receiver
uses A, never C, and A is always in <P>. So no small-subgroup leak is possible.

## Control holes (the v2 [GAP]): closed and verified
Control row = row J of the workspace grids, run on grid to grid (Toy 4 x 10, Hobby 4 x 20, Serious 10 x 20 holes):
script marker 0-14, phase hole 15, calling hole 16, ladder 17.. (WRRW / WRWRR / WRWWRRW in build order), parking hole, tally.
| | Toy | Hobby | Serious |
|---|---|---|---|
| need / available (was 32 / 51 / 113 before the calling hole) | 33 / 40 | 52 / 80 | 114 / 200 |
| tally peak | 11 | 29 | 89 |
| highest hole used | 32 | 51 | 113 |
| script marker peak | 15 of 15 | 15 | 15 |
Asserted in the sim: no overrun; the parked rung always matches the ladder; there is never a second tally
(`Tally3.start` asserts the row is empty). The phase hole ends red on both boards.
Not simulated: the coordinate rails (spec s3 R8, key grid). Also not simulated: hands-off position *inside*
a certificate or an inversion step (the script marker covers walks and the root strip only, as in v2).

## Calling rule checks (`calling_check.py`)
| | Toy | Hobby | Serious |
|---|---|---|---|
| let go before every call of a session, resume from the board alone | 46/46 ok | 118/118 ok | 358/358 ok |
| stale receiving home, answers laid without clearing: copy wrong | 200/200 | 200/200 | 200/200 |
| same, with "clear the homes named" first: copy wrong | 0/200 | 0/200 | 0/200 |
| published across / up bands as called | grid 2, A1..C7 / D1..F7 | grid 3, A1 .. grid 4, C9 / D1..F9 | grid 7, A1 .. grid 8, I9 / grids 9-10 |
Coordinates for all 7 homes are disjoint, never row J (control row), never a key grid (5 / 9 / 21-22). Every logged
call maps back to the same hole of the sender's band (asserted in every exchange).

## Earlier defaults
(i) Tally rebuild from the ladder: the problem is gone. Only one tally exists and inversions never nest, so
one row of at most 11 / 29 / 89 holes is enough (asserted). Recommendation: drop the rebuild rule (v3 has none).
(ii) Re-derive P vs store it in 2 bands: with P stored all game the peak is 9 bands at every tier
(`card_sim_v3_..._storeP.json`, exchanges still correct). Grids (ecbs_budget.budget): Toy 5 -> 5, Hobby 9 -> 9
(the 2 spare band slots absorb it), **Serious 22 -> 26**. Saving per game = the base point: 16.5 % / 6.2 % / 1.8 %.
Recommendation: keep re-deriving at every tier. Storing P could be an optional Toy/Hobby variant only.

## Card length
PLAYER_CARD_v3.md: play card 1,089 words + check card 350 = 1,440 (wc-style token count; v1 794, v2 1,410).
The revised calling rule added 8 words to the play card (grid numbering, calling hole) and 38 to the check card.
The single-page target was not met, so the card is split (Zachary's fallback). The v3-only state rules (control row, phase hole,
rails, strip and mini-key homes, calling) take roughly 80 words (an estimate, not counted) and keep "all state in the pegs".

## Spec fixes for re-land (certificate protocol)
The earlier 10-item list is not saved on disk. This list was rebuilt from ECBS_SPEC.md, EXPLAINER s6 and the runs above.
1. s0 rows 5/10, s5.2.2: replace the trace check with the certificate. Send C and A = pi(C) - C. The receiver runs the curve
   test on C, rebuilds A (one chord add), rejects if A is empty and rejects unless it matches. It walks over A, and K = (lambda-1)ab*P.
2. State the lemma: (pi - 1) maps E(GF(3^n)) onto <P> with kernel E(GF(3)). So a matching A is in <P>\{O}, and A = O
   exactly for the 5 GF(3) points. C itself may lie outside <P>; it is accepted but harmless. Drop "accepts exactly <P>\{O}".
3. s5.2.1 / s7: the curve test stays mandatory. With a self-consistent A, 100 % of off-curve C pass without it. The twist
   analysis in s7 is written for the trace check and needs restating for the certificate (not re-run here).
4. s6: the uniform-shared-point model is unchanged because lambda - 1 is a unit mod l. Restate K.
5. s5.2 exchange: BS PR #152 s3.1 calling, as revised after DHH's review. Clear the receiving homes first; use a
   calling-in-progress hole; park the cursor at the NEXT hole to call (off the board at the end); call each hole aloud by
   grid and coordinate (grids numbered from the workbench). Call only the published bands, in number order, with no
   early stop, never the key or control row. C goes into the base bands first. A goes into the bottom and gap after both players have certified.
   Calling all four bands at once does not fit 7 homes. Holes called per receiver: 92 / 236 / 716. The sender certifies
   in place, consuming C, after its C has been called.
6. s2: control inventory. Drop the trace ladder and the second tally. Control row = row J of the workspace grids: 15
   script + 1 phase hole (replaces the 3-hole protocol marker) + 1 calling hole + ladder + parking + tally
   = 33/52/114 of 40/80/200.
   This replaces "columns 9-10 and row J".
7. s2 / s5.2 numbers: validation 3.9 M -> 0.76 M (Serious); check 15.3 k / 93 k / 0.76 M. Per person 0.142 / 1.71 /
   40.3 M (sampled keys). Peak still 7 bands in every phase; grids 5 / 9 / 22.
8. s3 R6: one ladder, laid in the spare from n-1 pegs, with the leftover thrown away. Rungs go into the control row in
   build order; climb from the last made with the parking hole; one tally, no rebuild rule. Fix "three ladders" (s8).
9. s5.1: the root strip lives in the across band; W R W R goes in the first four key cells; the script marker counts strip steps;
   the base point is made before the key is rolled. Remove "trace check on P" from the s8 test-vector row.
10. s3 R7 / s8: the chord rule now appears only in the certificate (lazy y and Frobenius in place after the inversion). Drop the
   receiver-chain and trace rows; add certificate and calling rows. Keep the v2 literal verse wording ("mirror the
   across, lay base across times a copy of the bottom onto it").
11. Demo tier: the certificate at Demo (1/2 set, chord walk) was not simulated here. Its control budget needs re-checking.
