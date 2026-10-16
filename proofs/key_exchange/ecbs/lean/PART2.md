# ECBS Link 2 part 2

Handoff for `cursor/ecbs-link2-part2` after `origin/main` (`884f1775`, part 1) was merged. Part 1's `HomeIn`, `BoardShape`, `Budget`, and `FieldLay.fits` stay. Part 2 call sites of `settle_*`, `place_*`, `mul_refines`, `mul_no_eq`, and `cube_off_eq` pass those bundles. This file is not `RESUME.md`.

The EcbsLink2 build log has no `linter.unusedVariables` warnings. `demo_invert_hole1` is `invert_number` on Demo's white peg in hole 1 (`hole1Peg`); the export returns `hole1Inv`, a different list. `demo_multiply_hole1` is that peg times `hole1Inv`, and the export returns the unit. 3886 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. The build succeeded under `ulimit -v 7000000`.

Next: the board `chord_add_open` leaves, marker off, meets `OpenLay` and `OpenMatch`, so `chord_add_point` can call `open_checked` and drop `hinv`. Then the remaining settle rooms, full `walk_chord`, `walk_fform`, `base_point_of`, and the other seven exports. Eight exports are not tied.

ECBS Link 2 part 2, branch `cursor/ecbs-link2-part2`. Part 1 is PR #201 on `cursor/ecbs-link2-4113`. Pick up from this note.

## Done on this branch, past `d49b865d`

- Nocopy `mul` with the marker on. `EcbsLink2/Link2/MarkerMul.lean`.
  `mul_down_eq`: marker lifted (`marker < 0`). `mul_up_eq`: marker already seated at `m`.
  Both say the emitted nocopy multiply is `mulNoOffBoard` of the board `marker_step` leaves, with the flag put back. The schoolbook is `school_loop_refines`. The lane fold is `lane_fold_refines`. `add` still never reads the marker.
- Bench-on cube with the marker seated. `EcbsLink2/Link2/MarkerBench.lean`, `cube_bench_up`.
  The bench is on and aimed at `home`, which is not the cube's source. `Ecbs.cube` steps the marker, slides that bench, then runs the marker-off comb of the source, and the flag stays on. `settle_flag` is the slide. `cube_tail_flag` is the comb.
- Across cube of `frobenius_affine` with the marker lifted. `EcbsLink2/Link2/FrobeniusOn.lean`, `down_across`.
  The emitted across cube is the flagged `cubeOffBoard` of `markerDownFeed`. The board it leaves has the bench on and the marker seated at 0. That is the board the up cube reads.

Compile peaks (VmHWM) before `across_up_cube` was added: MarkerMul 449356 kB, FrobeniusOn 385768 kB, MarkerBench 226532 kB. Re-measure FrobeniusOn after that theorem. All under 2 GB. 3089 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `FrobeniusRead.lean`

- `across_up_field`: the up cube returns `{upBoard with marker_on := true}`, and `upBoard`'s bench prefix is `fieldCube` of the up input (`up_field`, `cube_off_eq` on the board `up_slide` leaves).
- `up_close`: the closing settle writes that prefix into the up home and turns the bench off.
- `frobenius_affine_marker`: `Ecbs.frobenius_affine` with the marker lifted equals that settle. Home 0 is `fieldCube` of across (`up_home0`), home 1 is `fieldCube` of up, the marker flag stays on, the bench ends off. The three settle `FitsLen` checks stay hypotheses.

Compile peaks (VmHWM): FrobeniusRead 276480 kB, WalkLive 219316 kB, ChordRun 271244 kB after `chord_copy_add`. ChordIf 277208 kB, ChordRise 255200 kB, ChordTail 256168 kB. 3235 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `WalkLoop.lean`

- `walk_chord_eq`: the emitted `walk_chord` is `walkChordGo`. The bridge is `rfl`.
- `chordStep_zero`, `chordStep_fresh`, `chordStep_cube`: one cell of that loop. A zero cell while the accumulator is empty only lifts the marker. A white or red cell while it is empty copies the base. A zero cell while it is live is `frobenius_affine`, taken as a hypothesis so the cube board stays abstract.
- `walk_chord_zeros`: every cell empty, any length. The homes stay, the marker ends up, the result is not live and ok, and `walkRun` keeps the accumulator.
- `walk_chord_white_open`: any run of empty cells, then one white cell. Across and up become the base point, the result is live and ok, and `walkRun` is that base point.
- `walk_chord_red_open`: the same run of empty cells, then one red cell. Up is the negated base up.

Compile peak (VmHWM) for that file: WalkLoop 298392 kB. Axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `WalkLive.lean`

- `up_settle_fit` / `frobenius_affine_len`: the three settle `FitsLen` checks follow from a length-`n` home (`pegCount ≤ n`) and the cell's move and slide room (`cubeCharge`, `slideCharge`). They are not hypotheses of `frobenius_affine_len`.
- `cellFit_consume` / `live_zero_fit`: the cell invariant carries `FitsLen` of the remaining charges. One live zero spends one charge.
- `chordStep_live_zero`: a live zero cell is `marker_lift` then `frobenius_affine_len`. Homes become `fieldCube` of across and up, which is `walkStep` on colour 0. The Frobenius equation is not a hypothesis.

## Done in `ChordRun.lean`

- `trit_cancel` / `fieldSub_self`: a trit list subtracted from itself is the zero home.
- `chord_bump`: the chord op counter grows by one.
- `chord_copy_add`: on that bumped board, copy the base across into the bottom and `add` the accumulator across away. The bottom is `fieldSub`. One `FitsLen (moves + 2 * n)` covers the copy and the add, because each home has at most `n` pegs.
- `specInv_zero` / `walkStep_empty_run`: a zero run is not a peg in hole 0, so a live white or red cell is `none`. `is_zero_replicate` is the emitted check of that home.

## Done in `ChordIf.lean`

- `chord_add_eq`: `Ecbs.chord_add_demo` is `chordAddEmit` by `rfl`. The generated cost lets are not the nested record update under `rw`; `except_pull` reassociates them onto `chordCopyAddGo`, and the `if is_zero` is that copy-then-add.
- `chord_add_empty`: an empty run (`fieldSub` is `n` zeros) returns `.ok (false, bA)`. The bottom is that zero home. The walk, not this return, clears the marker.
- `chord_add_open`: a nonempty run is `chordAddTail` on that board. The bottom is `fieldSub` of the two across homes. `is_zero_embed` is the check for any length-`n` home.

Compile peak (VmHWM): ChordIf 277208 kB.

## Done in `ChordRise.lean`

- `chord_rise`, `chord_rise_white`, `chord_rise_red`: copy the base up into the empty spare (mirrored when the cell is red) and take the accumulator up away. The spare is `fieldSub`. Up and base up stay. The marker flag stays. One `FitsLen (moves + 2 * n)` covers the copy and the add.

Compile peak (VmHWM): ChordRise 255224 kB.

## Done in `ChordTail.lean`

- `chord_tail_after_inv`: if `invert_checked` on the marker-off board returns `bI`, restoring the flag and running the rise is `chord_rise`. What remains of `chordAddTail` is `chord_tail` on that board. The inverse on a walk board is still a hypothesis.

## Done in `ChordGap.lean`

- `chord_gap_mul`: the first multiply of `chord_tail`, gap times spare, with the marker seated. The bench prefix is `fieldMul` of the gap home by the spare home (first times second).
- `chord_gap_prefix_slope`: that prefix equals `fieldMul rise inv`, which is the slope in `Spec.chordAdd`. Both homes are trits.

## Done in `ChordClear.lean`

- `chord_gap_clear`: `mul` of the gap by the spare, then `clear` of the gap. The gap was still held, so the bench stays on and aimed at the gap, holding the lane fold of `fieldMul inv rise`. The gap home is empty. The move counter grows by `pegCount inv`, and that sum has to fit (`FitsLen`).

## Done in `ChordSettle.lean`

- `chord_gap_settle`: `mul`, then `clear` of the gap, then `settle`. The gap home is `fieldMul rise inv` (SPEC.md §3 R7 line 156, via `slope_mul_swap`). The bench turns off. The marker flag stays on. The settle charges (`FitsLen` of twice the prefix's peg count, on moves and on slides) stay hypotheses.

## Done in `WalkLive.lean` (reroll cell)

- `chordStep_reroll`: a live white or red cell whose `chord_add_demo` returns the reroll flag is `Flow.ret ((true, false), marker off)`. The loop does not advance.
- `chordStep_empty_run`: that flag is `chord_add_empty` when the run is the zero home, and `walkStep` is `none`.

## Done in `FieldComm.lean`

- `fieldMul_comm` / `school_comm` / `slope_mul_swap`. SPEC.md §3 R7 line 156 names the slope as "rise over run", and `Spec.chordAdd` multiplies `fieldMul rise inv`. The same line's card says "do the gap times the spare": after the inverse sits in the gap and the rise sits in the spare, that product is `fieldMul inv rise`. The schoolbook strip does not depend on which factor is laid, and the lane fold is a function of that strip, so the two lists are equal. `Spec.chordAdd` is unchanged. This is not a spec/code mismatch: the formula and the card name the same product.

Compile peaks (VmHWM) under `ulimit -v 7000000`: FieldComm 230832 kB, ChordGap 201624 kB, WalkLive 257864 kB, ChordClear 212968 kB, ChordSettle 298976 kB. 3313 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `MarkerCopy.lean` / `MarkerCopyEq.lean`

- Generic copy multiply (`copy_second = true`, `onto = false`, `mirror = false`). The inlined schoolbook is changed to `rowStep` after the board is reduced (`mul_copy_off_after`); a whole-term `rfl` of `Ecbs.mul` against that loop exceeds the heartbeat limit. `mul_copy_up_after` / `mul_copy_down_after` are the same body after `marker_step`. `mul_copy_up_eq` / `mul_copy_down_eq`: marker on, the emitted multiply is the marker-off multiply of the feed, with the flag put back.
- `chord_square`: `mul` of the gap by a copy of itself into the bottom, marker seated. The bench prefix is `fieldMul` of that slope by itself (SPEC.md §3 R7 line 156). `FitsLen` of the copy and the marker script bound stay hypotheses, the same way `chord_gap_settle` leaves the settle charges.

Compile peaks (VmHWM) under `ulimit -v 7000000`: MarkerCopy 388212 kB, MarkerCopyEq 385500 kB, ChordWhite 380520 kB. 3361 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `ChordWhite.lean`

- `bench_white0_step`: the emitted white peg writes `(hole 0 + 1) mod 3` and charges one move.
- `take_set_white` / `chord_square_white`: on the square's bench, that write's length-`n` prefix is `fieldAdd` of the squared slope with `whiteHole0`. SPEC.md §3 R7 line 156, the plus one. One `FitsLen` of the move after the square stays a hypothesis.

## Done in `ChordAcross.lean`

- `bench_add_emit`: the emitted `bench_add` is the copied loop. The bridge is `rfl`.

## Done in `BenchAdd.lean`

- `bench_add_prefix`: the ascending loop. On a length-`n` source and a bench at least that long, the bench becomes `addOnto` and moves grow by `pegCount` of the source. The bridge is `bench_add_emit` (`rfl`). The coefficient-indexed invariant is the same shape as `add_refines`.
- `addOnto_off` / `addOnto_on` / `bench_add_field`: the length-`n` prefix is `fieldAdd` with the source, or with `mirrorTrits` when the mirror is on. `mirrorTrits` is what `mirror_refines` writes.
- `bench_add_across_bottom`: across with the mirror off, then the bottom with the mirror on. The length-`n` prefix is `fieldAdd` of the starting prefix with the across, then with `mirrorTrits` of the bottom. SPEC.md §3 R7 line 156, add its across and take away the bottom. One `FitsLen (moves + 2 * n)` covers both.

Compile peak (VmHWM) under `ulimit -v 7000000`: BenchAdd 385944 kB.

## Done in `BenchSettle.lean`

- `clear_settle_held`: `clear` of the held home the bench is aimed at, then `settle`. The home becomes the length-`n` bench prefix. The bench turns off. The settle charges stay hypotheses.
- `across_bottom_settle`: the across with the mirror off, the bottom with the mirror on, that clear, and that settle. The bottom home is `fieldAdd` of the starting prefix with the across, then with `mirrorTrits` of the bottom. SPEC.md §3 R7 line 156. The zero tail and the settle charges stay hypotheses.

Compile peak (VmHWM) under `ulimit -v 7000000`: BenchSettle 385028 kB. 3402 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `ChordTake.lean`

- `chord_take_mirror`: `add` of the bottom onto the across with the mirror on, then `mirror` of the up. The across becomes `fieldSub` of the old across and the bottom. The up becomes `mirrorTrits`. SPEC.md §3 R7 line 156, take the bottom away from its across and mirror its up. One `FitsLen (moves + 2 * n)` covers both.

Compile peak (VmHWM) under `ulimit -v 7000000`: ChordTake 384964 kB. 3403 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `StripLin.lean` / `BandCopy.lean`

- `school_strip` / `school_onto`: the schoolbook adds onto its strip. Starting from a home is the zero-strip product added to that home.
- `stripAdd_addAt` / `foldHigh_pad`: folding a sum whose second summand is empty at that high hole moves only the first summand's peg.
- `band_copy`: the `onto` arm's copy loop writes the destination into a zero strip. The result is `pref`.

Compile peaks (VmHWM) under `ulimit -v 7000000`: StripLin 385028 kB, BandCopy 386132 kB. 3432 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `StripFold.lean`

- `foldrHigh_pad` / `reduceStrip_pad` / `laneFold_pad`. The lane fold of a sum is the sum of the folds when the second summand has no peg at or above hole `n`. The fold over the offset list is its own induction; `foldHigh_pad` stays the one-hole step.
- `laneFold_onto`. Laying the schoolbook onto that sum and folding is the folded product added to the pad.
- `onto_add`. The length-`n` prefix is `fieldAdd` of the home and `fieldMul` of the two factors. `mul_onto_add` is the same fact next to the emitted multiply.

## Done in `MulOnto.lean`

- `mul_onto_school`. `mulFromHeld` on a strip that already holds the destination is `school_loop_refines` from that strip, then `mulAfter`.
- `mul_onto_else`. Bench off, so `settle` is the identity. `mulElse` with `onto`, not `copy_second`, not `mirror`, clears the destination, charges `2 * pegCount` moves and the same number of slides, copies the home (`band_copy_after`), and is that schoolbook.
- `mul_onto_off`. Marker off. `Ecbs.mul` is that `mulElse` after the op bump.
- `mul_onto_up`. Marker on and already seated. `log_op` is `marker_step`, and the onto multiply is `mul_onto_else` on `markerOn (bumpOp (markerUpFeed …) …)`. The flag stays on. The conclusion names `markerOn`, so it matches `onto_up_prep`.
- `ontoCharge_markerOn` / `onto_up_prep`. The marker flag commutes with the onto charge, the prep, and `withMoves`.
- `mul_onto_up_eq`. The seated onto multiply is the marker-off multiply of `markerUpFeed`, with the flag put back. `dsimp` then `simp only [markerOn_mk]` turns the record update into `markerOn`. `erw [onto_up_prep]` matches where `rw` does not. `mulAfter_flag` carries the flag across the fold, and `mul_onto_off` is the right-hand side.
- `mulAfter_ok` / `ontoFoldBoard`. `mulAfter` on a marker-off board is `.ok` of the lane-fold bench, then `note_peak`.
- `mul_onto_off_fold` / `mul_onto_up_prefix`. That bench's length-`n` prefix is `fieldAdd` of the destination home and `fieldMul` of the two factors. The seated result is the same board with the flag on.
- `card_y3`. SPEC.md §3 R7 line 156. `fieldAdd` of `mirrorTrits y` and `fieldMul slope dx` is `fieldSub` of that product and `y`. That is the new up once the onto multiply's home is the mirrored first up and `dx` is `fieldSub` of the first x and the new x.

Compile peaks (VmHWM) under `ulimit -v 7000000`: StripFold 210760 kB, BandCopy 239636 kB, MarkerMul 441692 kB, MulOnto 306548 kB. 3486 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. A clean `lake build EcbsLink2` under that ulimit succeeded.

## Done in `ChordUp.lean`

- `move_band_off`: bench already off, so `move_band`'s opening `settle` is the identity. `dst` is empty and `src` is held. The source home moves to `dst`. Moves and slides each grow by `2 * pegCount`. `note_peak` may raise the peak. One outer `settle_skip` drops the identity settle without unfolding the record; later lets are dropped one at a time (`zeta1`) and the board is generalised back to a variable so the record is not copied into itself.
- `chord_up_slide`: on the board the onto multiply leaves (bench on and aimed at the up, up and across empty, gap still holding the slope, bottom holding the new x), `clear` the gap, `settle` into the up, and `move_band` the bottom into the across. The up is the length-`n` bench prefix. The across is the bottom's old home. The gap and the bottom end empty. The bench ends off. The marker flag stays. SPEC.md §3 R7 line 156. The settle charges and the move's `FitsLen`s stay hypotheses.

Compile peak (VmHWM) for ChordUp under `ulimit -v 7000000`: 387512 kB. 3509 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. A clean `lake build EcbsLink2` under that ulimit succeeded.

## Done in `ChordCell.lean`

- `walkStep_live_chord`: a live white or red cell whose run inverts is `some (true, (x3, y3))`, with `x3` and `y3` the SPEC.md §3 R7 line 156 formulas on the cubed accumulator.
- `mul_refines` now also says the copy multiply keeps the marker index, the control counter, and the script maximum. `CurveTest` splits those three conjuncts off the hole equality.
- `gap_settle_lay`: gap times spare, clear, settle. The gap is `fieldMul rise inv`. The spare is empty. Homes other than 5 and 6 stay. Marker, control, and the script maximum are the values `markerUpFeed` writes. Moves and slides are `mvGap` and `slGap`.
- `square_white_lay`: on that board, square the slope and write the white peg. The bench prefix is slope² + 1. Homes other than the spare stay. The spare stays empty.
- `gap_square_obtain`: those two, with `obtain` on the settled board. The `do` is the prefix of `chord_tail` through `bench_white0`.
- `x3_settle_lay`: the across with the mirror off, the bottom with the mirror on, clear, and settle. The bottom is `chordX3` (slope² + 1 + across − run). The bench turns off. Marker, tier, moves, and slides are projections (`benchAddBoard_home`, `settle_home_eq`, `settle_ix`); the settled record is not simplified.

The take, the mirror, the onto multiply, and `chord_up_slide` are not in that `obtain` yet. The inverse on a walk board is still a hypothesis. The `FitsLen` charges of the gap, the square, and this settle are still hypotheses.

Compile peak (VmHWM) for a clean `lake build EcbsLink2` under `ulimit -v 7000000`: 978612 kB. 3540 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Done in `ChordLay.lean`

- `square_kept`: gap times spare, clear, settle, then the square and the white peg. The bench prefix is slope² + 1, with a zero tail. Homes other than the spare stay, and home 5 is the slope.
- `bottom_lay`: that square, then the two bench adds, the clear, and the settle. The bottom is `chordX3` (slope² + 1 + across − run). Across stays the cubed across, the gap stays the slope, the bench ends off. SPEC.md §3 R7 line 156. The `FitsLen` charges of the settle stay hypotheses.
- `point_from_bottom`: on that board, `add` of the bottom onto the across with the mirror on, `mirror` of the up, then the onto multiply of the gap by that difference. The bench prefix is `chordY3`. `card_y3` is the mirrored up plus the product. The conclusion now also has the `OntoLay` facts on `markerOn` of that board: across and up empty, bottom kept as `chordX3`, gap kept as the slope, bench on and aimed at the up. That board is handed to `slide_point`. The `do` from `add` through `move_band` is `.ok`, home 0 is `chordX3`, and home 1 is `chordY3`. The two tail rooms are `FitsLen` of the post-multiply moves plus `5 * n`, and of the slides plus `6 * n`.
- `fold_tail`: after the lane fold, holes from `n` up are empty.
- `slide_point`: clear the gap, settle the bench into the up, and move the bottom into the across. Homes are 1, 0, 2, 5. The up is the bench prefix and the across is the bottom's list. `FitsLen (moves + 5 * n)` and `FitsLen (slides + 4 * n)` cover the settle and the move, because a length-`n` home has at most `n` pegs. Those two rooms are the ones a later budget supplies. The seven settle `FitsLen`s are not hypotheses.
- `square_kept` exports `ops[0] = cOps + 2` after the gap multiply and the square.
- `bottom_lay` also exports the marker, control, script maximum, tier, moves, slides, held 2, the kept up, `ops[0]`, and the peak triple, so the slide reads them off this conclusion.
- `chord_do_join`: the square-and-settle prefix, then the slide, then the generated `pure`, is one `do`.
- `chord_tail_across_up`: `Ecbs.chord_tail b Ecbs.across Ecbs.up` is that `do`, by `rfl`.

`x3_settle_lay` now also says which homes stay, and `chord_take_mirror` says the same for the take. `mul_onto_up_prefix` returns `OntoLay`: the destination and the second factor are empty, the bench is on and aimed at the destination, and the other homes stay.

Compile peak (VmHWM) for ChordLay under `ulimit -v 7000000`: 1579356 kB. Under 2 GB.

## Done in `ChordOpen.lean` and `WalkLive.lean`

- `chord_tail_point`: obtain `bottom_lay`, obtain `point_from_bottom`, then `rw [chord_tail_across_up]` and `chord_do_join`. `Ecbs.chord_tail` on the across and the up is `.ok`, home 0 is `chordX3`, home 1 is `chordY3`. The tail `FitsLen`s are passed in, not rebuilt with `omega`.
- `chordStep_open`: a live white or red cell whose `chord_add_demo` returns `(true, bA)` stays live. The index advances unless the cell is last.
- `chordStep_live_spec`: that step, together with a `walkStep` hypothesis for the same point. `walkStep_live_chord` is the spec side. The chord add is still a hypothesis: `chord_tail_after_inv` does not yet hand its rise board to `chord_tail_point`, and `invert_checked` on a walk board is still a hypothesis.
- `chord_add_from_tail`: if `chordAddTail` is `chord_tail` on the rise board and that tail returns `b'`, the add returns `(true, b')`.
- `chord_rise` / `chord_rise_white` / `chord_rise_red` keep across (home 0), bottom (home 2) and gap (home 5), and the fields the tail does not write. The peak is whatever `place` leaves, as a natural.
- `chord_tail_after_inv` exports those kept homes. `chord_add_point` obtains that board and applies `chord_tail_point`. `chordAddTail` is `.ok (true, b')` with home 0 `chordX3` and home 1 `chordY3`. `invert_checked` is still a hypothesis.

3755 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. A clean `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. The earlier fresh elaboration of ChordOpen, before `chord_add_point`, peaked at 353308 kB.

## Done in `InvertWalk.lean`

- `OpenLay`: the marker-off board `invert` reads. The control row is still the painted ladder, the ladder array is climb order, the gap and the spare are empty, and home `bottom` holds the input. Counters are naturals, with room for the gap copy and the tally peg.
- `OpenMatch`: the climb budget is those counters after the copy, and the tier's ladder. The peak is whatever `place` leaves when the gap becomes held.
- `open_tally`: bump `op_inv`, copy the bottom into the gap, lay the white peg at the tally origin. The gap is the input. The control counter grows by one.
- `open_climb`: that board satisfies `ClimbInvK` at the empty prefix. The model is `entryModel` with the walk's control counter.
- `open_invert`: `Ecbs.invert` on that board is the climb bound into the final tail.
- `open_invGap`: home 5 after that `invert` is `invGap` of the bottom.
- `open_check_mul`: the check multiply of that gap by the bottom is `fieldMul`, and `bench_read_and_clear` returns it.
- `open_checked`: `Ecbs.invert_checked` on that board is `.ok`, and home 5 is the list `fieldInv` returns. The hole-0 peg is nonzero, the tail is zero, and a red peg mirrors the gap.

3822 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. The `EcbsLink2` build that included `open_checked` peaked at 490888 kB VmHWM. A clean `lake build EcbsLink2` under `ulimit -v 7000000` succeeded.

## Done in `CopyLay.lean` and `ChordOpen.lean`

- `RunFrame` / `copy_add_open`. The board `chordCopyAddGo` leaves, with the marker held off, is `OpenLay` for `fieldSub` of the two across homes. A climb budget on those counters is `OpenMatch`. The two across copies and the gap copy `invert` does next are one `FitsLen (moves + 3 · n)`. The climb `FitsLen`s are the budget, the same shape as `entryBudget`, starting from this board's counters rather than from zero.
- `RiseRead` / `chord_add_point`. `open_checked` returns the inverse, so `chord_add_point` no longer takes `invert_checked` as a hypothesis. `chord_add_point_of_inv` is the tail once the counters are known. The settle `FitsLen`s are discharged below.
- `open_check_mul` / `open_checked` also say home 2 is still the input and still held. The climb keeps `xHome`, `CheckRead` keeps it through the final cube, and the check multiply keeps every home other than the spare. A red mirror writes home 5 only (`mirrorHome_other`).

Homes 0, 1, and 4 are on `ClimbBudget` (`side0`, `side1`, `side4`, and the three held flags) and `ClimbShape` carries `SideKeep`. A rung writes the gap and the spare; `shape_refresh` is handed the three cells it did not write. The fresh tally board starts them empty. A walk board records them on `OpenLay` and `OpenMatch`, and `copy_add_open` shows the copy-add leaves them.

`QuietKeep` is the rest of that frame: home and held arrays stay length 8, the tier record stays `tierSnap`, and the script-marker index and its maximum stay `markSnap` and `mxSnap`. The fresh tally board starts the marker at `-1` and the maximum at `0`. A walk board records a natural index and maximum on `OpenLay` and `RunFrame`. `final_cube_settle` returns `QuietKeep` on the settled board. `open_check_mul` turns that into `RiseCarry` on the board the check leaves (size 8, `embTier`, the lay's marker and maximum, spare empty, bench off, and the counters as naturals). A red mirror keeps every one of those fields except the move counter, which stays a natural. `open_checked` returns `RiseCarry` for both branches.

`chord_add_point` no longer takes `RiseRead`. It obtains `open_checked` and builds `RiseRead`: homes 0, 1, 2, 4, and 5 and the held flags are the lay and the inverse, and the counters are the naturals `RiseCarry` reads.

## Done in `AfterClimb.lean`, `InvertWalk.lean`, and `ChordOpen.lean`

- `PostCubeBound` / `CheckBound`. The board the final cube leaves has moves, slides, control, and ops slot 0 at most `checkMoveCap`, `checkSlideCap`, `checkCtrlCap`, and `checkOpsCap`. The check multiply, including a red mirror, stays inside the move cap: the white branch has one `n` of slack and the mirror spends at most that many pegs.
- `tailRoom_of`. Every settle `FitsLen` in `TailRoom` follows from one move room `FitsLen (moves0 + tailMoveCap n bench)`, one slide room `FitsLen (slides + tailSlideCap n)`, and one room each for the marker (`m + 3 < script` and `FitsLen (m + 4)`), the control counter (`FitsLen (ctrl + 6)`), and ops slot 0 (`FitsLen (cOps + 3)`). A length-`n` home has at most `n` pegs, so `pegCount` never appears in those rooms.
- `chord_add_point` takes those five rooms on the climb budget (`checkMoveCap + tailMoveCap`, and the same shape for slides, control, and ops) and on the lay's marker. It builds `TailRoom` and the tail is unconditional: `chordAddTail` is `.ok (true, b')`, home 0 is `chordX3`, home 1 is `chordY3`.

4141 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 979360 kB VmHWM; unchanged modules were replayed. The last build that elaborated the climb peaked at 1703936 kB. Both are under 2 GB.

## Done in `CopyLay.lean` and `ChordLive.lean`

- `copy_add_open` also says the marker flag is unchanged, and it exports the lay's marker index, its maximum, and homes 0, 1, and 4 with their held flags. Those are what `chord_add_point` reads off the copy-add board.
- `chord_add_live`. A live white or red cell. `RunFrame` is the board `frobenius` leaves: the accumulator is already cubed. Five rooms cover the climb and the tail: `liveMoveRoom`, `liveSlideRoom`, `liveCtrlRoom`, `liveOpsRoom`, and the script marker (`mark + 3 < script`, `FitsLen (mark + 4)`). `Ecbs.chord_add_demo` is `.ok (true, b')`, home 0 is `chordX3`, home 1 is `chordY3`, and `walkStep` is `some (true, (x3, y3))`. An empty run cannot invert (`specInv_zero`), so the emitted `is_zero` branch is the nonempty tail.

4147 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 484748 kB VmHWM. The climb was replayed. Under 2 GB.

## Done in `ChordNext.lean`

- `cellMoveCharge` / `cellSlideCharge` / `cellCtrlCharge` / `cellOpsCharge`. One live cell adds at most that much. `live_move_le` uses `pegCount ≤ n`. The slide, control, and ops charges are exact.
- `cell_rooms_left` / `marker_room_left`. A fuel of further cells, plus this cell's charge, leaves this cell's `FitsLen` and the same rooms at the next counters. The marker walks a fixed step; `mark + step * (fuel + 1) < script` leaves `fuel` steps.
- `climb_high_ge` / `settle_high_mark`. At the end of the ladder `control_highest` is `t0 + tally - 1`. `final_cube_settle` carries that value through unpark, the final cube, the settle, and `tally_clear`. It is not strictly below `t0`. `RunFrame.highLt` is the first cell, where the high still sits under the tally origin. The settled board does not have it.
- `tally_start_again`. The next tally start, once the high is already at or above the origin and `tally_max` is already positive. The white peg is written. The high and the maximum stay. `tally_put_keep` and `tally_note_keep` are the two branches `tally_start_raise` does not take.

The check multiply, the rise, and the chord tail are not yet shown to keep this high. `set_control` never lowers it, and `finalTail` does not write it.

## Done in the high-water export

- `mul_refines` keeps `control_highest`. The copy multiply does not write that field.
- `open_check_mul` / `open_checked` / `checked_high_mark`. The board `invert_checked` leaves has the same high as the board `tally_clear` leaves, and that high is at least `tallyOrigin`. The next cell's tally start is `tally_start_again`. `RunFrame.highLt` remains the first cell, where the mark still sits strictly under the origin.
- `gapMul_high` / `gap_settle_lay` / `square_white_lay` / `square_kept`. The gap multiply, its clear, its settle, and the slope square keep the recorded high. `gap_settle_high` is that settle.
- `benchAdd_high` / `x3_settle_lay` / `bottom_lay`. The two bench adds, the clear, and the settle into the bottom keep that same high. `bottom_lay`'s board has the high the tail's rise board had.
- `chord_take_mirror` / `ontoFoldBoard_high` / `mul_onto_off_fold` / `mul_onto_up_prefix` / `moveBand_high` / `chord_up_slide` / `slide_point` / `point_from_bottom` / `chord_tail_point`. The take, the onto multiply, and the closing slide keep that high. `chord_tail` on the rise board returns a board with the same `control_highest`.

- `place_high` / `rise_add` / `chord_rise`. The spare copy and the following add leave `control_highest`. White and red share that fact.
- `chord_tail_after_inv` / `chord_add_point_of_inv` / `chord_add_point` / `chord_add_live`. The rise board keeps the inverse board's high, and the board `chord_tail` returns keeps that same high. It is a natural at least `tallyOrigin`. That is the climb water mark, not the strict `RunFrame.highLt` the cell entered with.
- `later_climb_entry`. The next cell's tally start, once `tally_len = 0`, `t0 ≤ high`, and `1 ≤ tally_max`, is `tally_start_again`. The white peg is written, `tally_len` becomes 1, and the high stays. `¬ high < t0`, so `RunFrame.highLt` is not this entry. `ClimbInvK.highTop` still asks for `high = t0 + tally - 1` on every later rung, and this start does not give that equality.

4167 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1703276 kB VmHWM. Under 2 GB.

- `frobenius_affine_room` / `chordStep_live_zero_room`. A live zero cell whose rooms are `FitsLen (moves + cubeCharge)` and `FitsLen (slides + slideCharge)` is the emitted step, and `walkStep` on colour 0 is the two field cubes. `frobenius_affine_len` still asks for the first cell's envelope `moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n` and `slides ≤ 2 * n`.
- `down_across`. The bundle it builds now takes `FitsLen (moves + 8 * n + 6 * (bench - n))` and `FitsLen (slides + 4 * n)`, which are `cubeCharge` and `slideCharge`. The counters that do not include `moves` still use `small_cube_cap`. A later cell can construct `DownAcross` from the room it has left.

4169 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1702184 kB VmHWM. Under 2 GB.

4170 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1702116 kB VmHWM. Under 2 GB.

4158 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 991828 kB VmHWM. The rebuild that re-elaborated ChordLay after the high conjunct peaked at 1594024 kB. Both are under 2 GB.

## Done in the climb high

- `ClimbBudget` carries `high0` and `tallyPos` (`0 < tally0`). `ClimbInvK.highTop` and `ClimbInvKCore.highTop` are `s.high = max base.high0 (s.t0 + s.tally - 1)`. `PegRead.top` is the lower bound the reads use, `t0 + tally - 1 ≤ high`.
- `rungHigh` is the max of the previous high and the new hole. A final rung keeps the high. A non-final white hole is `t0 + 2 * tally - 1`. A non-final red hole is `t0 + 2 * tally`. `set_control` keeps the recorded high when that hole does not beat it. This counter is not a Spec result. `walkStep`, `chordAdd`, and the inverse polynomial do not read it. It feeds the cost field and the next rung's `set_control` test.
- `tally_lay_keep`, `tally_add_one_keep`, `tally_add_one_mark`. Whitening needs only `t0 + m - 1 ≤ high`. The double and the extra peg return `max` of the current high and the new hole. `modelRung_highTop` and `climbTallyPrefix_ge` carry that max through a successor.
- The first cell is the case `high0 ≤ t0`: `entryBudget.high0 = 0`, and the walk copy uses `lay.high` under `RunFrame.highLt`. `open_climb` and `chord_add_live` still enter through `tally_start_raise`, which sets the high to `tallyOrigin`. `later_climb_entry` (`t0 ≤ h0`, `tally_start_again` leaves the high) is not yet an instance of those two theorems.

4177 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1702088 kB VmHWM. Under 2 GB.

## Done in the tally maximum

- `tally_note_mark`. The note records `max` of the old maximum and the new length.
- `tally_double_refines`, `tally_double_withPark`, and `rung_double_refines` no longer require `tmax < 2 · m`. The result maximum is `max tmax (2 · m)`.
- `tally_add_one_raise_stay`, `tally_add_one_keep_stay`, and `tally_add_one_mark`. The extra peg records `max` of the old maximum and the new length. The high is still `max` of the old high and the new hole. `tally_max` is not a Spec result.
- `ClimbInvK.tmaxLt` and `ClimbInvKCore.tmaxLt` are `∃ tmax, tally_max = tmax`. The old bound `tmax < 2 · tally` held on the first cell, where the maximum grows with the tally. A later cell keeps the previous maximum, and that bound fails when the next tally starts at length `1`.

4180 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1702512 kB VmHWM. Under 2 GB.

## Done in the climb entry

- `tally_start_mark`. The first cell (`high < origin` and `tally_max = 0`) raises both marks. A later cell (`origin ≤ high` and `1 ≤ tally_max`) keeps both. The recorded high is `max` of the entry high and the origin. `tally_max` is `max` of the old maximum and `1`. `tally_start_again` is the keep branch; it now lives next to `tally_start_raise`.
- `OpenLay.hStart` and `RunFrame.hStart` are that disjunction. `highLt` is no longer a field. `open_climb` and `chord_add_live` take the disjunction, so the first cell and `later_climb_entry` are both instances. The climb model is `openModelAt`: its high is `max` of the entry high and `tallyOrigin`. On the first cell that max is `tallyOrigin`.

4182 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1697560 kB VmHWM. Under 2 GB.

## Next

The full `walk_chord` induction, `.ok` of Spec `walkChord` on the stated domain. A later live cell can enter `chord_add_live` through `RunFrame.hStart`. Then `walk_fform`; `base_point_of` (errors 963 and 1527, Demo non-vacuity only); `walk_key`, `exchange`, `receive_check`, `make_certificate`; `fold` / `fold_key`, `roll_key`, `call_in`.

The eight exports `base_point_of`, `walk_key`, `exchange`, `receive_check`, `make_certificate`, `fold`, `roll_key`, `call_in` are not tied.

`origin/main` at `884f1775` is merged. `HomeIn`, `BoardShape`, `Budget`, and `FieldLay.fits` are part 1's bundles. New statements should be readable off them: `OpenLay` is the homes and the control frame, `OpenMatch` is the one budget.

## Scope that stays in the PR body

- Success-branch reachability is not proved for Toy, Hobby, or Serious.
- SPEC.md gives the Hobby and Serious base points only as hashes.
- Future work, not started: proving `fieldInv` is the true field inverse, so inverses could be checked as one-multiply certificates.

## Proof rules that worked

- Restate the emitted stepper so the bridge is `rfl`. `markerOn` plus `@[simp] markerOn_flag` fixed the `noteBench_flag` goal that rejected a bare `rfl` on `{b with marker_on := true}`.
- Do not `simp` a `marker_on = false` or `bench_on = false` hypothesis into a board constructor. Use `log_op_off` / `settle_off` with the proof.
- `rw` is syntactic. `conv => lhs` when the rewrite also matches a dependent proof on the right. Change the school stepper to `rowStep` before rewriting `subI`. `simp only [markerOn_mk]` after `dsimp` turns `{ b with marker_on := true }` into `markerOn b`. `erw` matches `onto_up_prep` when the proof terms differ and `rw` does not. A whole-term `zeta` of `move_band` exceeds 200000 heartbeats because each record update copies the previous board into every field. Drop one let (`zeta1`), then `generalize` the board back to a variable.
- Opaque boards and projection lemmas. Never evaluate a concrete board at tier scale.
- Never `cases` a `Nat.le` proof. Keep `FitsLen` as a conjunct.
- Only axioms `propext`, `Classical.choice`, `Quot.sound`. No `native_decide`, no `sorry`, no heartbeat bump.
- A whole-term `rfl` of `Ecbs.mul` against an inlined schoolbook exceeds 200000 heartbeats. Reduce the board, then `change` the stepper to `rowStep` and the fold to `mulAfter`.
