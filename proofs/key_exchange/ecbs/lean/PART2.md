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

## Done toward `walk_chord`

`tally_max` and the climb high are not export results. `walk_key` returns a point. `receive_check` returns `Checked`; its peak, check-move delta, `tally_max`, and `control_highest` have to be named exactly, not as a natural. `call_in` returns the board, so its cost fields have to be named exactly too. The weakened `tmaxLt` and `openModelAt` stay inside the climb.

- `walkRun_walkGo`. A successful `walkRun` is Spec `walkGo` of the same point. `walkGo` is the walk Spec `walk_chord` is measured against.
- `chord_add_live` states the new point by the chord formulas, not by a `let` that hides them. The board high is still only a natural at least the origin, and that high is not an export result.

`walk_chord_zeros`, `walk_chord_white_open`, and `walk_chord_red_open` conclude Spec `walkGo` as well as the emitted `.ok`. That is the walk on an empty key, and on empty cells followed by one opening cell. A later live cell still has to rebuild `RunFrame` from the board `chord_add_live` returns. `chordStep_open` is the emitted step once `chord_add_demo` has returned; joining it to `chord_add_live` in one theorem elaborates past the heartbeat limit, so they stay separate.

4185 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. The sampled peak while this group's climb files were elaborated was 1702276 kB VmHWM. Under 2 GB.

## Done toward the next cell's row

`RowHome` is the control row below the tally origin: the painted ladder, except the parked hole is empty and the park hole holds that hole's painted colour. `rowHome_rung` is one park-and-tally step. `rowHome_clear` is unpark then `tally_clear`: if holes at and after the origin are blank on the painted row, and holes at and after the final tally are already blank, the row is the painted row again.

`ClimbBudget.baseRow` is that painted row. `basePark` and `baseZero` say the park hole and every hole from the origin on are empty. `ClimbInvK.rowHome` is the agreement, carried by `rowHome_carry` (`rowHome_rung`) at each rung. `parkEq` and `origin` name the park hole and the tally origin. `fromNePark` says a parked source is not the park hole. Entry and the open walk both start from `entry_row_home`.

`ClimbInvK.blankTail`: every hole at and after `t0 + tally` is empty. `rungRow_past` keeps it, because a rung writes only inside the length it leaves. At entry the tally is one peg, so the tail is `entry_past`. `climb_row_cleared` is `rowHome_clear` on that invariant: unpark and empty the current tally, and the row is `base.baseRow`. At the end of the ladder the current tally is the final one.

`unpark_painted`. `unpark_rung` leaves `unparkList`, and `rowHome_clear` of that list is `base.baseRow`. In `final_cube_settle` the final cube and the outer settle copy that row (`cubeOffBoard` and `settleBoard_plain`); `tally_clear` then writes `paintZero` of it.

`chord_tail_point` says the control row on the board `chord_tail` returns is the incoming row. The proof is the per-step row projections composed along the emitted tail. `gapMul_row` (`mulNoOffBoard`) and `settleBoard` cover the gap settle. `mul_refines` covers the square; its conclusion now includes the row. `benchAddBoard_row` and `settleBoard` cover the bottom settle. `addBoard_row` and `mirrorHome_row` cover the take. `ontoFoldBoard_row` covers the onto multiply. `moveBandBoard_row` and `settleBoard` cover the slide.

`final_cube_settle` says the board `tally_clear` returns has `base.baseRow`. That is `paintZero` of the list `unpark_rung` left, which `climb_row_cleared` names. `final_cube_both` exports the same row. On the open walk `OpenMatch.baseRow` is `paintedRow`. `open_check_mul` and `open_checked` carry it through the check multiply and `bench_read_and_clear`: the board `invert_checked` returns has `paintedRow`. `chord_add_live` does not yet return a `RunFrame`. The tail already keeps whatever row it is given.

4202 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Only `RowHome` was elaborated; its sampled peak was 416080 kB VmHWM. Under 2 GB.

4219 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded after `RowHome` was added to the climb invariant. Under 2 GB.

4224 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1698208 kB VmHWM. Under 2 GB.

4225 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1698104 kB VmHWM. Under 2 GB.

4231 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1704148 kB VmHWM. Under 2 GB.

4231 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1694052 kB VmHWM. Under 2 GB.

4231 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1699444 kB VmHWM. Under 2 GB.

4231 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1699728 kB VmHWM. Under 2 GB.

## Done toward the next cell's frame

`FrameScalar` is the ladder, its origin, the rung count, the park hole, parked-from, the rung index, the tally length, the tally origin, and `tally_max`. `mul_refines` returns it: a copy multiply writes the spare and the bench, and those nine fields stay. `tally_max` is the incoming value, not a closed formula. It is not an export result. `walk_key` returns a point.

`TailStay` is that scalar frame plus the tier and homes 3 and 4. The chord tail keeps it. `gap_settle_lay`, `square_white_lay`, `x3_settle_lay`, `chord_take_mirror`, the onto multiply, and `chord_up_slide` each return `TailStay`. `square_kept`, `bottom_lay`, and `chord_tail_point` compose them. The board `chord_tail` returns agrees with the rise board on the control frame and on the two base homes. `unpark_after_climb` keeps the ladder, its origin, the rung count, the park hole, and `tally_max`, and it still sets parked-from to `-1` and the rung index to `0`.

4268 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1677204 kB VmHWM. Under 2 GB. The earlier incremental build of the same tail proofs, with the heavy modules already built, peaked at 995000 kB.

`settled_unpark_frame` obtains `unpark_after_climb`, the inner `settle_refines`, `cube_refines`, the outer `settle_refines`, and `tally_clear_refines`. It is not folded into `final_cube_settle`. The board `tally_clear` returns keeps the climb board's ladder, ladder origin, rung count, park hole, and `tally_max`. Parked-from stays `-1`, the rung index stays `0`, the tally origin is the climb model's `t0`, and `tally_len` is `0`. `cube_refines` returns `FrameScalar`: the final cube writes a home, the bench, the marker flag, and some cost fields, and those nine scalars stay. `tally_max` on that board is still the climb board's incoming value, not a closed formula and not an export result. `walk_key` returns a point.

4278 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1668584 kB VmHWM. Under 2 GB.

`climbEmit_ladder` is the induction: one rung does not write the ladder array, so the board `climbEmit` returns has the ladder it was given. `open_invert` exports that the tally board's ladder is `embed (tierClimb t)`. `open_check_mul` obtains `settled_unpark_frame` and `FrameScalar` from the check multiply, so the board `bench_read_and_clear` returns has that same ladder. `open_checked` carries it through the white return and through `mirrorHome` of home 5. The board `invert_checked` returns has ladder `embed (tierClimb t)`.

`1 ≤ tally_max` is not read by `open_climb` or `chord_add_live`. The only use was the later arm of `tally_start_mark`, which called `tally_start_again`. `later_climb_entry` has no callers. The later branch of `OpenLay.hStart` and `RunFrame.hStart` is now `tallyOrigin ≤ high` alone. `tally_start_high` is that arm: the high stays, and `tally_max` becomes `max` of the old value and `1` without a positivity hypothesis. The partial `TmaxGe` induction is deleted.

4281 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 1700440 kB VmHWM. Under 2 GB.

Home 3 is the base. `ClimbBudget` stores that list and its held flag. `SideKeep` keeps the cell with homes 0, 1, and 4: a rung writes the gap and the spare, not index 3. `OpenLay` reads the cell off the board that enters `invert`. `open_tally` leaves it. `open_climb` puts it on the climb invariant. `open_check_mul` carries it through the check multiply and `bench_read_and_clear`. `open_checked` returns it, and the red branch keeps it through `mirrorHome` of home 5. The walk's copy sets that lay cell to the `RunFrame` base, held. A fresh board's home 3 stays empty.

4289 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 978160 kB VmHWM. Under 2 GB.

The board `chord_tail_point` returns has the three scratch homes empty. Home 2 and home 5 are the empty array and are not held: `chord_up_slide` clears the bottom and the gap, and `slide_point` now returns those four facts. Home 6 is not held. The square leaves it that way (`square_kept`, then `bottom_lay`), the take and the onto multiply do not write it, and the slide keeps it. `point_from_bottom` carries all three through to the tail.

4289 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 473232 kB VmHWM. Under 2 GB.

The board `open_checked` returns now also states the control frame a later cell reads. Ladder origin is `t.script + 2`, the rung count is `tierR t`, the park hole is `t.script + 2 + tierR t`, parked-from is `-1`, the rung index is `0`, the tally length is `0`, the tally origin is `tallyOrigin t`, and `tally_max` is a natural. `1 ≤ tally_max` is still not part of that statement. `chord_rise` keeps `TailStay` from the restored checked board, and `chord_tail_after_inv` returns that fact.

The closing slide does not write the marker, the script maximum, the control counter, the ops array, the strict peak, or the bench hole. It does return the move and slide counts, a natural peak, and held homes 0 and 1. The onto multiply sets ops slot 0 to one more than its input and leaves a natural strict peak and a natural bench hole. `chord_tail_point` returns marker `m + 3`, control `ctrl + 6`, script maximum `max (max (max mx (m + 2)) (m + 3)) (m + 4)`, and natural moves, slides, peak, strict peak, and bench hole. The move count is at most the incoming moves plus `tailMoveCap`. Homes 0 and 1 are held. Both arrays have size 8. Those counters are not yet the next `RunFrame`.

`settled_ops` is the ops array on the board `tally_clear` returns. It is the climb board's array with slot 1 replaced by one more than the value the cube read. The inner settle and the outer settle leave the array (`settle_ops`). The cube writes slot 1 (`cube_off_ops`, through `cube_refines`). `tally_clear` is `touchRow`, which does not write ops. `settled_unpark_frame` obtains those four facts. `final_cube_settle` stays closed, and the 200000 heartbeat limit stays. A climb step does not change the ops array's length, so `climb_refines_emit` returns that size. `open_check_mul` and `open_checked` then say slots 2 and 3 are naturals. Slot 2 is in range on the open board. Slot 3 is in range when the incoming board already has it. Each value `c` satisfies `c + 1 ≤ checkOpsCap base + 3`. The check multiply writes slot 0 and the cube writes slot 1, so those two slots are the climb's values.

4303 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. The resident peaks of the modules this change rebuilt are InvertWalk 799936 kB, ChordLay 1707620 kB, and ChordOpen 2736036 kB. ChordOpen is above 2 GB. The virtual limit held.

The chord tail turns the bench off. It writes ops slot 0 and leaves every other slot. Slot 0 becomes the value it was given plus 3. Slots 2 and 3 on that board are the slots `open_checked` returned, each a natural `c` with `c + 1 ≤ checkOpsCap base + 3`.

`ChordTailPoint` is `chord_tail_point` and the tail caps. `ChordRoom` is `TailRoom` and `tailRoom_of`. `ChordOpen` keeps the inverse and `chord_add_point`. That split is what brings every file under 2097152 kB. The first measurement of the split was ChordTailPoint 2045576 kB, ChordOpen 1143060, ChordRoom 1005748, ChordLive 494576, ChordNext 461580, EcbsLink2 439644.

`chord_rise` returns `bR.row = b.row`. `place` and `add` do not write the control row (`place_row`, `addBoard_row`). `chord_tail_after_inv` carries that equality through the restored marker.

4305 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Rebuilt peaks: ChordRise 293264 kB, ChordTail 266664, ChordCell 812988, ChordLay 1703676, ChordTailPoint 2020864, ChordRoom 1005820, ChordOpen 1143172, ChordLive 494652, ChordNext 461588, EcbsLink2 439780. All under 2097152 kB.

## Next

`chord_add_point` returns `TailPack`. It is the tail on the board `invert_checked` returned: the bench is off, `TailStay` and the control row survive the rise, slot 0 is three above the checked value, and every other ops slot stays. The move bound uses the rise board's move counter, `moves0 + pegCount baseY + pegCount accY`.

4327 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Rebuilt peaks: ChordOpen 1163016 kB, ChordLive 494812, ChordNext 461632, EcbsLink2 439892. All under 2097152 kB.

`chord_tail_point` was one `by` that obtained `bottom_lay` and then `point_from_bottom`. That file peaked at 2020864 kB, about 75 MB under the 2 GB gate. `ChordTailLay` is now `TailBottom` and `tail_bottom`: the bottom board, the counters `point_from_bottom` reads, and the equations that put those counters back on the move, slide, marker, control, script-max, ops, slope, and `chordX3` formulas. A projection out of the structure is not that formula. `chord_tail_point` obtains the witness and continues with `point_from_bottom`. No `set_option`.

4379 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Peaks of the files this split elaborated: ChordTailLay 864124 kB, ChordTailPoint 1542680, ChordRoom 1004668, ChordOpen 1163476, ChordLive 492040, ChordNext 450404, EcbsLink2 432940. ChordTailPoint is under about 1.8 GB. All are under 2097152 kB.

`chord_add_live` now returns `LiveLeft` and `TailPack`. `LiveLeft` is the control frame on the output board: tier, ladder, park, tally origin, homes 3 and 4, and `CheckedOps` at `checkOpsCap + 3`. The move bound is `checkMoveCap + 2 · n + tailMoveCap` because the rise's two homes sit on top of the check cap. Control is at most `checkCtrlCap + 6`, which is at most `liveCtrlRoom`. Ops slot 0 on the tail is three above the checked slot, and the ops array keeps its length. `copy_add_open` returns that length.

`chord_add_live_frame` needs one cell of fuel after this one. `fitRoom` and `fitCtrl` do not fit in a single `liveMoveRoom` or `liveCtrlRoom`. The output is a `RunFrame`: homes 0 and 1 are the new point, homes 3 and 4 are still the base, scratch 2, 5, and 6 are empty, and `hStart` is the later branch `tallyOrigin ≤ high`. `chordStep_from_live` obtains that frame and passes the demo equation to `chordStep_open`. The two proofs are separate. No `set_option`. The 200000 heartbeat limit stays.

4409 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Peaks: ChordTailLay 867952 kB, ChordTailPoint 1547700, ChordRoom 1006512, CopyLay 367640, ChordOpen 1327712, ChordFrame 493408, EcbsLink2 416208. ChordLive's successful elaboration of the `LiveLeft` return peaked at 481592 kB. All are under about 1.8 GB and under 2097152 kB.

`walkCharge` is `cellMoveCharge` plus `2 · n`, the rise's two homes. `cellsLeft i toN` is the cells still to run, including `i`. A cell with `cellsLeft ≥ 2` gives the frame `fuel = cellsLeft - 1`, so the extra cell is the next index. The last index has `cellsLeft = 1` and is `chordStep_live_last`: `chord_add_live` and `chordStep_open`, one charge, no next frame. `chordStep_live_cell` is that branch. `suffix_move_room` and `suffix_ctrl_room` carry the envelope down the suffix when each cell spends at most one charge. The frame's `1 ≤ fuel` is not a hypothesis of these theorems.

`demo_walk_room`, `toy_walk_room`, `hobby_walk_room`, and `serious_walk_room` are the shipped-tier room lemmas. Each says one cell past that tier's key, `(cells + 1)` times the move, slide, control, and op charge, fits an i64. The rung list is `demo_rungs` (and the three siblings); the inequality is `decide` on the numeral. No `native_decide`.

4451 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Peaks: WalkCharge 585124 kB, WalkLast 442456, WalkStep 447496, EcbsLink2 420840. All under about 1.8 GB and under 2097152 kB.

`cell_affine` is `marker_lift` then `frobenius_affine` on a live `RunFrame`. The output board is `cellOut`. `cell_to_frame` says homes 0 and 1 are `fieldCube` of the incoming point, the marker sits at 1, and the control counter is the incoming counter plus 4. `affine_home` says every other home is the home of the lifted board. `affine_card` says a projection the two settles and the two cubes do not write (the ladder, the row, the tally, the park) is that same board's projection. `frob_move_le_walk` puts one Frobenius, plus the three homes the next invert copies, inside one `walkCharge`. The same for slides, five control steps, and two op bumps.

`cell_run_frame` is that output as a `RunFrame` on the cubed accumulator. `held_kept` carries held flags other than 0 and 1, which the cubes and settles do not write. `ops_kept` carries every ops slot other than 1; slots 2 and 3 stay the incoming naturals, and `opsRoom` uses cap `opsCap + 2` because slot 1 grew by two. `cell_strict` and `cell_hole` are the values the up cube writes: `raisedPeak` of the across cube's strict, and `raisedHole` of its hole. The ladder, row, tally, and park are `affine_card`. Moves and slides are at most one `cubeCharge` and one `slideCharge`.

4550 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Peaks: CellRun 506052 kB, EcbsLink2 413476. All under about 1.8 GB and under 2097152 kB.

`demo_walk_span`, `toy_walk_span`, `hobby_walk_span`, and `serious_walk_span` sit inside those products. Each says `2 · cells + 2 ≤ cellOpsCharge`, the Frobenius move overhead `(6 · benchlen + 2 · n) · cells ≤ walkCharge`, `4 · n · cells ≤ cellSlideCharge`, `4 · cells ≤ cellCtrlCharge`, and both `7` and `benchlen` are at most `(cells + 1) · cellOpsCharge`. `frob_fits` turns a cell's counters (`moves ≤ done · (walkCharge + overhead)`, and the same shape for slides, control, and `ops ≤ done · (cellOpsCharge + 2)`, with `peakS ≤ 7` and `hole ≤ benchlen`) into `FitsLen (ops + 2)`, `FitsLen` of the two counters, and the chord's four rooms. `demo_frob_fits` and its three siblings supply the span and the room; those are not hypotheses.

`cell_run_frame` now also says the ops cap is the incoming cap plus 2, and strict and hole are `raisedPeak` and `raisedHole`. The across cube raises the incoming strict by `countHeld` of the eight held flags and the incoming hole by `topIdx` of the across comb. The up cube raises those again, by `countHeld` of the settled up board and by `topIdx` of the up comb. `held_seven` is `countHeld ≤ 7`. `comb_top_le` is `topIdx` of a comb at most `benchlen`. `TierWalk` is that span and those four rooms as one fact. `demo_tier_walk`, `toy_tier_walk`, `hobby_tier_walk`, and `serious_tier_walk` are the four shipped tiers. `tier_cell_frob` is the Frobenius step for any such tier: the four `FitsLen` checks are `tier_frob_fits`, the cubed frame has `peakS ≤ 7` and `hole ≤ benchlen`, and both of those are `FitsLen` of the ops product. `tier_cell_frob_zero` is the blank counters. `tier_cell_chord` is a non-final cell: `chord_add_live_frame` gets `chord_rooms`, and the frame it returns has ops cap `incoming + cellOpsCharge`, at most `(done + 1) · (cellOpsCharge + 2)`. Demo is not special in these statements.

`chord_add_live_frame` exports that ops cap, `moves ≤ incoming + walkCharge`, and `ctrl ≤ incoming + cellCtrlCharge`.

`gap_settle_lay` and `square_white_lay` say the strict they write is `raisedPeak` of the incoming strict by some `occ ≤ 7`, and the hole is `raisedHole` of the incoming hole by some top at most `bench`. `square_kept` composes the two. `ChordLay` is only that square. `bottom_lay` is `ChordBottom`: the strict it returns is `raisedPeak` of `raisedPeak` of the incoming strict, and the hole is the same shape. The point, the join, and the across-up step are `ChordPoint`. `TailBottom.strictForm` and `holeForm` are those two formulas. The onto multiply raises strict once more, by an `occ ≤ 7`. `chord_tail_point` puts that raise on top of the bottom's two, so `TailPack.strict` is three `raisedPeak`s of the strict that entered the tail. `raised_thrice_le` says those three stay at most 7 when the base is at most 7.

The climb keeps the same cap. `LivePeg.hpeakSB` is the peg loop's strict, at most `max` of the value it started from and 7. `RungDelta.strict` is one rung: the strict it leaves is at most `max` of the strict it read and 7. `ClimbBudget.peakS0` is the strict on the board the climb starts from. `OpenMatch.peakS0` says that is the open lay's strict. The copy leaves that equal to the `RunFrame`'s `peakS`. `ClimbInvK.strictLe` carries `peak_strict ≤ max peakS0 7` from rung to rung. A slide settle does not write strict.

`CheckRead.strictCube` is the final cube's raise: the strict it leaves is one `raisedPeak` of the climb board's strict, by a held-count of at most 7. `join_check_strict` puts the check multiply's raise on top of that. `mul_refines` raises once more, again by a count of at most 7, and `bench_read_and_clear` keeps the strict. The board `open_checked` returns therefore has strict at most `max lay.peakS 7`. `ClimbInvK.strictLe` and `OpenMatch.peakS0` are what tie that cap to the strict the climb started from. The copy sets `lay.peakS` to the incoming `RunFrame`'s `peakS`.

`TailPack.strict` names that checked strict as the base of its three raises. `chord_add_live_frame` takes `fr.peakS ≤ 7` and returns `fr'.peakS ≤ 7`. With that hypothesis the checked base is at most 7, and `raised_thrice_le` keeps the three tail raises there. The fact is sealed out of the local context before a later `omega`, because opening the exists makes the combo too wide.

`tier_cell_frob` and `tier_cell_chord` are the generic cell for every tier that has a `TierWalk`. Demo, toy, hobby, and serious are the four `*_tier_walk` facts. There is not a separate copy per tier. `tier_cell_frob` already returned `peakS ≤ 7`. `tier_cell_chord` now takes the same hypothesis and returns it on the frame the chord leaves, together with the ops cap.

4640 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded. Peaks of the modules this change elaborated, VmHWM: AfterClimb 712672 kB, InvertWalk 802760, EntryInv 535516, CopyLay 364852, ChordOpen 1319060, ChordLive 506064, ChordFrame 507656, WalkBound 608620, WalkCell 458764, WalkStep 449856, ChordPoint 1365020, ChordTailPoint 1598196, EcbsLink2 421792. The climb modules that this change did not edit were elaborated in the same limit by rebuilding their artifacts: Invert 508052, RungCharge 419528, ClimbEmit 1705768, SlideGap 335628, InvertDelta 478584, TightDelta 242840, InvertStep 1003400, HomeRed 645688, ParkStep 919828, OpenRed 740180, ClimbStep 374492. All under about 1.8 GB and under 2097152 kB.

The final cube's bench hole is `CheckRead.holeCube`: one `raisedHole` by a comb top, at most the bench. `join_check_hole` puts the check multiply's school-top raise on top of that and of `ClimbInvK.holeLe`. The board `open_checked` returns therefore has hole at most the bench. `TailPack.hole` is at most `max` of that checked hole and the bench, so `hole_under` keeps the tail's hole at most the bench. `chord_add_live_frame` and `tier_cell_chord` return `fr'.hole ≤ t.benchlen` together with `peakS ≤ 7`. The chord also returns `marker_on = true`, and the post-Frobenius frame's flags and point are the ones the next cell reads. `TierWalk.scriptRoom` is `4 < script`, which is the chord's `mark + 3 < script` once Frobenius has seated the marker at 1.

`built_strict` and `built_hole` are the initial board: both counters are 0. `frame_from_initial` reads a `RunFrame` whose strict and hole are still those values and concludes `peakS = 0` and `hole = 0`. `live_at_initial` is the first cell's frame. `peakS ≤ 7` and `hole ≤ bench` are that reading; the walk does not take either bound as a hypothesis. `live_cell` is one live cell, zero or white or red. A zero cell is Frobenius. A white or red cell is Frobenius then the chord, and the inverse is the one for the run that cell reaches. `walk_chord_live` is the loop from that first frame through `t.cells` entries. The state at the end has the homes `walkRun` reached, and the emitted loop is `chordAfter` of that state.

4681 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2.Link2.WalkInd` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 4681. Peaks of the modules this change elaborated, VmHWM: ChordTailPoint 1661196 kB, ChordOpen 1524664, ChordPoint 1412604, InvertWalk 830972, AfterClimb 701968, WalkBound 623752, WalkInd 616860, ChordFrame 516900, ChordLive 494208, WalkCell 460736. All under about 1.8 GB and under 2097152 kB.

`walk_chord_from` is that live loop starting at any index. `walk_chord_live` is the index-0 case: the first frame still reads `peakS ≤ 7` and `hole ≤ bench` off the initial board. `asc_resume` is the prefix of a loop whose every step continues, so the loop from 0 is the loop from the index where the prefix stopped.

The marker on `new_board` is already `-1`. `marker_lift` of that board is the board itself, and control does not move. `chord_fresh_white_down` and `chord_fresh_red_down` are the opening copy in that state. The two `place`s keep strict, hole, control, and slides. `walk_chord_zeros_down` is an empty key: the homes stay, the result is not live, and `walkRun` keeps the accumulator. `walk_chord_white_down` and `walk_chord_red_down` are the empty cells before that copy. Across becomes the base across. Up becomes the base up, or its negation when the cell is red. The marker is still `-1`. `walkRun` is that copied point.

`baseBoard` is `new_board` with the base point in homes 3 and 4. `openWhite` is the white copy of that point into homes 0 and 1, flag on, marker still `-1`. A `place` does not write the control row, the ladder, the park, the tally, the bench flag, or the marker flag.

4779 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 4779. Peaks of the modules this change elaborated, VmHWM: WalkInd 617180 kB, WalkPrefix 494208, WalkLoop 304312, OpenBoard 260364, WalkChord 247628, CopyMirror 235792, WalkCopy 222292, EcbsLink2 428580. The audit itself peaked at 895632 kB. All under about 1.8 GB and under 2097152 kB.

`whiteRec` is that white opening as a record: homes 0 and 1 hold the base point, the flag is on, and the marker is still `-1`. The board with the marker at `0` and control `tierR − 1` is a private proof device. `seat_white` and `seat_white_at` do not name it. `seat_white` says `frobenius_affine` of `whiteRec` returns a `RunFrame`, with control `tierR + 3`, `peakS ≤ 7`, and hole at most the bench. `seat_white_at` is the `LiveAt` at one cell, the cube of the copied point.

`redRec` is the red opening. Home 1 is `embed (mirrorTrits y)`. The move counter matches the white copy, because `pegCount_mirror` says the negated up has the same number of pegs, and the peak does not read the coefficients. `seat_red` and `seat_red_at` are that seat. The cubed up is `fieldCube` of the negated base up. Their statements do not name the early-marker board either.

`seat_white_chord` and `seat_red_chord` are that cell when it is not last. Frobenius seats the marker, then `chord_add_demo` is `walkStep` on the copied point, and the board it leaves is `LiveAt` at `done + 1`. `done` is the cell's index. The opening counters sit under one charge, so a later index only widens the bound. `seat_white_last` and `seat_red_last` are the same cell when it is last: the homes are the point `walkStep` names. The inverse of the cubed run is a hypothesis of these four lemmas. The full walk still has to take it from `walkRun = some`. None of the four names the early-marker board.

4983 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 4983. Peaks of the modules this change elaborated, VmHWM: SeatDown 541660 kB, SeatChord 472584, EcbsLink2 429232, OpenBoard 292004. The audit peaked at 899720 kB. All under about 1.8 GB and under 2097152 kB.

`walk_chord_base_zeros` is an empty key on `baseBoard`: the homes stay, and the result is not live. `walk_chord_base_white` and `walk_chord_base_red` are a key whose only nonzero cell is the last one. Across becomes the base across. Up becomes the base up, or its negation when that cell is red. `walkRun` is that copied point.

4999 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 4999. Peaks of the modules this change elaborated, VmHWM: WalkJoin 457692 kB, EcbsLink2 419816. The audit peaked at 900096 kB. All under about 1.8 GB and under 2097152 kB.

`white_copy_kept` is the opening copy on an abstract board. Each field the two `place`s do not write is `place_*` of the board the copy started from. `placeBoard` stays irreducible there, so the projection is not reduced. `OutLay` is that board. `seat_out` is Frobenius of it: control is `tierR + 3`, `peakS ≤ 7`, and the hole is at most the bench. The early marker is private and is not in the statement. `base_in_lay` says `chordFlag` of `baseBoard` is the input. `seat_base_white` is that copy and then the seat, a `LiveAt` at one cell. `seat_base_chord` and `seat_base_last` run the chord as well. The inverse of the cubed run is still a hypothesis of those two. `live_chord_inv` reads it off a successful live `walkStep`, which is how `walk_chord` will discharge it.

5099 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5099. Peaks of the modules this change elaborated, VmHWM: CopySeat 526892 kB, EcbsLink2 431956, CopyKeep 267380. The audit peaked at 902892 kB. All under about 1.8 GB and under 2097152 kB.

`walkRun_at` is the cell a successful run actually stepped. `walkRun_live_inv` is the inverse at a live white or red cell of that run, by `live_chord_inv`. The final `walk_chord` uses this instead of an inverse hypothesis.

5104 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5104. Peaks of the modules this change elaborated, VmHWM: WalkRunInv 450396 kB, EcbsLink2 448644. The audit peaked at 903364 kB. All under about 1.8 GB and under 2097152 kB.

`red_copy_kept` is the red opening on that same abstract board. Home 1 is `embed (mirrorTrits y)`. `walk_reach_white` and `walk_reach_red` are the emitted loop through the empty cells and that copy, when at least one cell remains. The loop from index 0 is the loop at the seat cell, on the copied board.

5109 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5109. Peaks of the modules this change elaborated, VmHWM: WalkReach 478236 kB, EcbsLink2 432772, CopyKeep 265200. The audit peaked at 904164 kB. All under about 1.8 GB and under 2097152 kB.

`walk_chord_success` is the success direction. If `walkRun` of the key is `some (true, (px, py))`, then `Ecbs.walk_chord` on `baseBoard` is `.ok ((true, true), b')`, home 0 is `embed px`, and home 1 is `embed py`. A key whose only nonzero cell is the last one is `walk_chord_base_white` or `walk_chord_base_red`. A longer key reaches the copied board by `walk_reach_white` or `walk_reach_red`, runs that seat cell (`seat_out`, then a cube or `seat_cell_chord` / `seat_cell_last`), and continues with `walk_chord_from` when a cell remains. The inverse is `walkRun_live_inv` of the successful run. `chord_after_nat` is the closing lift: the marker is a natural, one more control step fits, and the homes stay. `chord_add_live` exports that marker and that fit.

5132 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5132. Peaks of the modules this change elaborated, VmHWM: WalkInd 590968 kB, WalkSeat 528912, ChordFrame 522236, CopySeat 505008, ChordLive 499304, SeatChord 470356, WalkLast 442992, EcbsLink2 426948. The audit peaked at 905692 kB. All under about 1.8 GB and under 2097152 kB.

`walk_chord_cases` is the walk on the domain: every cell is `0`, `1`, or `2`, with `TierWalk`, `BoardOk`, `TierSat`, `TierShape`, and `0 < tierR`. There are three results.

`walkRun = some (false, acc')` never goes live. `walk_chord_idle` says every cell is `0`, `acc' = acc`, and `Ecbs.walk_chord` is `.ok ((false, true), {baseBoard with marker_on := false})`. The homes stay.

`walkRun = some (true, (px, py))` is `walk_chord_success`: `.ok ((true, true), b')`, home 0 is `embed px`, and home 1 is `embed py`.

`walkRun = none` is `walk_chord_none`. The first refused cell is live and white or red, and `fieldInv` of that run is `none`. An all-zero run is Spec `walkStep = none` and the emitted walk `.ok ((true, false), {bA with marker_on := false})`. Both refuse a point. A nonempty run whose inverse is missing is `.error e` with `e.kind = "AssertFailed"` and detail `s!"line {728}"`, or `s!"line {730}: {SudoRt.Canon.canon (Int.ofNat d)} != {SudoRt.Canon.canon (0 : Int)}"` for a nonzero `d`. The refusal at the seat index is `seat_is_fail`. A later cell is `land_seat`, then `live_until`, then `frame_is_fail`. `invert_checked` on that walk board is `invert_checked_lay_none`.

5188 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5188. Peaks of the modules this change elaborated, VmHWM: WalkFail 532944 kB, WalkSeat 528880, WalkCase 528624, EcbsLink2 353308. The audit peaked at 909932 kB. All under about 1.8 GB and under 2097152 kB.

`walk_fform_eq` is the emitted F-form walk: `Ecbs.walk_fform` is `walkFformGo` by `rfl`. The loop is the chord walk's loop, with line 788 as the trit check. `fformStep_zero` is an empty cell while the accumulator is not live: only the marker lifts. `fformStep_fresh` is a white or red cell in that state, and `start_walk` is the copy. `fformStep_point` is a live zero cell, and `frobenius_point` is the cube. `fformStep_add` is a live white or red cell whose `fform_add` returns the new point. `fformStep_reroll` is that cell when `fform_add` returns false: `.ok (Flow.ret ((true, false), {bA with marker_on := false}))`. Those three calls stay hypotheses of the cell. The whole walk is not yet `walkRun`.

5198 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5198. Peaks of the modules this change elaborated, VmHWM: WalkFform 353312 kB. The audit peaked at 909928 kB. All under about 1.8 GB and under 2097152 kB.

`white0_fresh` is an empty home with the bench off. `Ecbs.white0` plants `whiteHole0`, marks the home held, adds one peg to the move counter, and `note_peak` raises the peak. That is the peg `start_walk` writes into the bottom. The two opening copies, `frobenius_point`, and `fform_add` are still hypotheses of the cell steps, so the whole `walk_fform` is not yet `walkRun`.

5206 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5206. Peaks of the modules this change elaborated, VmHWM: FformOpen 353340 kB. The audit peaked at 910760 kB. All under about 1.8 GB and under 2097152 kB.

`start_walk_white` and `start_walk_red` are the two copies inside `start_walk`, then the bottom peg. On an `InLay` board, across becomes the base across and up becomes the base up, or `mirrorTrits` of it when the cell is red. The bottom is `whiteHole0`. The move counter is the two peg counts plus one. The bench stays off and the tier stays `embTier`.

5213 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5213. Peaks of the modules this change elaborated, VmHWM: FformStart 353312 kB. The audit peaked at 911220 kB. All under about 1.8 GB and under 2097152 kB.

`frobenius_point_cubes` is the emitted point: across, then up, then the bottom, each cubed into itself. `point_across_up` is the first two. On a `DownAcross` board they leave `upFlag`: the bench is on, aimed at up, and holds the cubed up.

5215 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5215. Peaks of the modules this change elaborated, VmHWM: FformPoint 353336 kB. The audit peaked at 910736 kB. All under about 1.8 GB and under 2097152 kB.

`point_bottom` is the bottom cube on that board. The bench still holds the cubed up and is aimed at up, so the cube settles the up and then folds the bottom. It is `cube` of `markerUpFeed` with the marker at 1, control `ctrl + 3`, and script maximum `max (max mx 1) 2`, and the marker flag stays on. `bottom_held` and `bottom_home` say held 2 and home 2 are the bottom the across cube left on `b1On`: the up cube writes home 1 and settles home 0. `frobenius_point_bottom` is the emitted point, the across cube and the up cube and then that bottom cube.

5235 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5235. Peaks of the modules this change elaborated, VmHWM: FformPoint 353340 kB. This `lake build EcbsLink2` peaked at 387104 kB. The audit peaked at 912224 kB. All under about 1.8 GB and under 2097152 kB.

`held_copy_school` is the copy inside the run multiply. `mulFromHeld` with `copy_second` and the mirror off copies the second home into the spare, and the schoolbook reads that copy. The second home stays. The strip is `pad`, and what is laid on it is `school` of the first home by the second.

5241 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5241. Peaks of the modules this change elaborated, VmHWM: FformAdd 353316 kB. This `lake build EcbsLink2` peaked at 435296 kB. The audit peaked at 912164 kB. All under about 1.8 GB and under 2097152 kB.

`run_onto_copy` is that multiply with the bench off. It settles nothing, copies the destination onto a zero strip, then `held_copy_school`. The length-`n` pad is the destination home. The product laid on it is `school` of the first home by the second. The destination ends empty. The second home stays, because the schoolbook read the spare.

5245 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5245. Peaks of the modules this change elaborated, VmHWM: FformAdd 353332 kB. This `lake build EcbsLink2` peaked at 387300 kB. The audit peaked at 912244 kB. All under about 1.8 GB and under 2097152 kB.

`run_onto_settles` is the settle in front of that multiply. The bench is on and aimed at `seat`, and `seat` is not the destination, so the onto-keep test fails. `Ecbs.mul` settles the bench and then multiplies. Settling first leaves the same multiply: the second prologue sees the bench off. `run_onto_at` is that settled board. `run_onto_off` is the bench-off multiply, the op bump and then `run_onto_copy`. The marker is off in all three.

5250 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5250. Peaks of the modules this change elaborated, VmHWM: FformAdd 353324 kB. This `lake build EcbsLink2` peaked at 425256 kB. The audit peaked at 912736 kB. All under about 1.8 GB and under 2097152 kB.

`run_marker_seat` is the marker step after `frobenius_point`. The marker is on, the bench is on, and the bench is aimed at `seat`, which is not the multiply's destination. `log_op` is `marker_step`. The onto-keep test fails, so `Ecbs.mul` continues as `mulElse` on `markerOn (bumpOp (markerUpFeed b))`. The flag stays on. The mirror flag of this multiply is the constant `false`.

5251 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5251. Peaks of the modules this change elaborated, VmHWM: FformAdd 353208 kB. This `lake build EcbsLink2` peaked at 388368 kB. The audit peaked at 912968 kB. All under about 1.8 GB and under 2097152 kB.

`mul_onto_school` and `held_copy_school` take the mirror flag. `run_onto_copy`, `run_onto_off`, `run_onto_settles`, `run_onto_at`, and `run_marker_seat` pass that flag through. The run supplies the constant `false`. The rise supplies the constant `false` on a white cell and the constant `true` on a red cell. The schoolbook proof does not case on the flag.

`run_else_flag` is the settle inside that `mulElse`. The bench is aimed at `seat`. The marker flag is not read, so it stays on, and the multiply that follows is `mulElse` of `markerOn (settleBoard ...)`. `run_marker_else` is the marker step and then that settle. `Ecbs.mul` equals that flagged settle's `mulElse`.

`rise_marker` is the rise. `Ecbs.mirror` negates the home, then the onto multiply steps the marker. The mirror flag of that multiply is the constant `mirror`. Negating the home does not move the bench, the marker, or the op counter, so `run_marker_seat` applies to `mirrorHome`.

`off_marker` is a gap multiply, where `onto` is the constant `false`. The keep test does not read the bench. `log_op` is still `marker_step`, and the multiply continues as `mulElse` on the flagged board. `copy` and `mirror` are not inspected. `mul_else_flag` is the settle inside that `mulElse`, again with `onto` false. `off_marker_else` is the marker step and then that settle.

5258 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5258. Peaks of the modules this change elaborated, VmHWM: FformAdd 386564 kB, FformGap 386848 kB. The root rebuild peaked at 1645036 kB. The audit peaked at 914576 kB. All under about 1.8 GB and under 2097152 kB.

`copy_else_off` is that `mulElse` once the bench is off. `onto` is false and `copy_second` is true, so it aims a zero strip at the destination and `held_copy_school` lays `school` of the first home by the second on that strip. The mirror flag is `mirror`. A gap multiply has this shape after `off_marker_else` settles the previous bench.

5260 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5260. Peaks of the modules this change elaborated, VmHWM: FformAdd 386452 kB. The root rebuild peaked at 387608 kB. The audit peaked at 913812 kB. All under about 1.8 GB and under 2097152 kB.

`nocopy_else_off` is the same settle-and-aim with `copy_second` false. `mul_onto_school` lays `school` on the zero strip. The later gap lines, and the first multiply of the new across and the new up, have this shape. The mirror flag is `false` except the new up, which passes the constant `true`. `zero_school_mul` says that strip, with the mirror flag off, folds to `fieldMul`: `laneFold` is `reduceStrip`.

5262 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5262. Peaks of the modules this change elaborated, VmHWM: FformAdd 388732 kB, FformGap in that same rebuild. The root rebuild peaked at 410688 kB. The audit peaked at 915092 kB. All under about 1.8 GB and under 2097152 kB.

`fformGap` is that schedule as one field value: the bottom times the square of the rise, plus the run times its own square, plus the square of the run times the bottom. `fformGap_order` commutes the squared factors, so the card's order is `u² Z + v³ + v² Z`. `fformZ3` is the new bottom, the run times that spare-bottom product. `fformX3` is the new across, the gap times the run plus base across times `Z₃`. `fformX3_order` swaps the first of those products, which is `v F + x₂ Z₃`. `fformY3` is the new up on a white cell: the gap times the up, mirrored, plus base up times `Z₃`, mirrored. `fformY3Red` is the red cell. The gap-times-up product stays mirrored, and `not red` leaves the base-up product unmirrored.

5266 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5266. Peaks of the modules this change elaborated, VmHWM: FformField 380516 kB. The root rebuild peaked at 404884 kB. The audit peaked at 914372 kB. All under about 1.8 GB and under 2097152 kB.

`walk_fform_zeros` is an empty key with the marker already `-1`. `Ecbs.walk_fform` only lifts the marker. The homes stay, the result is `.ok ((false, true), {b with marker_on := false})`, and `walkRun` is `some (false, acc)`. `walk_fform_idle` is that walk on `baseBoard`. `TierWalk` supplies `FitsLen` of the cell count. This is the dead run. The live point and the `none` run are still open.

5272 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5272. Peaks of the modules this change elaborated, VmHWM: the root rebuild 387168 kB. The audit peaked at 915024 kB. All under about 1.8 GB and under 2097152 kB.

`fformGap`, `fformZ3`, `fformX3`, `fformY3`, and `fformY3Red` are helpers for the card's multiply order. Each one is proved equal to the formula in SPEC.md §3 R7, so a later theorem can cite Spec and not these helpers. `fformZ3_spec` is the new bottom `v · (v²Z)`, by `rfl` with `fformBottom`. `fformGap_spec` is `F = u²Z + v²(v + Z)`: the card's sum `u²Z + v³ + v²Z` is that product because `fieldMul` distributes over `fieldAdd` on the right. `fformX3_spec` is `v·F + x₂·Z₃`. `fformY3_spec` is `−(u·F + y₂·Z₃)`. `fformY3Red_spec` is that same new up at `−y₂`. `fformMir` is `mirrorTrits` of `fieldMul`, not a second product. Spec's run and rise are `fformRun` and `fformRise` in `SpecBase`.

5349 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5349. Peaks of the modules this change elaborated, VmHWM: FieldLin 384804 kB, FformField 386084 kB. The root rebuild's highest module was ChordTailPoint 1649672 kB, then ChordOpen 1500860 kB and ChordPoint 1393572 kB. The audit peaked at 915496 kB. All under about 1.8 GB and under 2097152 kB.

`nocopy_else_field` is a bench-off multiply that is not onto and not a copy, with the mirror off. The length-`n` bench prefix is `fieldMul`. A gap line has this shape, and so does the first multiply of the new across and of the new up when that mirror flag is off. `run_else_field` is the run multiply: onto, copying the second home, mirror off. The prefix is `fieldAdd` of the destination and `fieldMul` of the two factors. `run_is_fformRun` is that prefix once the destination is `mirrorTrits` of the across: SPEC.md §3 R7 line 149, `v = x₂Z − X`. `bench_is_zero` reads that bench. The flag is whether the run is the zero home, which is the reroll. `onto_add_mirror` is the same onto product with the schoolbook mirrored: the home plus `mirrorTrits` of `fieldMul`. A red rise lays that. The rise on the board, the gap, and the new point are not this theorem yet.

5358 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5358. Peaks of the modules this change elaborated, VmHWM: FformAdd 386616 kB, FformFold 386756 kB. A later elaboration of FformFold peaked at 353340 kB. The audit peaked at 916560 kB. All under about 1.8 GB and under 2097152 kB.

`run_else_lane` is the onto copy with the mirror flag left open. The bench is the lane fold of `school` on the destination. `run_else_field` is that fold with the flag off, so the prefix stays `fieldAdd` of the home and `fieldMul`. `rise_lane_spec` is the length-`n` prefix of the rise schoolbook laid on `mirrorTrits` of the up. That prefix is `fformRise`, SPEC.md §3 R7 line 150. White passes `y₂`. Red passes `mirrorTrits y₂`: the mirrored schoolbook is `fieldMul` of the negated base up. `rise_on_board` is the emitted rise. `Ecbs.mirror` negates the up, then `Ecbs.mul` lays base up times the bottom onto it, with that constant mirror flag. The bench aimed at `seat` settles first. The new bench prefix is that `fformRise`.

5364 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5364. Peaks of the modules this change elaborated, VmHWM: FformAdd 356288 kB, FformRise 278204 kB, EcbsLink2 334580 kB. The audit peaked at 917520 kB. All under about 1.8 GB and under 2097152 kB.

`copy_else_field` is a bench-off multiply that copies the second home, with the mirror off. The length-`n` bench prefix is `fieldMul`. The marker, the tier, and the slides stay. The bench ends on, aimed at the destination, and the peak stays when it was already at least 7. `gap_u2` is the first gap line on that board. The bench holds the rise and is aimed at the up, so `Ecbs.mul` of the gap by the up, copying the up, settles the rise first. The new bench prefix is `fieldMul u u`. `gap_u2z` settles that square into the gap and multiplies the bottom by it. The bench prefix is `fieldMul z u²`. SPEC.md §3 R7 line 151 writes the factor `u²Z`.

5376 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5376. Peaks of the modules this change elaborated, VmHWM: FformAdd 364156 kB, FformGap 242336 kB, FformFold 260512 kB, FformRise 262260 kB, FformGapLay 269552 kB, EcbsLink2 428228 kB. The audit peaked at 919020 kB. All under about 1.8 GB and under 2097152 kB.

`gap_v2` settles the bench into the gap and squares the across. The bench prefix is `fieldMul v v`. `gap_v2z` settles that square into the spare and multiplies it by the bottom. The bench prefix is `fieldMul v² z`.

5378 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5378. Peaks of the modules this change elaborated, VmHWM: FformGapLay 283272 kB, EcbsLink2 353328 kB. The audit peaked at 920172 kB. All under about 1.8 GB and under 2097152 kB.

`gap_keep` is the onto multiply whose bench is already aimed at the destination, with that home empty. The keep test uses the bench as the strip. The marker steps, then `mul_onto_school` lays the two factors on that strip and the fold is `fieldAdd` of the bench prefix and `fieldMul` of the factors. The chord's onto multiply takes the other branch, copying a held home onto a fresh strip; this one keeps the bench. For the gap the prefix is `u²Z` and the factors are `v` and `v²`, so the sum is `u²Z + v³`.

5379 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5379. Peaks of the modules this change elaborated, VmHWM: FformGapLay 326980 kB. The audit peaked at 921436 kB. All under about 1.8 GB and under 2097152 kB.

`add_off` is `Ecbs.add` with the mirror flag off. Both homes are held. The destination becomes `fieldAdd` of the two homes, and the move counter grows by `pegCount` of the source. `gap_fform` is the sum `(u²Z + v³) + v²Z = fformF`: the squared run distributes over `v + Z`, and addition associates. `gap_add_f` is that add on those two homes. The result is `embed (fformF ...)`.

5402 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5402. Peaks of the modules this change elaborated, VmHWM: FformAddOff 220204 kB. The audit peaked at 921728 kB. All under about 1.8 GB and under 2097152 kB.

`settle_nocopy` is one settle and one nocopy multiply. The bench was aimed at `seat`, not at the destination, so that prefix is written home and the new bench is `fieldMul` of the two factors, or `mirrorTrits` of it when the mirror flag is on. The second home is cleared. Every other home stays. `fform_new_bottom` is that multiply for the new bottom: the gap held `F` on the bench, the bottom held `v²Z`, and the bench prefix is `fformBottom`. `fform_bottom_step` is the emitted `mul bottom across bottom`. The gap home is `fformF`. Across, up, base across, and base up stay. `keep_copy` is the onto multiply that keeps the bench and copies the second factor into the spare. The spare ends empty. Every other home stays. The prefix is `fieldAdd` of the bench and the product, or of the bench and `mirrorTrits` of the product. `across_sum` is that sum at `F·v` and `x₂·Z₃`, which is `fformAcross`. `up_white` is both products mirrored, which is `fformUp`. `up_red` leaves the base-up product unmirrored, which is `fformUp` at `−y₂`. `zeroTail_pref` turns a zero tail into the pad `keep_copy` reads.

5510 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. This `lake build EcbsLink2` under `ulimit -v 7000000` succeeded, and `lake env lean Axioms.lean` audited 5510. Peaks of the modules this change elaborated, VmHWM: FformPointLay 361168 kB, FformPointKeep 386632 kB, FformPointDo 386868 kB, EcbsLink2 390460 kB. The audit peaked at 925308 kB. All under about 1.8 GB and under 2097152 kB.

The composed suffix, the `F·v` multiply through `clear`, is not one theorem yet. `keep_copy` and `settle_nocopy` are the two steps it obtains.

Still open: that composed suffix, then the `none` run and the three-way `walk_fform`; `base_point_of` ↔ `Spec.basePoint` (lines 963 and 1527 ↔ `none`), with Demo non-vacuity; `walk_key`, `exchange`, `receive_check` (counters exact), `make_certificate`, `fold` / `fold_key`, `roll_key`, `call_in` (cost fields exact). The exported theorems discharge `TierWalk`, `BoardOk`, `TierSat`, and `TierShape` for the four shipped tiers. An empty key does not write the accumulator into the homes. The live point cites Spec, not the card helpers.

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
