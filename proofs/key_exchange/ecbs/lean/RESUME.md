# RESUME

ECBS Link 2, branch `cursor/ecbs-link2-4113`. Pick up from this note.

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

## Next

The last multiply (`mul` of the up by the gap onto the up). That is the `onto = true` arm. It is what makes a successful later white or red cell match `chordAdd`. The inverse on a walk board is still a hypothesis (`invert_checked_some` is `bottomBoard`). Then discharge the settle `FitsLen` hypotheses inside the cell invariant, discharge the inverse with `invert_checked`, and the full `walk_chord` induction over cells, for every key length and colour sequence, with the live/ok flag and the error branch, and no hypotheses beyond the stated domain. After that: `walk_fform`; the root-strip search (`base_point_of`, errors 963 and 1527, Demo non-vacuity only); `walk_key`, `exchange`, `receive_check`, `make_certificate`; `fold` / `fold_key`, `roll_key`, `call_in`.

## Scope that stays in the PR body

- Success-branch reachability is not proved for Toy, Hobby, or Serious.
- SPEC.md gives the Hobby and Serious base points only as hashes.
- Future work, not started: proving `fieldInv` is the true field inverse, so inverses could be checked as one-multiply certificates.

## Proof rules that worked

- Restate the emitted stepper so the bridge is `rfl`. `markerOn` plus `@[simp] markerOn_flag` fixed the `noteBench_flag` goal that rejected a bare `rfl` on `{b with marker_on := true}`.
- Do not `simp` a `marker_on = false` or `bench_on = false` hypothesis into a board constructor. Use `log_op_off` / `settle_off` with the proof.
- `rw` is syntactic. `conv => lhs` when the rewrite also matches a dependent proof on the right. Change the school stepper to `rowStep` before rewriting `subI`.
- Opaque boards and projection lemmas. Never evaluate a concrete board at tier scale.
- Never `cases` a `Nat.le` proof. Keep `FitsLen` as a conjunct.
- Only axioms `propext`, `Classical.choice`, `Quot.sound`. No `native_decide`, no `sorry`, no heartbeat bump.
- A whole-term `rfl` of `Ecbs.mul` against an inlined schoolbook exceeds 200000 heartbeats. Reduce the board, then `change` the stepper to `rowStep` and the fold to `mulAfter`.
