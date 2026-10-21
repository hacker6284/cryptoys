<!-- Owns: the scope of the ECBS Link 2 proofs (proofs/key_exchange/ecbs/lean) and their export table. Maintenance rules: ../../../../DOCS.md. -->
# ECBS Link 2, part 1: exports with a finished refinement

Status: **part 1.** This branch proves that the code `sudoc` emits from [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) (in [`Generated/`](Generated/README.md)) computes what the hand-written model in [`EcbsLink2/Spec.lean`](EcbsLink2/Spec.lean) says, for the exports in the table whose refinement is finished. A finished refinement states its domain and leaves no hypothesis past that domain. Each success branch has a Demo witness. The chord walk, the key walk, and the exports the table marks as not tied stay on branch `cursor/ecbs-link2-part2`. It is **correctness of the emitted code on that domain, not a security claim**: nothing here says the curve's discrete log is hard, that a key has entropy, or that the fold extracts.

Part 2 of this branch continues in [`PART2.md`](PART2.md). It has tied `walk_key` (the seated board and the walk), `fold`, `roll_key`, `exchange`, `receive_check`, `make_certificate` (the chord, not the identity `π(C) − C`), and `call_in`. `base_point_of` is still open. That note is the handoff. It is not a second export table. After the merge of part 1, this branch's `EcbsLink2` build is 4022 theorems.

`curve_test_refines` is the exported curve test on `FieldLay` and `TierSat`, for two length-n trit lists. `demo_curve_zero_one` is that call on Demo at the zero across and the one-peg up, and it returns true. `invert_number_refines` is the exported inverse when the spec inverse returns a list. `invert_number_none` is the assert when the spec inverse returns none. `demo_invert_one` is the one-peg list on Demo, returned as its own inverse. `multiply_refines` and `cube_number_refines` are the exported field operations on `FieldLay`; the cube also needs the comb reach. `demo_multiply_one` and `demo_cube_one` run those exports on Demo's one-peg list and return that list. `demo_new_board` is a fresh Demo board. `demo_coordinate_origin` is coordinate of home 0, hole 0 on Demo.

`demo_basePoint` is the spec base point on Demo, equal to the coordinate pair written in SPEC.md §5.1. `frobenius_affine_refines` cubes the across home and the up home on a board that already holds those two length-n trit lists, with the marker off, the bench off, and the move and slide counters inside the stated bounds. It is not an export. `base_point_of` is not this theorem.

Demo also has one non-unit witness for each of `multiply` and `invert_number`. `negPeg` is a red peg in hole 0 (the constant `2`, not the unit). `demo_invert_neg` is `invert_number_refines` on that peg, and the export returns the same peg. `demo_multiply_neg` is `multiply_refines` on that peg times itself, and the export returns the unit. `hole1Peg` is a white peg in hole 1. `demo_invert_hole1` is `invert_number_refines` on that peg, and the export returns `hole1Inv`, a different list. `demo_multiply_hole1` is `multiply_refines` of that peg by `hole1Inv`, and the export returns the unit. The two steps of the Demo climb are kernel `decide`; nothing raises the heartbeat or recursion limit.

Toy, Hobby, and Serious each have a success witness for the unit (`toy_invert_one`, `hobby_invert_one`, `serious_invert_one`, and `toy_curve_zero_one`, `hobby_curve_zero_one`, `serious_curve_zero_one`). What those tiers do not have is the published base points, and inputs other than the unit. SPEC.md gives the Hobby and Serious base points only as hashes. Proving that `fieldInv` is the true field inverse is future work, not started.

The climb inside the inverse uses this room. The numbers are the model's final tally and the control-row room, not a claim about the unfinished exports:

| Tier | Final tally T | Row room |
| --- | --- | --- |
| Demo | 3 | 6 |
| Toy | 11 | 18 |
| Hobby | 29 | 57 |
| Serious | 89 | 175 |

Build and audit (Lean 4.14.0, no Mathlib):

```sh
cd proofs/key_exchange/ecbs/lean
lake build                                       # EcbsLink2 (and the emitted Generated/)
python3 ../../../doubledeal/check_axioms.py ecbs # every EcbsLink2 theorem: propext, Classical.choice, Quot.sound only
python3 ../../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
```

No `sorry`, no `native_decide`, no `axiom`. Tier names and the four tiers' `BoardOk` / `GridOk` / `FoldOk` facts use `decide` and `decide!` (kernel evaluation, no extra axiom), split per tier. A clean `lake build EcbsLink2` under `ulimit -v 7000000` succeeds: 3027 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only. The largest file is `EcbsLink2/Link2/ClimbEmit.lean`, compile peak (VmHWM) 1749256 kB. No `maxHeartbeats` or `maxRecDepth` option is set. The 2 GB per-file cap and that clean build are checked by the weekly workflow [`.github/workflows/ecbs-link2-mem.yml`](../../../../.github/workflows/ecbs-link2-mem.yml) (`workflow_dispatch` and a Monday schedule), not by the pull-request `ecbs-lean` job.

## Generated Lean

[`Generated/`](Generated/README.md) is emitted from `ecbs.sudo` by `proofs/emit_lean.sh ecbs` under the terminates gate. Its TAP runs every sudo `test` (`ecbs_test`). That is evidence the emitter ran, not a theorem.

## The model

[`EcbsLink2/Spec.lean`](EcbsLink2/Spec.lean). A register is a `List Nat` of trits. `embTier` / `embed` send a model tier or register to the emitted record.

- `Spec.demo`, `Spec.toy`, `Spec.hobby`, `Spec.serious`: the §1 table, names as ASCII bytes.
- `Spec.coordinate`: §5.2. Demo uses the fixed lane table; the other tiers use `geoper` bands, and `geodouble` splits a column at 10.
- `Spec.keypadFirst` / `Spec.keypadSecond`: §4, faces `1 .. 9`.
- `Spec.flipTrit`, `Spec.phaseNames`, `Spec.opNames`.
- `Spec.rungList` is the ladder `new_board_refines` paints into the control row, in build order. `Spec.fieldInv` follows the emitted climb (rung order, the tally, the final cube, the hole-0 check) and returns `none` when that check's product is not one peg in hole 0. It does not prove the product is one under `Spec.fieldMul`. `Spec.foldKey` / `Spec.rollKey` are the SPEC's fold and row cup. `fold_refines` and `roll_key_refines` are the emitted functions on the domains in the table.

`GridOk` is the coordinate domain (non-Demo `w` and `geoper` positive, the products fit an i64). All four published tiers meet it. `BoardOk` is the domain of `new_board_refines`: `0 < n`, the script and control products fit an i64, and the ladder indices fit the control row. `FoldOk` is the same kind of arithmetic check for the fold; it is not a refinement of `fold`.

## Emitted functions

Every `export func` of `ecbs.sudo` has a row. `check_axioms.py --selftest` checks this column against the sudo.

| Emitted function | Theorem | What it says |
| --- | --- | --- |
| `tier` | `tier_demo_refines`, `tier_toy_refines`, `tier_hobby_refines`, `tier_serious_refines`, `tier_rejects` | `tier` of the four ASCII names is the model's tier. Any other array, given the four `beq` results are false, traps with kind `AssertFailed` (the detail carries the sudo line and is not claimed). |
| `phase_names` | `phase_names_refines` | The eight phase names, in index order. |
| `op_names` | `op_names_refines` | The five operation names, in index order. |
| `new_board` | `new_board_refines`, `demo_new_board` | On `BoardOk`: a fresh board, `n − 1` spare pegs, the halving loop and `lay_rung`, `clear` of the spare, park and tally, `climb_holes`, and the ladder append. The control row from `ladder0` is `Spec.rungList` in build order. The ladder array is that list reversed (climb order). Moves end at 0, `ladder_moves` is `Spec.ladderMoves`, and peak is 1. Demo is in `BoardOk` and returns that board. A script long enough that the last rung does not fit the control row is outside `BoardOk` and is not claimed. |
| `coordinate` | `coordinate_refines`, `demo_coordinate_origin` | For `home < 7` and `i < n` on a `GridOk` tier, `coordinate` is `Spec.coordinate`, including Demo's lane table and the `geodouble` split at column 10. Demo at home 0, hole 0 returns that value. |
| `place` | `place_refines`, `demo_place_peg` | On an empty home, `xs` of length `n` (fits an i64), and moves/peak that are naturals whose sum with the nonzero count fits an i64: writes `xs` into that home, sets held, adds the nonzero count to moves, and raises peak to the held-count of homes `0 .. 6` when that count is strictly larger. `bench_on` is unchanged. Demo places one peg in hole 0 of an empty home. |
| `band` | `band_held_refines`, `band_bench_refines`, `band_traps`, `demo_band_peg` | Held: the first `n` entries of that home. Not held, and the bench is on and aimed at this home: the first `n` entries of the bench. Otherwise kind `AssertFailed`. An index past the array is `OutOfBounds` and is not claimed. Demo reads a held one-peg home. |
| `call_in` | `call_in_card` | `start_calling`, then `call_hole` on both destinations for holes `0` through `n − 1`. The close is `set_control` of the calling hole to `0` and `ctrl + 1`. No `FieldOk`. |
| `roll_key` | `roll_key_refines`, `demo_roll_key`, `toy_roll_key`, `hobby_roll_key`, `serious_roll_key` | `rolledMatch` of `Spec.rollKey`. Every face is at most 9, and `FitsLen (faces.length + 1)` is a hypothesis. The four shipped tiers discharge the cell count. No `FieldOk`. A face outside `0 .. 9` is assert 1216 and is not claimed. |
| `exchange` | `exchange_card` | The card's sequence. A nonempty failure text is returned, and that branch does not run the later step. The two publish refusals are the reroll texts. No `FieldOk`. Not a proof of the shared point. |
| `receive_check` | `receive_check_card` | The four verdicts. `checkedAt` names the peak, `subI` of the moves since the curve test, `tally_max`, and `control_highest`. The curve failure does not call `certificate`. No `FieldOk`. |
| `make_certificate` | `make_certificate_card`, `make_certificate_steps`, `certificate_card` | A fresh board, the two puts, and the chord. An empty bottom returns `none` and does not invert. The other arm is `invert_checked`, and the export returns `point_of`. This is not the identity `π(C) − C`. No `FieldOk`. |
| `curve_test` | `curve_test_refines`, `demo_curve_zero_one` | On `FieldLay` and `TierSat`, for two length-`n` trit lists: the bool is the curve predicate. Demo at the zero across and the one-peg up returns true. Hobby and Serious published base points are not claimed. |
| `base_point_of` | none: the root-strip search is not tied | |
| `walk_key` | `key_seated`, `demo_walk_key`, `fform_walk_key` | `new_board` and the two base puts are `baseBoard`: moves `pegCount x + pegCount y`, peak 2, slides 0, control `tierR`. Demo is unconditional and walks by `walk_chord`. Toy, Hobby, and Serious walk by `walk_fform` and `finish`, and they take `FieldOk` (used for `¬ RunNonUnit`). Not a proof that the point is `Spec.walkRun`. |
| `invert_number` | `invert_number_refines`, `invert_number_none`, `demo_invert_one`, `demo_invert_neg`, `demo_invert_hole1` | On `BoardOk`, a length-`n` trit list, `TierSat`, `TierShape`, and `0 < tierR`: when the spec inverse is `some ans`, the export returns that list; when it is `none`, the kind is `AssertFailed`. Demo's one-peg list is returned as its own inverse. Demo's constant red peg (`negPeg`) is returned as its own inverse. Demo's white peg in hole 1 (`hole1Peg`) is returned as `hole1Inv`, a different list. |
| `multiply` | `multiply_refines`, `demo_multiply_one`, `demo_multiply_neg`, `demo_multiply_hole1` | On `FieldLay` (a `BoardOk` tier whose `n`, `k`, `w`, `h`, `r`, and `benchlen` are the layout `mul_refines` uses, with `n ≤ 1000000` and `benchlen ≤ 1000001`): `new_board`, across `put`, up `put` (two held homes, so peak goes from 1 to 2), `mul`, `settle`, `value`. The array is embedded `Spec.fieldMul`. The across input is a trit list of length `n`. The up input has length `n`. `FieldLay.fits` and `FieldLay.fits_n` are the `FitsLen` bounds this export and `cube_number` use. Demo's one-peg list times itself returns that list. Demo's constant red peg times itself returns the unit. Demo's white peg in hole 1 times `hole1Inv` returns the unit. |
| `cube_number` | `cube_number_refines`, `demo_cube_one` | On `FieldLay`, with `3·(n−1) + combgap < benchlen`: `new_board`, across `put`, `cube` of that home onto itself, `settle`, `value`. The array is embedded `Spec.fieldCube`. The input is a trit list of length `n`. Demo's one-peg list cubes to itself. |
| `fold` | `fold_refines`, `demo_fold_refines`, `fold_key_refines` | `fold` returns embedded `Spec.foldKey`. `fold_key` returns that list, and the board's moves grow by one per nonzero dropped cell. No `FieldOk`. |

## Internals the exports use

Not exported, so not in the column above. Each is the emitted function on the stated domain.

- `with_script_refines`: replaces the script length and leaves the rest of the tier.
- `flip_refines`: a trit `c ≤ 2`. Empty stays empty; white and red exchange (`3 - c`).
- `prefix_refines`: the first `m` entries, `m ≤` length, `m` fits an i64.
- `is_empty_refines`: true iff every entry is `0`. The length fits an i64. The empty array is true.
- `is_trits_refines`: true iff every entry is in `0 .. 2`. The length fits an i64.
- `npeg_refines`: the number of nonzero entries (`Spec.nnz`). The length fits an i64.
- `occupied_refines`: how many of homes `0 .. 6` are held. The held array must cover those seven slots. Home `7` is a real slot (`home_count` is 8) and is not counted; `note_peak` uses only this count.
- `put_refines`: the same record update as `place_refines`, without the outer `pure`.
- `value_held_refines`: `band` without the outer `pure`, on a held home.
- `home_set_read`: the elaborated bind. `atL` of `a.set i v` at `Int.ofNat i` returns `v`.
- `value_after_set`: a held home whose array is the length-`n` prefix. `get_number` reads that home, `home_set_read` is the bind, and `prefix_refines` returns the prefix. `n` fits an i64 and `n ≤` the source length. This is the read after `settle` writes the bench prefix into an empty home and sets it held.
- `laneDest_eq`: with `0 < w`, `0 < h` and `w·h − 1 ≤ e`, "one band up and one hole on" (end-of-row carry included) equals `e − (w·h − 1)`.
- `laneDest2_eq`: with `0 < w` and `r ≤ e / w`, "r rows up, same column" equals `e − r·w`.
- `schoolCol_refines`: one schoolbook row, columns `0 .. n`, mirror bit included, one move per nonzero cell. `n > 0`, the first number covers `n` trits, the cell `i+(n−1)` is on the strip, and the index and move sums fit an i64.
- `school_loop_refines`: the descending loop `i = n−1 downto 0` around that row. A zero second-coefficient is skipped; a nonzero one is lifted (one move) and laid with mirror `decide (c = 2) != mirror`. The strip is `Spec.school`. The final state is what `after` sees; `onRet` is unused. This is the stepper every inlined copy in `mul` is.
- `foldGeom_refines`: the emitted `d1`/`d2` block (wrap and non-wrap) equals `laneDest` and `laneDest2`. `0 < w`, `0 < h`, `r < h`, `w·h − 1 ≤ e`, and `w, h, r, e ≤ 1000000`.
- `foldGeom_dest`: under `(w·h − 1) − k = w·r`, those indices are `e − (w·h − 1)` and `e − ((w·h − 1) − k)`.
- `fold_loop_refines`: the descending loop from the last hole down through hole `n`. A zero peg is skipped. A nonzero peg is cleared, added at both images, and charged three moves. The strip is `Spec.laneFold`. A strip no longer than `n` breaks at once. `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, every entry a trit, `w, h, r ≤ 1000000`, the length at most `1000001`, `n ≤ 1000000`, and `moves + 3·(length − n)` fits an i64.
- `lane_fold_refines`: the highest-hole scan, the check that the hole is inside the bench, then `fold_loop_refines`. Both `max_bench_hole` branches are that one loop. When the scan is strictly above the recorded hole, the record becomes the scan. The strip is at most `benchlen` long and `benchlen > 0`.
- `lane_fold_eq`: `Ecbs.lane_fold` on an embedded strip whose length fits an i64, when the tier's `w`, `h`, `r`, `n`, `k`, and `benchlen` are those naturals. The inlined index block is `foldGeom`. Both hole branches are `foldLoop`. The scan is `topScan`. Composed with `lane_fold_refines`, the strip is `Spec.laneFold`.
- `laneFold_high`: after the fold, with `0 < n`, `0 < gap` and `n ≤` length, every hole from `n` up is `0`.
- `mulSchool_step`: the schoolbook stepper inlined six times in `Ecbs.mul` (the copies differ by generated binder names) equals `rowStep`, including the mirror flag that copy closed over.
- `mulPipeline_spec`: fresh bench, `mirror = false`, the shared loops only. `school_loop_refines`, then `lane_fold_refines`. The first `n` holes are `Spec.fieldMul`. `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, `2·(n−1) < bench`, the first number is all trits and both numbers cover `n`, the fold's size bounds, and `moves + n·(n+1) + 3·(bench − n)` fits an i64. Not a theorem about `Ecbs.mul`.
- `copy_band_refines`: `mirror = false`. The source home is held and holds `xs` of length `n`. The destination is empty. Writes that prefix, sets held, adds the nonzero count to moves, then `note_peak`. Homes `0 .. 6` are present.
- `mul_refines`: `Ecbs.mul` with `copy_second = true`, `onto = false`, `mirror = false`. Marker off, bench off, the two homes held and the spare empty, `first` and `second` distinct from the spare. Ops slot 0 is a natural. The tier fields are the layout naturals, `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, `2·(n−1) < bench`, both numbers have length `n` and the first is all trits. The bench ends on and aimed at `dst`, holding the lane fold of the schoolbook product. The prefix is `Spec.fieldMul`. Holes from `n` up are `0`. The move counter is the incoming counter plus the spare copy, the schoolbook, and the lane fold. The peak is the spare-copy raise, kept when the spare is cleared, then raised again only when the remaining held homes outnumber it. Slides and the tier stay. Held flags match the incoming board with the spare empty.
- `mul_refines_nocopy`: the same call with `copy_second = false`. The second number is lifted from its own home and that home is cleared. `first ≠ second`. There is no spare copy, so the move counter omits it and the peak is raised only by the final `note_peak`. The bench prefix is still `Spec.fieldMul`. The marker stays off, the control row stays, `tally0` and `control_highest` stay, and ops slot 0 becomes the incoming count plus one. The bench-off call returns that named board. The same call with the bench already on and aimed at the second home returns the named board of the slid state.
- `multiply_refines`: `Ecbs.multiply` on `FieldLay`. `new_board_refines`, then `put` of the across trit list (peak stays 1), then `put` of the up list (peak becomes 2), then `mul_refines` into the gap, then `folded_read`. The result is embedded `Spec.fieldMul`.
- `comb_cell`: on `Spec.combStrip`, hole `3·i` is coefficient `i` of the source whenever `i < n` and `3·i < bench`. A zero coefficient leaves that hole empty.
- `comb_loop_refines`: the ascending loop `i = 0 .. n−1` inlined in `Ecbs.cube`. A zero peg is skipped. A nonzero peg is copied to hole `3·i` and charged two moves. The strip is `Spec.combStrip`. `0 < n`, the source covers `n`, `3·(n−1) < bench`, and the index, the product `3·(n−1)`, and `moves + 2·n` fit an i64. The final state is what `after` sees; `onRet` is unused.
- `cube_refines`: `Ecbs.cube`. Marker off, bench off, the source home held. Ops slot 1 is a natural. The tier fields are the layout naturals, `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, `3·(n−1) + combgap < bench`, the source has length `n` and is all trits. The comb is `comb_loop_refines`, then `lane_fold_eq` and `lane_fold_refines`. The bench ends on and aimed at `dst`, holding the lane fold of `Spec.combStrip`. The prefix is `Spec.fieldCube`. Holes from `n` up are `0` (`laneFold_high`). The move counter is the incoming counter plus two per nonzero comb peg plus the lane fold. The peak is the incoming peak, raised when the held-count after the source home is cleared is strictly larger. Slides and the tier stay. The source held flag ends false and that home array becomes empty; every other home stays. The marker stays off, the control row stays, `tally0` and `control_highest` stay, and ops slot 1 becomes the incoming count plus one. The bench-off call returns that named board. The same call with the bench already on and aimed at the source returns the named board of the slid state, and the projections (prefix, empty source, moves, slides, peak, `tally0`, `control_highest`, control row, control counter, marker) are the fields of that board.
- `cube_number_refines`: `Ecbs.cube_number` on `FieldLay` with `3·(n−1) + combgap < benchlen`. `new_board_refines`, then `put` of the across trit list, then `cube_refines` of that home onto itself, then `folded_read`. The result is embedded `Spec.fieldCube`.
- `folded_read`: the bench is on and aimed at an empty home, and every hole from `n` up is `0`. `Ecbs.settle` then `Ecbs.value` of that home is the length-`n` prefix. `settle_refines` does the slide; `value_after_set` is the read.
- `new_board_refines`: `Ecbs.new_board` on `BoardOk` (`0 < n`, `4·n + 8`, `script + 3` and `control + 1` fit an i64, and `script + 2 +` the length of `Spec.rungList (n − 1)` is at most `control`). The spare holds `n − 1` whites. The halving loop paints `Spec.rungList` into the control row from `ladder0`, first rung first. `clear` empties the spare. Park is the hole after the last rung and tally is the hole after that. `climb_holes` walks the rungs from the last back to `ladder0`, and the ladder array is that list reversed. Moves are restored to 0. `ladder_moves` is `Spec.ladderMoves`. Peak is 1. Homes and held flags are empty. Bench and marker are off.
- `settle_off`: `bench_on = false`. `Ecbs.settle` returns the same board.
- `settle_refines`: the bench is on and aimed at an empty home. Every hole from `n` up is `0` (`laneFold_high` is that fact for a folded strip). `Ecbs.settle` writes the length-`n` prefix into that home, sets it held, clears `bench_on`, adds twice the nonzero count to moves and to slides, then `note_peak`. Homes `0 .. 6` are present. `n` and the bench length fit an i64, and so do `2` times the nonzero count and the two counter sums.

`laneDest_eq` and `laneDest2_eq` are the equalities `lane_fold` asserts (`d1 = e − n`, `d2 = e − (n − k)` when `n = w·h − 1` and `n − k = w·r`). `foldGeom_refines` shows the emitted row/column block computes those indices. `fold_loop_refines` is the descending loop around that block, and `lane_fold_refines` runs it after the scan.

No SPEC/code disagreement showed up on the functions above. `coordinate` matches §5.2, including Demo. The keypad's integer subtraction on face `0` is outside the SPEC's `1 .. 9` and outside the theorem.
