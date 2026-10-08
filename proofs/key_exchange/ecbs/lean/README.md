<!-- Owns: the scope of the ECBS Link 2 proofs (proofs/key_exchange/ecbs/lean) and their export table. Maintenance rules: ../../../../DOCS.md. -->
# ECBS Link 2: emitted tier, coordinate, band, place and keypad against a hand-written model

Status: **in progress.** The Lean below proves that the code `sudoc` emits from [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) (in [`Generated/`](Generated/README.md)) computes what a hand-written model in [`EcbsLink2/Spec.lean`](EcbsLink2/Spec.lean) says, for the functions and domains in the table. `place` includes the record update. The schoolbook inside `mul` is one generic loop (`schoolCol_refines`, `school_loop_refines`) equal to `Spec.school`. The descending lane fold is one loop (`fold_loop_refines`) equal to `Spec.laneFold`, and both `max_bench_hole` branches are that loop (`lane_fold_refines`, including the highest-hole scan and the move counter). `mulPipeline_spec` is that composition on a fresh bench (`mirror = false`): the prefix is `Spec.fieldMul`. It is not a theorem about `Ecbs.mul`. The six inlined schoolbook steppers are `mulSchool_step` (`rowStep`). `lane_fold_eq` is `Ecbs.lane_fold`: the inlined geometry, both hole branches, and the scan. `mul_refines` is `Ecbs.mul` on the export flags (`copy_second`, not `onto`, not `mirror`): the bench is the lane fold of the schoolbook product, the prefix is `Spec.fieldMul`, and holes from `n` up are empty. `copy_band_refines` is the spare copy that flag uses. `comb_cell` is hole `3·i` of `Spec.combStrip`. `comb_loop_refines` is the ascending comb in `Ecbs.cube` (nonzero `v[i]` copied to that hole, two moves). `cube_refines` is `Ecbs.cube`: that comb, then `lane_fold_eq`, `lane_fold_refines`, and `laneFold_high`. The bench prefix is `Spec.fieldCube`, and holes from `n` up are empty. `settle_refines` is `Ecbs.settle`: the tail assert, the slide home, and `note_peak`. `folded_read` runs `settle` and then `value` on that zero-tailed bench, using `settle_refines` and `value_after_set`. `value` of a held home is already `value_held_refines`. The exported `multiply` and `cube_number` still start at `new_board`. The ladder, the fold and the exchange are not tied to the emitted loops yet. The lane-fold geometry those loops assert is proved as `Nat` arithmetic. The model is numbers and lists of trits (hole 0 first), written from [SPEC](../../../../primitives/key_exchange/ecbs/SPEC.md) §§1, 2, 4, 5.2 and 6. It is **correctness of the emitted code on that domain, not a security claim**: nothing here says the curve's discrete log is hard, that a key has entropy, or that the fold extracts.

Build and audit (Lean 4.14.0, no Mathlib):

```sh
cd proofs/key_exchange/ecbs/lean
lake build                                       # EcbsLink2 (and the emitted Generated/)
python3 ../../../doubledeal/check_axioms.py ecbs # every EcbsLink2 theorem: propext, Classical.choice, Quot.sound only
python3 ../../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
```

No `sorry`, no `native_decide`, no `axiom`. Tier names and the four tiers' `BoardOk` / `GridOk` / `FoldOk` facts use `decide` and `decide!` (kernel evaluation, no extra axiom), split per tier. A clean `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 432396 kB RSS.

## Generated Lean

[`Generated/`](Generated/README.md) is emitted from `ecbs.sudo` by `proofs/emit_lean.sh ecbs` under the terminates gate. Its TAP runs every sudo `test` (`ecbs_test`). That is evidence the emitter ran, not a theorem.

## The model

[`EcbsLink2/Spec.lean`](EcbsLink2/Spec.lean). A register is a `List Nat` of trits. `embTier` / `embed` send a model tier or register to the emitted record.

- `Spec.demo`, `Spec.toy`, `Spec.hobby`, `Spec.serious`: the §1 table, names as ASCII bytes.
- `Spec.coordinate`: §5.2. Demo uses the fixed lane table; the other tiers use `geoper` bands, and `geodouble` splits a column at 10.
- `Spec.keypadFirst` / `Spec.keypadSecond`: §4, faces `1 .. 9`.
- `Spec.flipTrit`, `Spec.phaseNames`, `Spec.opNames`.
- `Spec.rungList` / `Spec.foldKey` / `Spec.rollKey` are the SPEC's ladder, fold and row cup. No theorem says the emitted `new_board`, `fold` or `roll_key` returns them.

`GridOk` is the coordinate domain (non-Demo `w` and `geoper` positive, the products fit an i64). All four published tiers meet it. `BoardOk` and `FoldOk` are the same kind of arithmetic check for the ladder and the fold; they are not a refinement of `new_board` or `fold`.

## Emitted functions

Every `export func` of `ecbs.sudo` has a row. `check_axioms.py --selftest` checks this column against the sudo.

| Emitted function | Theorem | What it says |
| --- | --- | --- |
| `tier` | `tier_demo_refines`, `tier_toy_refines`, `tier_hobby_refines`, `tier_serious_refines`, `tier_rejects` | `tier` of the four ASCII names is the model's tier. Any other array, given the four `beq` results are false, traps with kind `AssertFailed` (the detail carries the sudo line and is not claimed). |
| `phase_names` | `phase_names_refines` | The eight phase names, in index order. |
| `op_names` | `op_names_refines` | The five operation names, in index order. |
| `new_board` | none: the emitted ladder (spare, halving, `lay_rung`, `clear`, `climb_holes`) is not tied to `Spec.rungList` | The published tiers satisfy the arithmetic side condition that the ladder indices fit the control row. A longer script can make the first rung assert; that trap is not a theorem here. |
| `coordinate` | `coordinate_refines` | For `home < 7` and `i < n` on a `GridOk` tier, `coordinate` is `Spec.coordinate`, including Demo's lane table and the `geodouble` split at column 10. |
| `place` | `place_refines` | On an empty home, `xs` of length `n` (fits an i64), and moves/peak that are naturals whose sum with the nonzero count fits an i64: writes `xs` into that home, sets held, adds the nonzero count to moves, and raises peak to the held-count of homes `0 .. 6` when that count is strictly larger. `bench_on` is unchanged. |
| `band` | `band_held_refines`, `band_bench_refines`, `band_traps` | Held: the first `n` entries of that home. Not held, and the bench is on and aimed at this home: the first `n` entries of the bench. Otherwise kind `AssertFailed`. An index past the array is `OutOfBounds` and is not claimed. |
| `call_in` | none: the calling loop is not tied | |
| `roll_key` | none: the three nested read loops are not tied | The keypad map they call is claimed for faces `1 .. 9` (`keypad_first_refines`, `keypad_second_refines`). Face `0` is the blank the row cup skips before those calls. The functions themselves do not assert the range. |
| `exchange` | none: both players' walks are not tied | |
| `receive_check` | none: the certificate check is not tied | |
| `make_certificate` | none: `π(C) − C` on the board is not tied | |
| `curve_test` | none: the curve predicate on the board is not tied | |
| `base_point_of` | none: the root-strip search is not tied | |
| `walk_key` | none: the key walk is not tied | |
| `invert_number` | none: the emitted inverse is not tied | |
| `multiply` | none: the exported function still starts at `new_board` | `mul_refines` is `Ecbs.mul` with `copy_second = true`, `onto = false`, `mirror = false`, marker off and bench off. The bench is the lane fold of the schoolbook product; the prefix is `Spec.fieldMul`. `mulSchool_step` is the stepper inlined six times. `lane_fold_eq` is `Ecbs.lane_fold`. `copy_band_refines` is the spare copy. `settle_refines` slides a zero-tailed bench home. The export still builds the board with `new_board` first. |
| `cube_number` | none: the exported function still starts at `new_board` | `cube_refines` is `Ecbs.cube` with the marker off and the bench off. The source home is held and holds a length-`n` trit list. Ops slot 1 is a natural. `3·(n−1) + combgap < bench`. The bench ends on and aimed at `dst`, holding the lane fold of the comb. The prefix is `Spec.fieldCube`. Holes from `n` up are `0`. `folded_read` is `settle` then `value` on a bench in that shape. The export still builds the board with `new_board` first. |
| `fold` | none: `fold` starts with `new_board` and `fold_key`, and neither loop nest is tied | `Spec.foldKey` is the §6 row drop (read the original across, add in GF(3), keep `keeprows` rows). It is not a theorem about the emitted function. |

## Internals the exports use

Not exported, so not in the column above. Each is the emitted function on the stated domain.

- `with_script_refines`: replaces the script length and leaves the rest of the tier.
- `flip_refines`: a trit `c ≤ 2`. Empty stays empty; white and red exchange (`3 - c`).
- `prefix_refines`: the first `m` entries, `m ≤` length, `m` fits an i64.
- `is_empty_refines`: true iff every entry is `0`. The length fits an i64. The empty array is true.
- `is_trits_refines`: true iff every entry is in `0 .. 2`. The length fits an i64.
- `npeg_refines`: the number of nonzero entries (`Spec.nnz`). The length fits an i64.
- `keypad_first_refines`, `keypad_second_refines`: faces `1 .. 9` only.
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
- `mul_refines`: `Ecbs.mul` with `copy_second = true`, `onto = false`, `mirror = false`. Marker off, bench off, the two homes held and the spare empty, `first` and `second` distinct from the spare. Ops slot 0 is a natural. The tier fields are the layout naturals, `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, `2·(n−1) < bench`, both numbers have length `n` and the first is all trits. The bench ends on and aimed at `dst`, holding the lane fold of the schoolbook product. The prefix is `Spec.fieldMul`. Holes from `n` up are `0`.
- `comb_cell`: on `Spec.combStrip`, hole `3·i` is coefficient `i` of the source whenever `i < n` and `3·i < bench`. A zero coefficient leaves that hole empty.
- `comb_loop_refines`: the ascending loop `i = 0 .. n−1` inlined in `Ecbs.cube`. A zero peg is skipped. A nonzero peg is copied to hole `3·i` and charged two moves. The strip is `Spec.combStrip`. `0 < n`, the source covers `n`, `3·(n−1) < bench`, and the index, the product `3·(n−1)`, and `moves + 2·n` fit an i64. The final state is what `after` sees; `onRet` is unused.
- `cube_refines`: `Ecbs.cube`. Marker off, bench off, the source home held. Ops slot 1 is a natural. The tier fields are the layout naturals, `0 < w`, `0 < h`, `0 < r < h`, `n = w·h − 1`, `k ≤ n`, `n − k = w·r`, `3·(n−1) + combgap < bench`, the source has length `n` and is all trits. The comb is `comb_loop_refines`, then `lane_fold_eq` and `lane_fold_refines`. The bench ends on and aimed at `dst`, holding the lane fold of `Spec.combStrip`. The prefix is `Spec.fieldCube`. Holes from `n` up are `0` (`laneFold_high`).
- `folded_read`: the bench is on and aimed at an empty home, and every hole from `n` up is `0`. `Ecbs.settle` then `Ecbs.value` of that home is the length-`n` prefix. `settle_refines` does the slide; `value_after_set` is the read.
- `settle_off`: `bench_on = false`. `Ecbs.settle` returns the same board.
- `settle_refines`: the bench is on and aimed at an empty home. Every hole from `n` up is `0` (`laneFold_high` is that fact for a folded strip). `Ecbs.settle` writes the length-`n` prefix into that home, sets it held, clears `bench_on`, adds twice the nonzero count to moves and to slides, then `note_peak`. Homes `0 .. 6` are present. `n` and the bench length fit an i64, and so do `2` times the nonzero count and the two counter sums.

`laneDest_eq` and `laneDest2_eq` are the equalities `lane_fold` asserts (`d1 = e − n`, `d2 = e − (n − k)` when `n = w·h − 1` and `n − k = w·r`). `foldGeom_refines` shows the emitted row/column block computes those indices. `fold_loop_refines` is the descending loop around that block, and `lane_fold_refines` runs it after the scan.

No SPEC/code disagreement showed up on the functions above. `coordinate` matches §5.2, including Demo. The keypad's integer subtraction on face `0` is outside the SPEC's `1 .. 9` and outside the theorem.
