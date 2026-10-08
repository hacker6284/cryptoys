<!-- Owns: the scope of the ECBS Link 2 proofs (proofs/key_exchange/ecbs/lean) and their export table. Maintenance rules: ../../../../DOCS.md. -->
# ECBS Link 2: emitted tier, coordinate, band, place and keypad against a hand-written model

Status: **a first slice.** The Lean below proves that the code `sudoc` emits from [`ecbs.sudo`](../../../../primitives/key_exchange/ecbs/ecbs.sudo) (in [`Generated/`](Generated/README.md)) computes what a hand-written model in [`EcbsLink2/Spec.lean`](EcbsLink2/Spec.lean) says, for the functions and domains in the table. `place` includes the record update. The ladder, the fold, multiplication and the exchange are not tied to the emitted loops yet; the lane-fold geometry those loops assert is proved as `Nat` arithmetic. The model is numbers and lists of trits (hole 0 first), written from [SPEC](../../../../primitives/key_exchange/ecbs/SPEC.md) §§1, 2, 4, 5.2 and 6. It is **correctness of the emitted code on that domain, not a security claim**: nothing here says the curve's discrete log is hard, that a key has entropy, or that the fold extracts. The ladder, the fold and the row-cup filler are modelled and not claimed; the emitted `mul`, `cube`, `invert` and the exchange are not tied.

Build and audit (Lean 4.14.0, no Mathlib):

```sh
cd proofs/key_exchange/ecbs/lean
lake build                                       # EcbsLink2 (and the emitted Generated/)
python3 ../../../doubledeal/check_axioms.py ecbs # every EcbsLink2 theorem: propext, Classical.choice, Quot.sound only
python3 ../../../doubledeal/security/checks/scan_sorry.py --root . --exclude Generated
```

No `sorry`, no `native_decide`, no `axiom`. Tier names and the four tiers' `BoardOk` / `GridOk` / `FoldOk` facts use `decide` and `decide!` (kernel evaluation, no extra axiom), split per tier. A clean `lake build EcbsLink2` under `ulimit -v 7000000` peaked at 432468 kB RSS.

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
| `multiply` | none: the emitted `mul` inlines each flag combination and is not tied | |
| `cube_number` | none: the emitted `cube` and `lane_fold` are not tied | |
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
- `laneDest_eq`: with `0 < w`, `0 < h` and `w·h − 1 ≤ e`, "one band up and one hole on" (end-of-row carry included) equals `e − (w·h − 1)`.
- `laneDest2_eq`: with `0 < w` and `r ≤ e / w`, "r rows up, same column" equals `e − r·w`.

`laneDest_eq` and `laneDest2_eq` are the equalities `lane_fold` asserts (`d1 = e − n`, `d2 = e − (n − k)` when `n = w·h − 1` and `n − k = w·r`). They are not yet applied to the emitted loop.

No SPEC/code disagreement showed up on the functions above. `coordinate` matches §5.2, including Demo. The keypad's integer subtraction on face `0` is outside the SPEC's `1 .. 9` and outside the theorem.
