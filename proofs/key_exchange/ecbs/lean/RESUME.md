# RESUME

ECBS Link 2 part 1, branch `cursor/ecbs-link2-4113`. This branch is the finished slice. Do not continue the chord, the walk, or `base_point_of` here.

The in-progress development, including every file this branch deleted, is on `cursor/ecbs-link2-part2` at `146c0c6a507d57a116bff3cc26ffb5973482e1e7`. That branch has no pull request. The same recursion-depth and heartbeat removal is on that commit.

## Covered exports

Each row is a complete refinement: the hypotheses are the domain, and the Demo success is a separate theorem where the export has a success branch.

- `tier`: `tier_demo_refines`, `tier_toy_refines`, `tier_hobby_refines`, `tier_serious_refines`, `tier_rejects`. Domain: the four ASCII names, and any other array once the four comparisons are false (`AssertFailed`).
- `phase_names`: `phase_names_refines`. No input.
- `op_names`: `op_names_refines`. No input.
- `new_board`: `new_board_refines` on `BoardOk`. Demo: `demo_new_board`.
- `coordinate`: `coordinate_refines` on `GridOk`, `home < 7`, `i < n`. Demo: `demo_coordinate_origin`.
- `place`: `place_refines`. Domain: empty home, `xs` of length `n` fitting an i64, natural moves and peak, `moves +` nonzero count fitting an i64, homes `0 .. 6` present. Demo: `demo_place_peg`.
- `band`: `band_held_refines`, `band_bench_refines`, `band_traps`. Domain: the home index is inside the held array. An index past the array is `OutOfBounds` and is not claimed. Demo success: `demo_band_peg`.
- `curve_test`: `curve_test_refines` on `FieldLay`, `TierSat`, two length-`n` trit lists. Demo: `demo_curve_zero_one`.
- `invert_number`: `invert_number_refines` and `invert_number_none` on `BoardOk`, a length-`n` trit list, `TierSat`, `TierShape`, `0 < tierR`, and `fieldInv` some or none. Demo: `demo_invert_one`.
- `multiply`: `multiply_refines` on `FieldLay`, across a length-`n` trit list, up a length-`n` list. Demo: `demo_multiply_one`.
- `cube_number`: `cube_number_refines` on `FieldLay` with `3·(n−1) + combgap < benchlen`, input a length-`n` trit list. Demo: `demo_cube_one`.

`demo_basePoint` is `Spec.basePoint` on Demo. `frobenius_affine_refines` is the affine cube on a board that already holds the two homes. Neither is an export. `base_point_of` is not covered.

## Not covered

`call_in`, `roll_key`, `exchange`, `receive_check`, `make_certificate`, `base_point_of`, `walk_key`, `fold`. They stay on `cursor/ecbs-link2-part2`.

Success-branch reachability is not proved for Toy, Hobby, and Serious. SPEC.md gives the Hobby and Serious base points only as hashes. Proving that `fieldInv` is the true field inverse is future work, not started.

## Gates

A clean `lake build EcbsLink2` under `ulimit -v 7000000` succeeds.

- Theorems: 2989
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Largest remaining file: `EcbsLink2/Link2/ClimbEmit.lean`, VmHWM 1740496 kB
- No `maxHeartbeats` or `maxRecDepth` option. The concrete `decide` facts are split into kernel steps, and `red_cube_mul` fits the default heartbeat limit.
