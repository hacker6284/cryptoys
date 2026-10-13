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

## Next

The up cube equation is `across_up_cube`: on the board `down_across` leaves, `Ecbs.cube` of up onto up is `cube_bench_up` (`m = 0`, control `ctrl + 1`, max `max mx 1`). The bench is still on. Still open: `cube_settle_other` and `cube_off_eq` of that up home, then the closing `settle`, so the two homes are `fieldCube`. Do those by `rw` of the projection lemmas. A single declaration that also simplified `cubeOffBoard` exceeded the default heartbeat limit.

After that, in order: general `walk_chord` by induction on cells; `walk_fform`; the root-strip search (`base_point_of`, errors 963 and 1527, Demo non-vacuity only); `walk_key`, `exchange`, `receive_check`, `make_certificate`; `fold` / `fold_key`, `roll_key`, `call_in`.

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
