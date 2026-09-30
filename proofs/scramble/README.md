<!-- Owns: what this tree claims and does not claim for Scramble, and how to rebuild its Generated Lean. Maintenance rules: ../../DOCS.md. -->
# Scramble proofs

Scramble stays a **teaching / lineage** hash. `scramble_v2` is current ([`primitives/hash/scramble/`](../../primitives/hash/scramble/SPEC.md)). This directory does not claim collision resistance, preimage resistance, or any other hash-security property.

Sudo is normative. Emitted Lean under `lean/Generated/` is the
algorithm. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). This does
**not** claim sudo↔Lean semantic-equivalence theorems (emitter soundness). The emit
terminates gate is on. Production loops are bounded `for`.

## Birthday ceiling

The digest size and attack figures are in the SPEC's [`scramble_v2`](../../primitives/hash/scramble/SPEC.md#scramble_v2) section. They are honesty about the group size, not theorems in this tree, and not a reason to treat Scramble as a hash with a security level.

## Generated Lean

Do not edit `lean/Generated/` by hand. From the repo root:

```sh
proofs/emit_lean.sh scramble
cd proofs/scramble/lean/Generated && lake build && ./.lake/build/bin/scramble_test
```

Expected TAP: **15/15**. Pin and regenerating: [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

## Link 2 (in progress): `lean/ScrambleV2`

The Lake package `lean/` (library `ScrambleV2`, Lean 4.14, no Mathlib) is the Link 2
work for `scramble_v2`: a hand-written model of the v2 digest, and theorems that the
emitted Lean computes it. **The headline is not proved yet.** What is proved, all
checked by the axiom gate (`check_axioms.py scramble`: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`):

**The model** (`ScrambleV2/Spec.lean`), written from the SPEC, v2 only: cubies on integer
coordinates, each a position plus stickers (a color facing a direction); the SPEC's face
maps; Rule B's matrix with rows `e × t`, `e`, `t`; the closer and seat; the digest by the
SPEC's slot tables, with `co` packed little-endian in base 3. `digestV2? msg` is an
`Option` (it answers `none` where the SPEC leaves a case undefined, such as a slot with
no cubie); `digestV2` is its `getD []`. The trace text is not modelled.

- `kat_empty`, `kat_a`, `kat_A7`, `kat_hello`, `kat_cube` (`ScrambleV2/Kat.lean`): the
  model gives the five v2 digests of the SPEC table and of `scramble.sudo`'s tests
  (kernel `decide!`). This pins the model to the vectors, not the emitted code.

**The invariant** (`ScrambleV2/Link2/Reach.lean`, model only). `Reach cube`: each cubie is a
rotation (one of the 24 signed permutation matrices of determinant 1, `rots`) of the
solved cubie that started in its list slot; the positions are a permutation of the 26
lattice points; one frame rotation places every face center.

- `reach_solved`, `reach_quarter`, `reach_rotate`: it holds for the solved cube and
  survives every quarter turn and every whole-cube rotation from `rots`.
- `centerOf_reach`, `cubieAt_reach`: every center and every lattice slot is found, and
  where.
- `rotateTo_reach`, `ruleB_reach`: Rule B's two colors are on perpendicular faces, its
  matrix is in `rots`, and the result is reachable.
- `digestV2_isSome`: for every message the model's walk, seat and slot reads all
  succeed, so `digestV2? msg` is never `none` (every slot holds a real piece and every
  color lookup the digest makes is defined).

**Refinement of the cube moves** (`ScrambleV2/Link2/Turn.lean`, `Matrix.lean`). `embedC` /
`embedCube` map a model cubie to the emitted `Cubie` (colors `1 … 6`, `0` for an empty
slot). Hypotheses are domain facts only: positions in `{-1, 0, 1}` and a list length that
fits `i64`.

- `turn_cubie_refines`, `quarter_refines`, `apply_turns_refines`: the emitted face turn
  equals the model's `moveCubie` / `quarter`.
- `cross_refines`, `mul_vec_refines`, `apply_matrix_refines`: the emitted cross product,
  matrix-vector product and whole-cube rotation equal the model's, for a matrix in `rots`.
  These target the matrix shape of the Generated code on `main` today (`List<List<int>>`).

**Not proved yet** (the plan): the emitted `center_dir`, `reorient`, `do_rule`,
`facelets_of` (never traps on a reachable cube), the tape and state functions
(`update`, `apply_ready`, padding, `evaluate`), `rank_perm`, `corner_piece`,
`edge_piece`, `digest_bytes`, `index_bytes`, and the headline: for a byte message, the
emitted `scramble_v2`, `update`, `evaluate` return `.ok` with `digest = embed (digestV2 msg)`
(digest only; the trace is excluded).

None of this is a hash-security claim.

## Long-term hash story

A future **multi-cube sponge** is the long-term hash direction. Until that lands as a published primitive, do not read this directory as a reduction, an attack-bound proof, or a commitment to a next version number.
