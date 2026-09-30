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

## Link 2: `lean/ScrambleV2`

The Lake package `lean/` (library `ScrambleV2`, Lean 4.14, no Mathlib) is the Link 2
work for `scramble_v2`: a hand-written model of the v2 digest, and theorems that the
emitted Lean computes it. **The digest-only headline is proved** (see the end of this
section); the trace is not. What is proved, all
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
- `cross_refines`, `dot_refines`, `mul_vec_refines`, `apply_matrix_refines`: the emitted
  cross product, row dot product, matrix-vector product and whole-cube rotation equal the
  model's, for a matrix in `rots`. Rows are the triple of `(Int × Int × Int)` from the
  streaming-state regeneration (not `List<List<int>>`). Positions in `{-1, 0, 1}`, and a
  list length that fits `i64`.
- `reorient_refines`: on a reachable cube, with two colors on perpendicular faces, the
  emitted `reorient` is the model's `rotateTo` (Rule B's matrix, or the seat).

**Lookups and piece readers** (`ScrambleV2/Link2/Lookup.lean`, `Pieces.lean`).

- `cubie_at_refines`: the emitted `cubie_at` returns the first index whose cubie sits at
  the asked point (so, with `atL`, the model's `cubieAt`).
- `is_center_refines`, `has_color_refines`, `hasCode_posed`, `center_dir_refines`: the
  emitted `center_dir` returns the point the model's `centerOf` finds, on a cube whose
  cubies are rotated solved cubies (which `Reach` gives).
- `sticker_on_refines`, `color_char_refines`, `is_ud_refines`, `edge_bit_refines`: the
  emitted readers on every axis code and every color.
- `corner_piece_refines`, `edge_piece_refines`: on colors that form a piece, the emitted
  readers return the model's `pieceId` (checked on all 216 color triples and 36 pairs).
- `fact_refines`: the emitted `fact` on `0 … 11`, the arguments `rank_perm` passes for
  the digest's 8 corners and 12 edges.

**The digest encoding** (`ScrambleV2/Link2/Rank.lean`, `Digest.lean`, `Index.lean`).

- `rank_perm_refines`: the emitted `rank_perm` on any list of naturals of length at most
  12 is the model's `rank` (every intermediate stays below `12!`, so nothing leaves `i64`).
- `digest_bytes_refines`: for `s3 < 2^61` and an 11-bit `eo`, the emitted `digest_bytes`
  (a 12-byte little-endian buffer, eleven carrying doublings, a carrying add, the
  three-zero-bytes assert, a big-endian copy-out) is `beBytes 9 (s3 · 2048 + eo)`.
- `index_bytes_refines`, `Reach.index_bytes`: whenever the model's `digestOf cube` is
  defined, the emitted `index_bytes` on `embedCube cube` returns exactly those 9 bytes
  (slot lookups, stickers, piece ids, the W/Y orientation if-chain, the base-3 and
  base-2 packs, both ranks); on a reachable cube it is always defined.

**Facelets and trace names** (`ScrambleV2/Link2/Facelets.lean`).

- `Reach.facelets_of`: the emitted `facelets_of` never traps on a reachable cube; it
  returns 54 color letters (every facelet slot holds a sticker on its axis in all 24
  poses, checked by `decide`).
- `solved_cube_refines`, `solved_facelets_ok`: the emitted solved cube is the model's,
  and its facelets are 54 color letters.
- `letter_refines`, `hex_digit_refines`, `move_name_refines`: the trace's name helpers on
  every color, digit `0 … 15`, face and turn count.

**State, digest path** (`ScrambleV2/Link2/State.lean`). Trace text is not modelled.
A digest-only state has `traced = false`, so `push_step` does not call `facelets_of`.

- `fresh_refines`, `scramble_v2_refines`, `scramble_v2_digest_refines`: `fresh(version, traced)`,
  and the two v2 constructors (`scramble_v2` traces, `scramble_v2_digest` does not).
- `push_step_digest`: on `traced = false`, `push_step` is the identity.
- `push_step_traced`: on a reachable cube with `traced = true`, `push_step` returns `.ok`
  and keeps the cube (the step list is the only field that grows).
- `do_move_refines`: `apply_turns` then `push_step`. For a turn count in `{1, 2, 3}` and a
  nybble below 16, the cube is `n` quarter turns. When not tracing, every other field stays.
- `do_rule_digest`: on a digest-only reachable state, `do_rule` is the model's Rule B
  rotation.
- `apply_v2_symbol_digest`: on a digest-only reachable state, one nybble below 16 is one
  v2 symbol (two quarter turns, then Rule B).

**The digest path end to end** (`ScrambleV2/Link2/Evaluate.lean`). States are written
field by field, so each statement names every field that changes. All are for the
digest-only v2 state (`version = 2`, `traced = false`).

- `pad_v2`: with `total = t` (and `t + 1` fitting `i64`), `pad` appends the marker `8`
  and then the cycle `6 0 7 1` up to 12 nybbles, as the model pads; nothing else changes.
  `padV2_eq`: the model's padding of a tape is that tape followed by the same suffix,
  taking `t` as the tape's length.
- `apply_ready_v2`: on a reachable cube with pending nybbles below 16, `apply_ready`
  applies every pending nybble as one v2 symbol (the model's walk over them), empties
  `pending`, and advances `processed` by their count (the sum fitting `i64`).
- `update_v2`: on a state that is not done, with a byte message (every element at most
  255), `update` appends the message's nybbles (high first), then does the above;
  `total` grows by twice the message length.
- `finish_digest`: `finish` is the model's closer and seat (`F2`, `B2`, Rule B with
  `up = W`, `front = G`) and sets `done`.
- `evaluate_v2`: on a state that is not done with `total = t`, `evaluate` (`pad`,
  `apply_ready`, `finish`, `index_bytes`) returns `.ok`, and the digest is the model's
  digest of the cube reached by walking pending plus the padding and seating.

**Headline (digest only):** `scramble_v2_digest_refines_digestV2`. For `msg : List Nat`
with every element at most 255 and `2 · msg.length + 12` fitting `i64`:

```lean
∃ s0 s1 ev s2, Scramble.scramble_v2_digest = .ok s0 ∧
  Scramble.update s0 (embed msg) = .ok s1 ∧
  Scramble.evaluate s1 = .ok (ev, s2) ∧
  ev.sudo_10Evaluation_6digest = embed (digestV2 msg)
```

So one `update` with the whole message on a fresh digest-only state, then `evaluate`,
never traps and yields the model's digest. The model is pinned to the SPEC vectors by the
five KATs above.

**Not claimed:** the trace (the `trace` field of the evaluation, `push_step` text,
`facelets_of` output beyond never trapping), and so the traced constructor `scramble_v2`
(the headline is stated for `scramble_v2_digest`; that the traced state gives the same
digest is not proved here); several `update` calls in a row (each call's theorem is
general, but no chained statement is given); an `update` or `evaluate` after `done`
(the sudo asserts); non-byte input (the sudo asserts, and nothing is claimed about it);
v1 (`scramble_v1`, `scramble_v1_digest`).

| Emitted function | Theorem | Domain |
| --- | --- | --- |
| `scramble_v2_digest` | `scramble_v2_digest_refines`, `fresh_refines` | none |
| `scramble_v2` | `scramble_v2_refines`, `fresh_refines` | none (constructor only; the traced digest is not claimed) |
| `update` | `update_v2` | digest-only v2 state, not done, pending nybbles below 16, reachable cube; byte message; counts fit i64 |
| `evaluate` | `evaluate_v2`, `scramble_v2_digest_refines_digestV2` | as `update`; digest only |
| `solved_facelets` | `solved_facelets_ok` | none (returns 54 color letters) |
| `scramble_v1`, `scramble_v1_digest` | none: v1 is out of scope for this package | |

`check_axioms.py --selftest` parses `scramble.sudo` and fails unless every `export func`
appears in the Emitted function column above, and only exports appear there.

None of this is a hash-security claim.

## Long-term hash story

A future **multi-cube sponge** is the long-term hash direction. Until that lands as a published primitive, do not read this directory as a reduction, an attack-bound proof, or a commitment to a next version number.
