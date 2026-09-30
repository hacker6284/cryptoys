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
emitted Lean computes it. **The digest headline is proved**, for the digest-only and the traced
constructor and for several updates; the trace's step fields are proved, not its letters
(see the end of this section). The digest-only v1 path is also proved against a v1 model. What is proved, all
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
field by field, so each statement names every field that changes. All are for
`version = 2`; all but `pad_v2` (which holds for either value) also need `traced = false`.

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

**Traced path and several updates** (`ScrambleV2/Link2/Traced.lean`). The same chain
for `traced` either value: `push_step_gen`, `do_move_gen`, `do_rule_gen`,
`apply_v2_symbol_gen`, `apply_ready_v2_gen`, `update_v2_gen`, `finish_gen`,
`evaluate_v2_gen`, each also saying which trace steps the call appends. The trace claim
is this: on a traced state the appended steps have exactly the SPEC's kind, move token,
nybble digit, block and index, in order, and each facelet string is 54 color letters. On
a digest-only state nothing is appended. The Rule B steps' `up` / `front` letters, and
which letters a facelet string holds, are not claimed.

- `updates_v2`, `updates_evaluate_v2`: from `fresh(2, traced)`, `update` with each
  message of a list in turn, then `evaluate`, all return `.ok`. The digest is the model's
  digest of the concatenated message (SPEC "API": `update(a)` then `update(b)` is
  `update(a || b)`). The trace is as above for the padded concatenation plus the closer,
  and on a digest-only state it is empty. Every message must be bytes, with twice the
  total length plus 12 fitting `i64`.
- `scramble_v2_refines_digestV2_traced`: the traced constructor `scramble_v2`, one
  `update`, `evaluate`. Digest `embed (digestV2 msg)`. The trace's kind / move / nybble /
  block / index fields are the SPEC's steps for the padded tape and the closer; each
  facelet string is 54 color letters; there are `3 · (padded length) + 3` steps.
  `padV2_length`: the padded length is `max (len + 1) 12`, so a message of at most 5 bytes
  has 39 steps, the SPEC table's Steps column.

**v1, digest only** (`ScrambleV2/SpecV1.lean`, `KatV1.lean`, `Link2/V1.lean`). The v1
model is written from the SPEC's superseded `scramble_v1` section, on the same cube,
Rule B, closer, seat and digest as v2. A nybble is one move (the SPEC's 16-move table),
eight moves then Rule B make a block, and the tape is padded with the marker `8` and the
cycle `6 0 7 1 8 2 9 3` to a multiple of 8 and to at least 24. The v1 trace is not modelled.

- `kat_v1_empty`, `kat_v1_a`, `kat_v1_A7`, `kat_v1_hello`, `kat_v1_cube`: the v1 model
  gives the five v1 digests of the SPEC table and of `scramble.sudo`'s tests (kernel
  `decide!`). This pins the model to the vectors, not the emitted code.
- `apply_v1_block_digest`: on a digest-only reachable state, the emitted `apply_v1_block`
  on eight pending nybbles below 16 is the model's block (eight moves, then Rule B).
- `apply_ready_v1_digest`: with `processed = 8q`, `apply_ready` on a v1 state walks every
  complete block of `pending` (the model's `walkV1`), advances `processed` by 8 per
  block, and keeps the trailing partial block in `pending`.
- `pad_v1`, `padV1_eq`: `pad` on a v1 state with `total = t` appends the marker, the cycle
  up to a multiple of 8, then the cycle again up to 24 nybbles, as the model pads.
- `update_v1`, `evaluate_v1`: as `update_v2` and `evaluate_v2`, for a digest-only v1
  state with `processed = 8q`. `walkV1_append8`: walking whole blocks then the rest is
  walking the concatenation, so the partial block left in `pending` meets the padding.
- `scramble_v1_digest_refines`: `scramble_v1_digest` is `fresh(1, false)`.
- `scramble_v1_digest_refines_digestV1`: for `msg : List Nat` with every element at most
  255 and `2 · msg.length + 40` fitting `i64`,

```lean
∃ s0 s1 ev s2, Scramble.scramble_v1_digest = .ok s0 ∧
  Scramble.update s0 (embed msg) = .ok s1 ∧
  Scramble.evaluate s1 = .ok (ev, s2) ∧
  ev.sudo_10Evaluation_6digest = embed (digestV1 msg)
```

  One `update` only. Several v1 updates, the traced v1 constructor `scramble_v1` and the
  v1 trace are not claimed.

**Not claimed:** the Rule B steps' `up` / `front` letters and the facelet strings' letters
(the vectors' Final facelets column); an `update` or `evaluate` after `done` (the sudo
asserts); non-byte input (the sudo asserts, and nothing is claimed about it); the traced
v1 constructor `scramble_v1` and the v1 trace; several v1 updates.

| Emitted function | Theorem | Domain |
| --- | --- | --- |
| `scramble_v2_digest` | `scramble_v2_digest_refines`, `fresh_refines` | none |
| `scramble_v2` | `scramble_v2_refines`, `fresh_refines`, `scramble_v2_refines_digestV2_traced` | byte message, `2·len + 12` fits i64; trace fields as above |
| `update` | `update_v2`, `update_v2_gen`, `updates_evaluate_v2`, `update_v1` | v2 state (or digest-only v1 state with `processed = 8q`), not done, pending nybbles below 16, reachable cube; byte messages; counts fit i64 |
| `evaluate` | `evaluate_v2`, `evaluate_v2_gen`, `scramble_v2_digest_refines_digestV2`, `evaluate_v1`, `scramble_v1_digest_refines_digestV1` | as `update` |
| `solved_facelets` | `solved_facelets_ok` | none (returns 54 color letters) |
| `scramble_v1_digest` | `scramble_v1_digest_refines`, `fresh_refines`, `scramble_v1_digest_refines_digestV1` | byte message, `2·len + 40` fits i64; one `update` |
| `scramble_v1` | none: the traced v1 constructor is not claimed | |

`check_axioms.py --selftest` parses `scramble.sudo` and fails unless every `export func`
appears in the Emitted function column above, and only exports appear there.

None of this is a hash-security claim.

## Long-term hash story

A future **multi-cube sponge** is the long-term hash direction. Until that lands as a published primitive, do not read this directory as a reduction, an attack-bound proof, or a commitment to a next version number.
