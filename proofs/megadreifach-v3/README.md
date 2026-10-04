<!-- Owns: the MegaDreifach v3 Lean package (proofs/megadreifach-v3/): what is checked, what is not, and the Link 2 status of each v3 export. Maintenance rules: ../../DOCS.md. -->
# MegaDreifach v3 (ZP26) in Lean

Lean for MegaDreifach v3, the ZP26 card phase
([`primitives/hash/megadreifach/v3/SPEC.md`](../../primitives/hash/megadreifach/v3/SPEC.md),
[`v3/megadreifach.sudo`](../../primitives/hash/megadreifach/v3/megadreifach.sudo)).
The sudo is the source of truth. Link 2 (the emitted code equals a hand-written model): every
export has a Link 2 theorem, under the input conditions listed in the export table below.

| Piece | What it is | Checked by |
| --- | --- | --- |
| `lean/Generated/` | Lean emitted from the v3 sudo by `proofs/emit_lean.sh` (target `megadreifach-v3`), with `EMITTED_FROM.json`. Do not edit. | CI `generated-fresh` (`emit_lean.sh --check`); CI `megadreifach-v3-generated` builds it and runs the 23 sudo tests (TAP) |
| `lean/MegaDreifachV3/Vectors.lean` | The v3 KAT file `kats/megaminx_hash_kats_v3.json` as Lean data, written by `vectors/json_to_lean.py` | CI `megadreifach-v3-lean` (`json_to_lean.py --check`) |
| `lean/MegaDreifachV3/KatRun.lean` | Runs the compiled emitted code on every vector: 8 `Hash` messages (and `MegaDreifach`, `pad_message` length), the `hash_deck` vector, all 8 `body_vectors` (`HashDeckBody`, `MegaDreifachBody`, `HashDeckBodyFrom` at IV-COOK12) and the IV-COOK12 digest: 52 checks, and it fails unless exactly 52 ran | CI `megadreifach-v3-lean` (`lake exe megadreifach_v3_kat`; `vectors/kat_negatives.py` plants a bad digest and empty vector lists and requires the run to fail) |

What a green run means: the Lean build of the v3 sudo agrees with the published v3 vectors when
compiled and run. It is not a kernel proof, not a proof that the emitted Lean matches the sudo
(that is trusted, see [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md)), and not a security claim. The KAT
JSON is generated from the sudoc JS build of the same sudo (`kats/regen_v3.mjs`), so the KAT run
compares two builds of one source, not two independent implementations.

## Link 2: the layers shared with v2, then the v3 card phase

[`lean/MegaDreifachV3/Link2/Shared.lean`](lean/MegaDreifachV3/Link2/Shared.lean) states, for
the **v3** emitted functions, `compose_refines`, `face_move_refines`, `face_turn_refines` and
`inverse_refines`. Their proofs are the v2 lemmas, re-elaborated against this package's
`Generated/` by the `MegaDreifachLink` lib (`lakefile.toml`, explicit roots: 63 v2 modules,
exactly their own import closure, that elaborate against the v3 emit; with the 17 v3 modules
the package builds 80 modules, plus the `Generated/` package). The model side is the v2 position algebra,
which v3 keeps. These four functions are not exports.

[`lean/MegaDreifachV3/Link2/Codec.lean`](lean/MegaDreifachV3/Link2/Codec.lean) states, for the
v3 byte codecs, `pad_message_refines` (on `PadWf`), `pad_message_refines_array`,
`require_permutation_refines` (on permutations of `0..51`; it returns its input),
`require_permutation_refines_array`, `position_to_bytes_refines_gen` (the digest encoding, on
every position with bijective corner and edge tables), `position_to_bytes_refines` (under the
v2 side conditions `PosBytesWf`), `phi_chunk_refines`, `phi_chunk_refines_array`,
`phi_inv_refines` and `phi_inv_refines_array`. Same method: the v2 lemmas, whose step lemmas
take the `.sudo` assert line as a parameter (the emitter writes it into every `sudoAssert`;
v2 and v3 differ there), re-elaborated against this package's `Generated/`.

The v3 card phase. [`lean/MegaDreifachV3/Em.lean`](lean/MegaDreifachV3/Em.lean) is a
typed Lean model of the v3 sudo's `lowest_nbr_index` .. `dm_step`, a transliteration on the v2
position algebra. Like v2's `MegaDreifach.Em`, it is hand-written, so its agreement with the
emitted code is what Link 2 proves. The two piece searches (`edge_face_of`, `corner_face_of`)
are `Option`-valued in the model, and `none` is the emitted code's trap.

**What Link 2 does and does not check.** Link 2 proves only generated = model: the code
emitted from the sudo computes the same as `Em.lean`. It does not compare the sudo or the model
with the SPEC prose, so a deviation of the sudo from SPEC §5 would be transliterated into the
model and still pass. To make the model easy to check against SPEC §5 by reading,
[`lean/MegaDreifachV3/EmReading.lean`](lean/MegaDreifachV3/EmReading.lean) proves, about the
model only:
- `edgeFaceOf_spec` and `cornerFaceOf_spec`: a successful piece search returns a face of the
  slot holding the named piece, and that face shows the asked-for colour `x`.
- `turnedFace_countUp` and `turnedFace_king`: a card step's first turn counts up from the base
  face by the rank (`countUp`, SPEC §5.1: r steps up the colour cycle, after Q comes A), or takes
  the opposite face for a King. `echoColour_countUp`: the echo colour counts up from X by Y.
- `cardStep_g_last`, `dealFold_g_last`, `echoRun_g_last` and `emBlock_any_counters`: the cost
  counters never affect the position or the last face, so `emBlock` is the same from any
  starting counter values.

The card-phase layers:
- `triples_ok` (`Link2/CardFacts.lean`, kernel `decide`). For every colour `c` and suit amount
  `k ∈ 1..4`, `suit_nbrs c k = (n, n2)` names a real edge `(c, n)` and a real corner
  `(c, n, n2)`, which `corner_slot` finds. These are the side conditions of the piece searches.
- `lowest_nbr_index_refines` and `suit_nbrs_refines` (`Link2/CardTables.lean`, kernel
  `decide!` tables): exact on every colour and every `k ∈ 1..4`.
- `edge_face_of_refines` and `corner_face_of_refines` (`Link2/FaceOf.lean`) are symbolic in
  the position. Whenever the model search returns `some y`, the emitted function returns `y`:
  its slot scan (30 or 20 slots) is driven by `chain_loop`, and its asserts pass. When the
  model search returns `some` (the found-invariant) is proved separately.
- The found-invariants (`Link2/FaceOfFound.lean`):
  - `edgeFaceOf_found` and `cornerFaceOf_found`: on a position whose edge (or corner)
    table is injective, hence bijective by pigeonhole, the search returns `some` for every
    colour of the named piece. The corner case uses `corner_cover`, a finite `decide` check
    that every slot and twist show all three colour indices.
  - With `triples_ok`, `card_edge_found` and `card_corner_found`: for every colour `c` and
    `k ∈ 1..4`, the edge `(c, n)` and the corner `(c, n, n2)` have slots, and their `c`- and
    `n`-coloured stickers are found.
- The counted run state and one card step (`Link2/RunStep.lean`). `turn_run_refines`,
  `count_find_refines`, `count_relook_refines` and `count_register_looks_refines` hold while
  the counter update fits in an Int64. `card_colour_refines` is exact on every card number.
  `card_step_refines`: on a position with bijective corner and edge tables, with all five
  counters at most `counterCap` (2^40, far above any run), the emitted `card_step` returns the
  model `cardStep` for every base face, rank ≤ 12, `k ∈ 1..4` and colour. These hypotheses are
  sufficient, not necessary (a rank above 12 takes the King branch on both sides); they cover
  every card step a deal or an echo makes.
- `em_run` and `em_block` (`Link2/EmRun.lean`). `echo_colour_refines` holds on every position
  with bijective tables and every held card. `em_run_refines` and `em_block_refines`: on such a
  position and a deal of at least 52 cards, each `< 52` (sufficient conditions; every caller
  passes a permutation of `0..51`), the emitted functions return the
  model `emRun` / `emBlock`. Both loops (52 card steps, then 26 echoes) are driven by
  `chain_loop`. A card step keeps bijective tables and adds at most 10 to each counter, an echo
  at most 12, so every iteration meets the `card_step_refines` side conditions. `emBlock_inj`:
  `E_m` keeps bijective tables.
  `dm_step_refines`: the sudo's Davies–Meyer step
  `dm_step(h, deal) = compose(h, em_block(h, deal))` (used by `Hash`, `HashDeckBody` and
  `HashDeckBodyFrom`) is the model `dmStep`, under the same conditions. `dmStep_inj`: it
  keeps bijective tables.
- `Hash` (`Link2/VHash.lean`). `iv_cook12_refines`: the emitted IV is `Em.ivCook12` (v3 keeps
  the v2 IV). `v_Hash_refines` (on `PadWf`): the emitted `Hash` returns `vhashAlg msg`, i.e. pad,
  28-byte blocks, `phiUnrank ∘ fromBE`, Davies–Meyer with the v3 step
  `dmStep` (the sudo's `dm_step`) from `ivCook12`, then the 29-byte rank digest. Every chaining
  value has bijective tables, so `dm_step_refines` and `position_to_bytes_refines_gen` apply.
- `HashDeck` and the body exports (`Link2/VHashDeck.lean`). `v_HashDeck_refines` (on
  `PhiInvWf`): `HashDeck(deal) = Hash(φ⁻¹(deal))`, the algebraic hash of the deal's 28-byte
  Lehmer rank. `v_HashDeck_two_blocks`: that is one v3 Davies–Meyer block keyed by the deal
  itself from `ivCook12` (via the φ round trip `phiUnrank_lehmerRank` of v2's PhiInv), then the fixed pad
  block `deckPadBlock`. `body_from_refines`, `v_HashDeckBody_refines` and
  `v_HashDeckBodyFrom_refines`: on a permutation of `0..51` (and, for `BodyFrom`, a chaining
  value with bijective tables) the digest of `dmStep h deal`.
  Scope: the body exports are stated on `embed deal` only (there are no `_array` forms), and
  `HashDeckBodyFrom` / `MegaDreifachBodyFrom` only for chaining values of the form `embedPos h`
  (an emitted `Position` record that is not such an embedding is not covered).

Not in the roots: the v2 grip and card-phase layers (EmGrip, EmSpin, EmRecipe, EmStep, EmInv,
EmBlock, EmIv, InjInv, VHash, VHashDeck), which name v2-only emitted functions. The generic
lemmas v3 needs from those layers live in version-neutral v2 modules that both versions import:
InjPos (`injPos_faceTurn`, `injPos_compose`), VHashCommon (the chunk-copy loop, `padWf_toBE28`,
`deckPadBlock`), PhiInv (the φ round trip `phiUnrank_lehmerRank`) and Compose
(`identity_refines`). `unfold_matchers` (used by PadRef) is in the shared `proofs/audit` package.

## Link 2 status of each export

Every `export func` of the v3 sudo, and its Link 2 theorem.

| Emitted function | Link 2 theorem |
| --- | --- |
| `pad_message` | `pad_message_refines` (on `PadWf`) |
| `require_permutation` | `require_permutation_refines` (on permutations of `0..51`) |
| `position_to_bytes` | `position_to_bytes_refines_gen` (bijective cp and ep) |
| `Hash` | `v_Hash_refines` (on `PadWf`), `v_Hash_refines_array` |
| `MegaDreifach` | `v_MegaDreifach_refines` (on `PadWf`) |
| `HashDeck` | `v_HashDeck_refines` (on `PhiInvWf`), `v_HashDeck_refines_array`, `v_HashDeck_two_blocks` |
| `MegaDreifachDeck` | `v_MegaDreifachDeck_refines` (on `PhiInvWf`) |
| `HashDeckBody` | `v_HashDeckBody_refines` (on permutations of `0..51`; no `_array` form) |
| `MegaDreifachBody` | `v_MegaDreifachBody_refines` (on permutations of `0..51`; no `_array` form) |
| `HashDeckBodyFrom` | `v_HashDeckBodyFrom_refines` (permutations of `0..51`, chaining value `embedPos h` with bijective tables; no `_array` form) |
| `MegaDreifachBodyFrom` | `v_MegaDreifachBodyFrom_refines` (same) |

## Where this sits

- v3 is the current MegaDreifach (v2 deprecated; see PR #181 for the switch). v3 reuses the v2
  model and the version-neutral v2 Link 2 modules (InjPos, VHashCommon, Sudo, PhiInv, Compose,
  among the `MegaDreifachLink` roots); this PR moved shared lemmas into those modules, but v2's
  statements are otherwise unchanged and its audit (`check_axioms.py megadreifach`) is 2745.
  Its dependents (DoubleDeal-CBC-HMAC, Scramble and BS reuse its Link 2 runtime lemmas) keep
  their audit counts. Moving v3 into `proofs/megadreifach/` and v2 into `proofs/deprecated/` is
  a separate step.
- The emitted module is `Megadreifach`, the same name as the v1 and v2 emits; each lives in its
  own Lake package and they are never imported together.
- Gates: `scan_sorry.py --root proofs/megadreifach-v3/lean --exclude Generated`, and
  `check_axioms.py megadreifach-v3` (every theorem in `MegaDreifachV3.*`, plus the
  Lean-generated equation/match lemmas of the KAT runner's definitions). Its
  `--selftest` checks the table above against the sudo's exports.

Build locally one package at a time: `lake build` in `lean/Generated`, then in `lean`.
