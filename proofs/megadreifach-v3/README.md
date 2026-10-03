<!-- Owns: the MegaDreifach v3 Lean package (proofs/megadreifach-v3/): what is checked, what is not, and the Link 2 status of each v3 export. Maintenance rules: ../../DOCS.md. -->
# MegaDreifach v3 (ZP26) in Lean

Lean for MegaDreifach v3, the ZP26 card phase
([`primitives/hash/megadreifach/v3/SPEC.md`](../../primitives/hash/megadreifach/v3/SPEC.md),
[`v3/megadreifach.sudo`](../../primitives/hash/megadreifach/v3/megadreifach.sudo)).
The sudo is the source of truth. Link 2 (the emitted code equals a hand-written model) is
started: only the shared position layer is linked so far. **No export is linked yet.**

| Piece | What it is | Checked by |
| --- | --- | --- |
| `lean/Generated/` | Lean emitted from the v3 sudo by `proofs/emit_lean.sh` (target `megadreifach-v3`), with `EMITTED_FROM.json`. Do not edit. | CI `generated-fresh` (`emit_lean.sh --check`); CI `megadreifach-v3-generated` builds it and runs the 23 sudo tests (TAP) |
| `lean/MegaDreifachV3/Vectors.lean` | The v3 KAT file `kats/megaminx_hash_kats_v3.json` as Lean data, written by `vectors/json_to_lean.py` | CI `megadreifach-v3-lean` (`json_to_lean.py --check`) |
| `lean/MegaDreifachV3/KatRun.lean` | Runs the compiled emitted code on every vector: 8 `Hash` messages (and `MegaDreifach`, `pad_message` length), the `hash_deck` vector, all 8 `body_vectors` (`HashDeckBody`, `MegaDreifachBody`, `HashDeckBodyFrom` at IV-COOK12) and the IV-COOK12 digest: 52 checks | CI `megadreifach-v3-lean` (`lake exe megadreifach_v3_kat`) |

What a green run means: the Lean build of the v3 sudo agrees with the published v3 vectors when
compiled and run. It is not a kernel proof, not a proof that the emitted Lean matches the sudo
(that is trusted, see [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md)), and not a security claim. The KAT
JSON is generated from the sudoc JS build of the same sudo (`kats/regen_v3.mjs`), so the KAT run
compares two builds of one source, not two independent implementations.

## Link 2 so far: the layers shared with v2

[`lean/MegaDreifachV3/Link2/Shared.lean`](lean/MegaDreifachV3/Link2/Shared.lean) states, for
the **v3** emitted functions, `compose_refines`, `face_move_refines`, `face_turn_refines` and
`inverse_refines`. Their proofs are the v2 lemmas, re-elaborated against this package's
`Generated/` by the `MegaDreifachLink` lib (`lakefile.toml`, explicit roots: 61 v2 modules
that elaborate against the v3 emit). The model side is the v2 position algebra,
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

The v3 card phase starts here. [`lean/MegaDreifachV3/Em.lean`](lean/MegaDreifachV3/Em.lean) is a
typed Lean model of the v3 sudo's `lowest_nbr_index` .. `em_block`, a transliteration on the v2
position algebra. Like v2's `MegaDreifach.Em`, it is hand-written, so its agreement with the
emitted code is what Link 2 proves. The two piece searches (`edge_face_of`, `corner_face_of`)
are `Option`-valued in the model, and `none` is the emitted code's trap. So far:
- `triples_ok` (`Link2/CardFacts.lean`, kernel `decide`). For every colour `c` and suit amount
  `k ∈ 1..4`, `suit_nbrs c k = (n, n2)` names a real edge `(c, n)` and a real corner
  `(c, n, n2)`, which `corner_slot` finds. These are the side conditions of the piece searches.
- `lowest_nbr_index_refines` and `suit_nbrs_refines` (`Link2/CardTables.lean`, kernel
  `decide!` tables): exact on every colour and every `k ∈ 1..4`.

Not in the roots: the v2 grip and card-phase layers (EmGrip, EmSpin, EmRecipe, EmStep, EmInv,
EmBlock, EmIv, InjInv, VHash, VHashDeck), which name v2-only emitted functions. The v3 card
phase (`em_run`, `em_block`) and `Hash`, `HashDeck`, `HashDeckBody` are not linked yet.

## Link 2 status of each export

Every `export func` of the v3 sudo, and its Link 2 theorem.

| Emitted function | Link 2 theorem |
| --- | --- |
| `pad_message` | `pad_message_refines` (on `PadWf`) |
| `require_permutation` | `require_permutation_refines` (on permutations of `0..51`) |
| `position_to_bytes` | `position_to_bytes_refines_gen` (bijective cp and ep) |
| `Hash` | none yet |
| `MegaDreifach` | none yet |
| `HashDeck` | none yet |
| `MegaDreifachDeck` | none yet |
| `HashDeckBody` | none yet |
| `MegaDreifachBody` | none yet |
| `HashDeckBodyFrom` | none yet |
| `MegaDreifachBodyFrom` | none yet |

## Where this sits

- v3 is the current MegaDreifach (v2 deprecated; see PR #181 for the switch). The v2 package
  `proofs/megadreifach/` and its dependents (DoubleDeal-CBC-HMAC, Scramble and BS reuse its
  Link 2 runtime lemmas) are unchanged. Moving v3 into `proofs/megadreifach/` and v2 into
  `proofs/deprecated/` is a separate step.
- The emitted module is `Megadreifach`, the same name as the v1 and v2 emits; each lives in its
  own Lake package and they are never imported together.
- Gates: `scan_sorry.py --root proofs/megadreifach-v3/lean --exclude Generated`, and
  `check_axioms.py megadreifach-v3` (every theorem in `MegaDreifachV3.*`, plus the
  Lean-generated equation/match lemmas of the KAT runner's definitions). Its
  `--selftest` checks the table above against the sudo's exports.

Build locally one package at a time: `lake build` in `lean/Generated`, then in `lean`.
