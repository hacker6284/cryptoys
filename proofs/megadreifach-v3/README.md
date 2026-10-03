<!-- Owns: the MegaDreifach v3 Lean package (proofs/megadreifach-v3/): what is checked, what is not, and the Link 2 status of each v3 export. Maintenance rules: ../../DOCS.md. -->
# MegaDreifach v3 (ZP26) in Lean

Lean for MegaDreifach v3, the ZP26 card phase
([`primitives/hash/megadreifach/v3/SPEC.md`](../../primitives/hash/megadreifach/v3/SPEC.md),
[`v3/megadreifach.sudo`](../../primitives/hash/megadreifach/v3/megadreifach.sudo)).
The sudo is the source of truth. **This package has no theorems yet.** Link 2 (the emitted
code equals a hand-written model) is planned and not done.

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

## Link 2 status of each export

Every `export func` of the v3 sudo, and its Link 2 theorem. None exists yet.

| Emitted function | Link 2 theorem |
| --- | --- |
| `pad_message` | none yet |
| `require_permutation` | none yet |
| `position_to_bytes` | none yet |
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
  `check_axioms.py megadreifach-v3` (every theorem in `MegaDreifachV3.*`; today only 6
  Lean-generated equation/match lemmas of the KAT runner's definitions, no stated theorem). Its
  `--selftest` checks the table above against the sudo's exports.

Build locally one package at a time: `lake build` in `lean/Generated`, then in `lean`.
