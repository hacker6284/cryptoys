<!-- Owns: the file map of this directory. Maintenance rules: ../../../DOCS.md. -->
# MegaDreifach

Toy three-megaminx Merkle–Damgård hash. Not for real use. Naming, scope and non-goals: [`SPEC.md`](SPEC.md).

| File | Role |
| --- | --- |
| [`SPEC.md`](SPEC.md) | Normative specification (`Hash` / `HashDeck` / `HashDeckBody`, plus `MegaDreifach*` aliases; `*BodyFrom` is the free-start analysis surface) |
| [`megadreifach.sudo`](megadreifach.sudo) | Conformance implementation |
| [`kats/megaminx_hash_kats.json`](kats/megaminx_hash_kats.json) | Published KAT file (pad / IV / `\|G\|` metadata; research Hash hexes) |

HMAC-MegaDreifach is specified with [DoubleDeal-CBC-HMAC](../../aead/doubledeal-cbc-hmac/README.md). Conformance test command: [root README](../../../README.md#build-and-test). Proofs: [`proofs/megadreifach/`](../../../proofs/megadreifach/README.md).
