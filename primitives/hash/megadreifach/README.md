<!-- Owns: the file map of this directory. Maintenance rules: ../../../DOCS.md. -->
# MegaDreifach

Toy three-megaminx Merkle–Damgård hash. Not for real use. Naming, scope and non-goals: [`SPEC.md`](SPEC.md). The current version is v2; v1 is deprecated (why: [`v1/SPEC.md`](v1/SPEC.md) banner).

| File | Role |
| --- | --- |
| [`SPEC.md`](SPEC.md) | Normative specification, v2 (`Hash` / `HashDeck` / `HashDeckBody`, plus `MegaDreifach*` aliases; `*BodyFrom` is the free-start analysis surface; `trace_hash` is the demo's animation trace) |
| [`megadreifach.sudo`](megadreifach.sudo) | Conformance implementation, v2 |
| [`kats/megaminx_hash_kats_v2.json`](kats/megaminx_hash_kats_v2.json) | v2 KAT file (same inputs and layout as v1) |
| [`v1/SPEC.md`](v1/SPEC.md), [`v1/megadreifach.sudo`](v1/megadreifach.sudo) | Frozen, deprecated v1. The sudo keeps the v1 file name so the Lean emitted from it stays the module `Megadreifach` |
| [`kats/megaminx_hash_kats_v1.json`](kats/megaminx_hash_kats_v1.json) | v1 KAT file (pad / IV / `\|G\|` metadata; v1 Hash hexes), formerly `kats/megaminx_hash_kats.json`; contents unchanged |

HMAC-MegaDreifach is specified with [DoubleDeal-CBC-HMAC](../../aead/doubledeal-cbc-hmac/README.md). Conformance test command: [root README](../../../README.md#build-and-test); the frozen v1 sudo builds the same way with its own `-o` directory. Proofs (v2): [`proofs/megadreifach/`](../../../proofs/megadreifach/README.md); frozen v1 proofs: [`proofs/deprecated/megadreifach-v1/`](../../../proofs/deprecated/megadreifach-v1/README.md).
