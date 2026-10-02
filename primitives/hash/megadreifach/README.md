<!-- Owns: the file map of this directory. Maintenance rules: ../../../DOCS.md. -->
# MegaDreifach

Toy three-megaminx Merkle–Damgård hash. Not for real use. Naming, scope and non-goals: [`SPEC.md`](SPEC.md). The current version is v2; v1 is deprecated (why: [`v1/SPEC.md`](v1/SPEC.md) banner); v3 is a candidate (what changes and why: [`v3/SPEC.md`](v3/SPEC.md) banner).

| File | Role |
| --- | --- |
| [`SPEC.md`](SPEC.md) | Normative specification, v2 (`Hash` / `HashDeck` / `HashDeckBody`, plus `MegaDreifach*` aliases; `*BodyFrom` is the free-start analysis surface) |
| [`megadreifach.sudo`](megadreifach.sudo) | Conformance implementation, v2 |
| [`kats/megaminx_hash_kats_v2.json`](kats/megaminx_hash_kats_v2.json) | v2 KAT file (same inputs and layout as v1) |
| [`v1/SPEC.md`](v1/SPEC.md), [`v1/megadreifach.sudo`](v1/megadreifach.sudo) | Frozen, deprecated v1. The sudo keeps the v1 file name so the Lean emitted from it stays the module `Megadreifach` |
| [`v3/SPEC.md`](v3/SPEC.md), [`v3/megadreifach.sudo`](v3/megadreifach.sudo) | Candidate v3: the SPEC explains it (only the card phase `W` of `E_m` changes); the sudo is the normative runnable spec, and a mismatch is a bug in the prose. The sudo keeps the file name, so its JS build is `megadreifach.mjs` with the same exports |
| [`kats/megaminx_hash_kats_v3.json`](kats/megaminx_hash_kats_v3.json), [`kats/regen_v3.mjs`](kats/regen_v3.mjs) | v3 KAT file (v2's message inputs, plus 8 `HashDeckBody` vectors) and its generator from the sudoc JS build (`--check` in `tools/generate-demos.sh`) |
| [`kats/megaminx_hash_kats_v1.json`](kats/megaminx_hash_kats_v1.json) | v1 KAT file (pad / IV / `\|G\|` metadata; v1 Hash hexes), formerly `kats/megaminx_hash_kats.json`; contents unchanged |

HMAC-MegaDreifach is specified with [DoubleDeal-CBC-HMAC](../../aead/doubledeal-cbc-hmac/README.md). Conformance test command: [root README](../../../README.md#build-and-test); the frozen v1 sudo builds the same way with its own `-o` directory. Proofs (v2): [`proofs/megadreifach/`](../../../proofs/megadreifach/README.md); v3 evidence and design analysis: [`proofs/megadreifach/security/v3/`](../../../proofs/megadreifach/security/v3/README.md); frozen v1 proofs: [`proofs/deprecated/megadreifach-v1/`](../../../proofs/deprecated/megadreifach-v1/README.md).
