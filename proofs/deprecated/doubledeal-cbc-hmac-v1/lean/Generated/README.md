<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../../DOCS.md. -->
# Generated DoubleDeal-CBC-HMAC v1 Lean (frozen)

**Do not edit these files by hand.** They are produced from the frozen
[`primitives/aead/doubledeal-cbc-hmac/v1/doubledeal_cbc_hmac.sudo`](../../../../../primitives/aead/doubledeal-cbc-hmac/v1/doubledeal_cbc_hmac.sudo)
by `proofs/emit_lean.sh cbc-hmac-v1`, with MegaDreifach imported via
`-I primitives/hash/megadreifach`. v1 is superseded by DoubleDeal-CBC-Sandwich v2.

This directory is a standalone Lake package (its own `lakefile.lean`).
The Link 2 package next door (`../`) proves these emitted functions equal a
hand-written model. `lake-manifest.json` is committed so `lean-action` can
`lake build`; do not gitignore it.

This is not Link 2, not emitter soundness, and not an AEAD security
theorem.

See [`proofs/ANTI_DRIFT.md`](../../../../ANTI_DRIFT.md).
