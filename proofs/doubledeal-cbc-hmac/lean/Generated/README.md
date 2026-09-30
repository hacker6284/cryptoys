<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../DOCS.md. -->
# Generated DoubleDeal-CBC-Sandwich v2 Lean

**Do not edit these files by hand.** They are produced from
[`primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo`](../../../../primitives/aead/doubledeal-cbc-hmac/doubledeal_cbc_hmac.sudo)
(DoubleDeal-CBC-Sandwich v2; the directory and file keep their v1 names) by
`proofs/emit_lean.sh cbc-hmac`, with MegaDreifach and DoubleDeal imported via
`-I primitives/hash/megadreifach -I primitives/cipher/doubledeal`.

This directory is a standalone Lake package (its own `lakefile.lean`).
There is no algebraic proof package next door: v2 has no Link 2 yet (the frozen
v1 Link 2 package is `proofs/deprecated/doubledeal-cbc-hmac-v1/`).
`lake-manifest.json` is committed so `lean-action` can `lake build`; do not gitignore it.

This is not Link 2, not emitter soundness, and not an AEAD security theorem.

See [`proofs/ANTI_DRIFT.md`](../../../ANTI_DRIFT.md).
