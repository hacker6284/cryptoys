<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../../DOCS.md. -->
# Generated MegaDreifach v1 Lean (frozen, deprecated)

**Do not edit these files by hand.** They are produced from the frozen, deprecated **v1**
[`primitives/hash/megadreifach/v1/megadreifach.sudo`](../../../../../primitives/hash/megadreifach/v1/megadreifach.sudo)
by `proofs/emit_lean.sh` (target `megadreifach-v1`). The module is `Megadreifach` (the file
stem), the same name as the deprecated v2 module in `proofs/megadreifach/lean/Generated/`; the two
live in separate Lake packages and are never imported together.

This directory is a standalone Lake package (its own `lakefile.lean`, package `sudo`).
The frozen v1 proof package next door (`MegaDreifachV1`, [`../../README.md`](../../README.md))
requires it by path. `lake-manifest.json` is committed so `lean-action` can `lake build`;
do not gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../../ANTI_DRIFT.md).
