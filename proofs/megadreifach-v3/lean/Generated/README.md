<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../DOCS.md. -->
# Generated MegaDreifach v3 Lean

**Do not edit these files by hand.** They are produced from the v3 (ZP26 card phase)
[`primitives/hash/megadreifach/v3/megadreifach.sudo`](../../../../primitives/hash/megadreifach/v3/megadreifach.sudo)
by `proofs/emit_lean.sh` (target `megadreifach-v3`). The module is `Megadreifach` (the file
stem), the same name as the v2 module in `proofs/megadreifach/lean/Generated/` and the v1
module in `proofs/deprecated/megadreifach-v1/lean/Generated/`; the three live in separate
Lake packages and are never imported together.

This directory is a standalone Lake package (its own `lakefile.lean`, package `sudo`).
The v3 package next door (`MegaDreifachV3`, [`../../README.md`](../../README.md)) requires
it by path. `lake-manifest.json` is committed so `lean-action` can `lake build`; do not
gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../ANTI_DRIFT.md).
