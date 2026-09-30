<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../DOCS.md. -->
# Generated MegaDreifach Lean

**Do not edit these files by hand.** They are produced from the current **v2**
[`primitives/hash/megadreifach/megadreifach.sudo`](../../../../primitives/hash/megadreifach/megadreifach.sudo)
by `proofs/emit_lean.sh` (target `megadreifach`). The frozen v1 emit lives in
[`proofs/deprecated/megadreifach-v1/lean/Generated/`](../../../deprecated/megadreifach-v1/lean/Generated/README.md).

This directory is a standalone Lake package (its own `lakefile.lean`).
The proof-only `MegaDreifach` library next door requires it by path (package `sudo`);
Link 2 imports the emitted module `Megadreifach`.
`lake-manifest.json` is committed (same as `proofs/megadreifach/lean/`) so
`lean-action` can `lake build`; do not gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../ANTI_DRIFT.md).
