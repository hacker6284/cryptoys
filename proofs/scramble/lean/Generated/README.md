<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../DOCS.md. -->
# Generated Scramble Lean

**Do not edit these files by hand.** They are produced from
[`primitives/hash/scramble/scramble.sudo`](../../../../primitives/hash/scramble/scramble.sudo)
by `proofs/emit_lean.sh`.

This directory is a standalone Lake package (its own `lakefile.lean`).
There is no algebraic proof package next door. `lake-manifest.json` is
committed so `lean-action` can `lake build`; do not gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../ANTI_DRIFT.md).
