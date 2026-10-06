<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../../DOCS.md. -->
# Generated BS Lean

**Do not edit these files by hand.** They are produced from
[`primitives/key_exchange/bs/bs.sudo`](../../../../../primitives/key_exchange/bs/bs.sudo)
by `proofs/emit_lean.sh bs`.

This directory is a standalone Lake package (its own `lakefile.lean`).
The Link 2 package next door (`../`, library `BsLink2`) requires it by
path and proves facts about these emitted definitions without editing them;
see [`proofs/key_exchange/bs/lean/README.md`](../README.md). `lake-manifest.json` is
committed so `lean-action` can `lake build`; do not gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../../ANTI_DRIFT.md).
