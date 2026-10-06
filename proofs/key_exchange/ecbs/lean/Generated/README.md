<!-- Owns: what this Generated/ package is and that its emitted files are not hand-edited (this README is hand-written; tools/emit_lean.py keeps it). Maintenance rules: ../../../../../DOCS.md. -->
# Generated ECBS Lean

**Do not edit these files by hand.** They are produced from
[`primitives/key_exchange/ecbs/ecbs.sudo`](../../../../../primitives/key_exchange/ecbs/ecbs.sudo)
by `proofs/emit_lean.sh ecbs`.

This directory is a standalone Lake package (its own `lakefile.lean`). CI checks that
it matches a fresh emit (`proofs/emit_lean.sh --check`), builds it, and runs the
emitted sudo tests (`ecbs_test`, TAP): the `ecbs` row of the `generated` matrix in
`.github/workflows/proofs.yml`. sudocode#18
(https://github.com/hacker6284/sudocode/pull/18) makes `Ecbs.lean` elaborate in a CI
budget; it fixes https://github.com/hacker6284/sudocode/issues/17. Dated attempts
that did not finish, at the previous pin, are in
[`evidence/README.md`](../../evidence/README.md#lean). There is no Link 2 package for
ECBS yet: nothing proves facts about these definitions (see
[`proofs/key_exchange/ecbs/README.md`](../../README.md)). `lake-manifest.json` is
committed so `lean-action` can `lake build`; do not gitignore it.

See [`proofs/ANTI_DRIFT.md`](../../../../ANTI_DRIFT.md).
