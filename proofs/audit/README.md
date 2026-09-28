# audit

One small core-only Lean package with the `#audit_all Root` command
(`AuditAll.lean`). The audited packages require it by path:

- `proofs/doubledeal/security` (Mathlib): `Axioms.lean`, `AxiomsHeavy.lean`
- `proofs/megadreifach/lean` (dependency-free): `Axioms.lean`, `AxiomsHeavy.lean`

`#audit_all` prints the axioms of every theorem declared under `Root`, the
`audited N` count, and errors for unloaded module files and duplicate owners.
The single gate that parses this output and applies the allowlist is
[`../doubledeal/check_axioms.py`](../doubledeal/check_axioms.py). Do not add
dependencies here: this package must stay core-only so both consumers can use it.
