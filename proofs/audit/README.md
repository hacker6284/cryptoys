<!-- Owns: what the audit package provides and its no-dependency rule. Maintenance rules: ../../DOCS.md. -->
# audit

One small core-only Lean package with the `#audit_all Root` command
(`AuditAll.lean`). The audited packages require it by path:

- [`proofs/doubledeal/security`](../doubledeal/security/README.md) (Mathlib): `Axioms.lean`, `AxiomsHeavy.lean`
- [`proofs/megadreifach/lean`](../megadreifach/README.md) (dependency-free): `Axioms.lean`, `AxiomsHeavy.lean`
- [`proofs/deprecated/megadreifach-v1/lean`](../deprecated/megadreifach-v1/README.md) (dependency-free, frozen v1): `Axioms.lean`

`#audit_all` prints the axioms of every theorem declared under `Root`, the
`audited N` count, and errors for unloaded module files and duplicate owners.
The single gate that parses this output and applies the allowlist is
[`../doubledeal/check_axioms.py`](../doubledeal/check_axioms.py). Do not add
dependencies here: this package must stay core-only so every consumer can use it.
