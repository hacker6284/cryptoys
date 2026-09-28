/-
  Axiom audit of the default library. Run by the shared gate
  `python3 ../../doubledeal/check_axioms.py megadreifach` (after `lake build`). Prints the axioms of EVERY theorem declared in a
  `MegaDreifach.*` module, private ones included (no hand-written list), then
  `audited N`. The checker allows only propext, Classical.choice and Quot.sound;
  any other axiom (sorryAx, Lean.ofReduceBool from native_decide, a user axiom),
  an `axiom` declared in the package, or an unimported module fails.

  The heavy library `MegaDreifachHeavy` (the 8 KAT kernel witnesses, not a
  default target) is NOT imported here; it is audited by `AxiomsHeavy.lean`
  (`check_axioms.py megadreifach-heavy`, CI job `megadreifach-heavy`).
  `#audit_all` is the shared command of the core-only package `proofs/audit`.
-/
import MegaDreifach
import AuditAll

#audit_all MegaDreifach
