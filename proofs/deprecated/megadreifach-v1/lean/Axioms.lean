/-
  Axiom audit of the frozen v1 package. Run by the shared gate
  `python3 ../../../doubledeal/check_axioms.py megadreifach-v1-deprecated` (after
  `lake build`). Prints the axioms of EVERY theorem declared in a
  `MegaDreifachV1.*` module, private ones included, then `audited N`. Only
  propext, Classical.choice and Quot.sound are allowed.
-/
import MegaDreifachV1
import AuditAll

#audit_all MegaDreifachV1
