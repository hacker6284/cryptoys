/-
  Axiom audit of the MegaDreifach v3 package. Run by the shared gate
  `python3 ../../doubledeal/check_axioms.py megadreifach-v3` (after `lake build`). Prints the
  axioms of EVERY theorem declared in a `MegaDreifachV3.*` module, private ones included,
  then `audited N`. Only propext, Classical.choice and Quot.sound are allowed. Until Link 2
  lands the package states no theorems; N counts only the equation/match lemmas Lean
  generates for the KAT runner's definitions.
-/
import MegaDreifachV3
import AuditAll

#audit_all MegaDreifachV3
