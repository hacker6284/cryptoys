/-
  Axiom audit of the MegaDreifach v3 package. Run by the shared gate
  `python3 ../../doubledeal/check_axioms.py megadreifach-v3` (after `lake build`). Prints the
  axioms of EVERY theorem declared in a `MegaDreifachV3.*` module, private ones included,
  then `audited N`. Only propext, Classical.choice and Quot.sound are allowed. The v2 lemmas
  re-elaborated here (MegaDreifachLink, sources under ../../megadreifach/lean) are not under
  this root; `#print axioms` is transitive, so every one a MegaDreifachV3 theorem uses is
  still in its report.
-/
import MegaDreifachV3
import AuditAll

#audit_all MegaDreifachV3
