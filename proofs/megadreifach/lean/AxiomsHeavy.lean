/-
  Axiom audit of the heavy library. Run by
  `python3 ../../doubledeal/check_axioms.py megadreifach-heavy`
  after `lake build MegaDreifachHeavy`. Same rules as `Axioms.lean`.
-/
import MegaDreifachHeavy
import AuditAll

#audit_all MegaDreifachHeavy
