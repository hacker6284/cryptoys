/-
  Axiom audit of the heavy library. Run by `python3 ../check_axioms.py heavy`
  after `lake build MegaDreifachHeavy`. Same rules as `Axioms.lean`.
-/
import MegaDreifachHeavy
import MegaDreifachAudit

#audit_all MegaDreifachHeavy
