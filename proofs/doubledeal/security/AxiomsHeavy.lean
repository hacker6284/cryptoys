/-
  Axiom audit of the heavy library. Run by `python3 ../check_axioms.py security-heavy`
  after `lake build DoubleDealSecurityHeavy`. Same rules as `Axioms.lean`, with no
  KNOWN_SORRY entries; the checker also requires every theorem declared in
  `DoubleDealSecurityHeavy/` to be registered in HEAVY_THEOREMS and reported here.
-/
import DoubleDealSecurityHeavy
import AuditAll

#audit_all DoubleDealSecurityHeavy
