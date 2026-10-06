/-
  Axiom audit, Mathlib side. Run by `python3 ../check_axioms.py security`.

  Prints the axioms of EVERY theorem declared in a `DoubleDealSecurity.*`
  module, private ones included (no hand-written list), then `audited N`. The checker allows only propext,
  Classical.choice and Quot.sound; its KNOWN_SORRY set is empty, so no theorem may use
  `sorryAx` (`roundBody_covariant_iff_id` is proved in the heavy library; the default
  library has the `_of_covariant` reductions). Any other axiom, any theorem using
  `sorryAx`, an `axiom` declared in the package (used or not), or a stale KNOWN_SORRY
  entry fails.

  The heavy library `DoubleDealSecurityHeavy` (kernel witnesses, not a default
  target) is NOT imported here; it is audited separately by `AxiomsHeavy.lean`
  (`check_axioms.py security-heavy`, CI job `doubledeal-security-heavy`).
-/
import DoubleDealSecurity
import AuditAll

#audit_all DoubleDealSecurity
