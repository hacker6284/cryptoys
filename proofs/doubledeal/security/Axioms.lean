/-
  Axiom audit, Mathlib side. Run by `python3 ../check_axioms.py security`.

  Prints the axioms of EVERY theorem declared in a `DoubleDealSecurity.*`
  module, private ones included (no hand-written list), then `audited N`. The checker allows only propext,
  Classical.choice and Quot.sound, except that the theorems named in its
  KNOWN_SORRY set (the open conjecture `roundBody_covariant_iff_id` and the two
  theorems that rest on it) may also use `sorryAx`. Any other axiom, any other
  theorem using `sorryAx`, an `axiom` declared in the package (used or not), or
  a stale KNOWN_SORRY entry fails.

  The heavy library `DoubleDealSecurityHeavy` (kernel witnesses, not a default
  target) is NOT imported here; it is audited separately by `AxiomsHeavy.lean`
  (`check_axioms.py security-heavy`, CI job `doubledeal-security-heavy`).
-/
import DoubleDealSecurity
import AuditAll

#audit_all DoubleDealSecurity
