/-
  Mathlib-free half of the security package: statements that need the Link 2
  refinement (`Concrete`, `Link2.Encrypt`). Kept apart because the core
  package's `DoubleDeal/PassKey.lean` declares root-level
  `Function.LeftInverse`/`RightInverse` shims that clash with Mathlib, so these
  modules cannot share an environment with `DoubleDealSecurity`.
-/
import DoubleDealSecurityLink.Decks
import DoubleDealSecurityLink.RelabelLink
