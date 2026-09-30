/-
  Security layer (reductions and structural facts; NOT a security claim).
  See `proofs/megadreifach/security/REPORT.md`.

  Every module here is independent of the grip rule: `MDGeneric`,
  `MDReduction`, `StepWord`, `Parity`, `DigestInj`, `IdealCount`.  No
  statement mentions how the grip is chosen or which piece is read.  Each
  module docstring says which lemmas unfold the v2 `Em` definitions and would
  need repair if E_m changes.

  The results about the v1 grip rule (`CornerDriven`, `FreeStart`,
  `SwapCollision`) are proofs about the deprecated v1 hash.  They live, frozen,
  in `proofs/deprecated/megadreifach-v1/` (namespace `MegaDreifachV1`), built
  against Lean emitted from the frozen `v1/megadreifach.sudo`.  Nothing in
  this package states a weakness (or a strength) of v2.

  Imports follow use:
    MDGeneric → MDReduction;  StepWord (Em step lemmas, `Word`);
    MDReduction, StepWord → Parity → DigestInj;  MDReduction → IdealCount.
-/
import MegaDreifach.Security.MDGeneric
import MegaDreifach.Security.MDReduction
import MegaDreifach.Security.StepWord
import MegaDreifach.Security.Parity
import MegaDreifach.Security.DigestInj
import MegaDreifach.Security.IdealCount
