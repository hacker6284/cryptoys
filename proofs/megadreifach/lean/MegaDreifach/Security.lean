/-
  Security layer (reductions and proved structural weaknesses; NOT a security
  claim).  See `proofs/megadreifach/security/REPORT.md`.

  Two kinds of module:

  * Results about v1 of the grip rule (Recipe A reads only corner cubies):
    `CornerDriven`, `FreeStart`.  They document why the rule is being
    redesigned.  Every theorem that uses the corner-only read
    (`recipeA_sameCorners`) is in one of these two files.
  * Independent of the grip rule: `MDGeneric`, `MDReduction`, `Parity`,
    `DigestInj`, `IdealCount`.  No statement mentions the grip rule and no
    proof uses `recipeA_sameCorners`.  Each module docstring says which
    lemmas unfold the current `Em` definitions and would need repair if E_m
    changes.

  The import chain is linear: MDGeneric → MDReduction → CornerDriven → Parity
  → DigestInj → IdealCount → FreeStart.  `Parity` uses only `g2Step_fst` from
  `CornerDriven` (a G2 step left-multiplies by a word that depends on the grip
  and the card, whatever the grip rule is); it does not use the corner-only
  read.
-/
import MegaDreifach.Security.MDGeneric
import MegaDreifach.Security.MDReduction
import MegaDreifach.Security.CornerDriven
import MegaDreifach.Security.Parity
import MegaDreifach.Security.DigestInj
import MegaDreifach.Security.IdealCount
import MegaDreifach.Security.FreeStart
