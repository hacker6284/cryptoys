/-
  Security layer (reductions and proved structural weaknesses; NOT a security
  claim).  See `proofs/megadreifach/security/REPORT.md`.

  Two kinds of module:

  * Independent of the grip rule: `MDGeneric`, `MDReduction`, `StepWord`,
    `Parity`, `DigestInj`, `IdealCount`.  No statement mentions how the grip
    is chosen and no proof uses `recipeA_sameCorners`.  Each module docstring
    says which lemmas unfold the (v1) `Em` definitions and would need
    repair if E_m changes.
  * Results about the v1 grip rule ("v1": Recipe A, which reads only
    corner cubies, after the noon and Front turns): `CornerDriven`,
    `FreeStart`, `SwapCollision`.  They document why the rule is being
    redesigned.  Every theorem that uses the corner-only read
    (`recipeA_sameCorners`) is in `CornerDriven` or `FreeStart`.
    `SwapCollision` kernel-checks one concrete IV-anchored `v_Hash` collision
    of the v1 hash by evaluating the concrete `Em.g2Step`; it does not
    use `recipeA_sameCorners`.

  Imports follow use:
    MDGeneric → MDReduction;  StepWord (Em step lemmas, `Word`);
    MDReduction, StepWord → Parity → DigestInj;  MDReduction → IdealCount;
    MDReduction, StepWord → CornerDriven;  CornerDriven, Parity → FreeStart;
    SwapCollision needs only Link 2 (`VHash`, `EmIv`) and `Hex`.
  Deleting the v1 files (`CornerDriven`, `FreeStart`, `SwapCollision`) leaves
  the rule-independent ones (M3 glue, `v_Hash_collision_comp`) intact.
-/
import MegaDreifach.Security.MDGeneric
import MegaDreifach.Security.MDReduction
import MegaDreifach.Security.StepWord
import MegaDreifach.Security.Parity
import MegaDreifach.Security.DigestInj
import MegaDreifach.Security.IdealCount
import MegaDreifach.Security.CornerDriven
import MegaDreifach.Security.FreeStart
import MegaDreifach.Security.SwapCollision
