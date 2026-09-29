/-
  HEAVY (not in the default build target): the unconditional forms of the
  multi-round characteristic bounds of `DoubleDealSecurity/TrailBound.lean`, obtained by
  plugging in the kernel-checked GridCycle checks `check3_KC` / `check3_KS`
  (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`). No new `decide!` here.
  Same model and caveats as `DoubleDealSecurity/TrailBound.lean`: INDEPENDENT UNIFORM round keys (not the
  PassKey schedule), one constant-σ characteristic (not a differential), no
  final no-mix round. Not a bit-security claim.
-/
import DoubleDealSecurity.TrailBound
import DoubleDealSecurityHeavy.GridCycleSurvival

namespace DoubleDeal.Security.TrailBound

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key)

/-- (PROVED) Every `σ ≠ 1`, independent uniform round keys, every starting deck `y`:
    at most `(52!)^R / 64^R` of the `(52!)^R` key tuples make the pair `(y, σ·y)`
    follow the constant-`σ` characteristic through `R` rounds. -/
theorem trail_card_le_64 (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (y : Fin 52 → Nat)
    (hy : IsDeck y) :
    64 ^ R * (univ.filter fun K : Fin R → Key => Trail σ R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_64_of_check GCSurvival.check3_KC GCSurvival.check3_KS σ h1 R y hy

/-- (PROVED) Nontrivial `v10Sym a x`: at most `(52!)^R / 4420^R` key tuples. -/
theorem trail_card_le_4420_v10Sym (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) (y : Fin 52 → Nat) (hy : IsDeck y) :
    4420 ^ R * (univ.filter fun K : Fin R → Key => Trail (v10Sym a x) R y K).card ≤
      Nat.factorial 52 ^ R :=
  trail_card_le_4420_v10Sym_of_check GCSurvival.check3_KC GCSurvival.check3_KS a x hne R y hy

end DoubleDeal.Security.TrailBound
