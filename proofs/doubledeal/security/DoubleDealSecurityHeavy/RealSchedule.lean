/-
  HEAVY (not in the default build target): the unconditional form of the real-schedule
  characteristic bound of `DoubleDealSecurity/RealSchedule.lean`, obtained by plugging in
  the kernel-checked GridCycle checks `check3_KC` / `check3_KS`
  (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`). No new `decide!` here.
  Same model and caveats as `DoubleDealSecurity/RealSchedule.lean`: uniform master key,
  real PassKey schedule; ONE round's bound for every `R ≥ 1` (no gain beyond round 1:
  1/64, not (1/64)^R); one constant-σ characteristic, not a differential; no final no-mix
  round; `rounds` not linked to `encryptN`. Not a bit-security claim.
-/
import DoubleDealSecurity.RealSchedule
import DoubleDealSecurityHeavy.GridCycleSurvival

namespace DoubleDeal.Security.RealSchedule

open DoubleDeal Relabel Finset
open DoubleDeal.Security.TrailBound (Trail)

/-- (PROVED) Every `σ ≠ 1`, real PassKey schedule, every `R ≥ 1`, every starting deck
    `y`: at most `52!/64` of the `52!` master keys make `(y, σ·y)` follow the constant-σ
    characteristic through `R` rounds. ONE round's bound (probability ≤ 1/64 for every
    `R ≥ 1`), not `(1/64)^R`. -/
theorem realTrail_card_le_64 (σ : Relabel) (h1 : σ ≠ 1) (R : ℕ) (hR : 0 < R)
    (y : Fin 52 → Nat) (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => Trail σ R y (realKeys R π)).card ≤
      Nat.factorial 52 :=
  realTrail_card_le_64_of_check GridCycleSurvival.check3_KC GridCycleSurvival.check3_KS
    σ h1 R hR y hy

end DoubleDeal.Security.RealSchedule
