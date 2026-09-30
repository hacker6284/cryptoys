/-
  HEAVY (not in the default build target): the `4420` forms of the `v10Sym`-cluster
  bounds of `DoubleDealSecurity/Differential.lean`, for `(a, x) ≠ (0, 0)` and without the
  finite-check hypotheses, obtained by plugging in the kernel-checked GridCycle checks
  `check3_KC` / `check3_KS` (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`). No new
  `decide!` here.
  Same model and caveats as `DoubleDealSecurity/Differential.lean`. These cover ONLY
  paths whose difference stays inside `v10Sym` after every round; they are NOT a bound
  on the full differential, and no numeric bound on the full differential is proved
  anywhere. The real-schedule statement is the first mix round's bound (round 0, key `K_0`).
  No final no-mix round;
  `rounds` not linked to `encryptN` (both in `FullCipher`, M7). Not a bit-security claim.
-/
import DoubleDealSecurity.Differential
import DoubleDealSecurityHeavy.GridCycleSurvival

namespace DoubleDeal.Security.Differential

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key)
open DoubleDeal.Security.RealSchedule (roundKeys)

open Classical in
/-- (PROVED) Nontrivial `v10Sym a x` (`(a, x) ≠ (0, 0)`), independent uniform round keys, every deck
    `y`: at most `(52!)^R / 4420^R` key tuples keep the difference inside `v10Sym` for `R` rounds.
    Only paths inside `v10Sym`; NOT a bound on the differential. -/
theorem staysInV10_card_le_4420 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 ^ R * (univ.filter fun K : Fin R → Key => StaysInV10 R (v10Sym a x) y K).card ≤
      Nat.factorial 52 ^ R :=
  staysInV10_card_le_4420_of_check GridCycleSurvival.check3_KC GridCycleSurvival.check3_KS
    a x hne R hy

open Classical in
/-- (PROVED) Real PassKey schedule, uniform master key, `v10Sym a x` with `(a, x) ≠ (0, 0)`, every
    `R ≥ 1`, every deck `y`: at most `52!/4420` master keys keep the difference inside `v10Sym` for
    `R` rounds. The first mix round's bound (not `(1/4420)^R`); only paths inside `v10Sym`. -/
theorem realStaysInV10_card_le_4420 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (R : ℕ) (hR : 0 < R) {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 * (univ.filter fun π : Equiv.Perm (Fin 52) =>
      StaysInV10 R (v10Sym a x) y (roundKeys R π)).card ≤ Nat.factorial 52 :=
  realStaysInV10_card_le_4420_of_check GridCycleSurvival.check3_KC
    GridCycleSurvival.check3_KS a x hne R hR hy

end DoubleDeal.Security.Differential
