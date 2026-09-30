/-
  HEAVY (not in the default build target): the forms of `DoubleDealSecurity/FullCipher.lean`
  (roadmap milestone M7) without the finite-check hypotheses, obtained by plugging in the
  kernel-checked GridCycle checks `check3_KC` / `check3_KS`
  (`DoubleDealSecurityHeavy/GridCycleSurvival.lean`). Instances only; no new `decide!`.
  Same model and caveats as `DoubleDealSecurity/FullCipher.lean`: the characteristic and the
  `v10Sym` cluster only (every `v10Sym` bound for `(a, x) ≠ (0, 0)`), NOT the full-cipher
  differential, for which no numeric bound is proved anywhere. The real-schedule statements
  are the bound of the first mix round (round 0, key `K_0`) alone; mix rounds 1–4 and the
  final round add no factor (a limit of the proof, not a measured weakness). Not a
  bit-security claim.
-/
import DoubleDealSecurity.FullCipher
import DoubleDealSecurityHeavy.GridCycleSurvival

namespace DoubleDeal.Security.FullCipher

open DoubleDeal Relabel Finset
open DoubleDeal.Security (Key)
open DoubleDeal.Security.GridCycleSurvival (check3_KC check3_KS)

/-- (PROVED) Whole cipher, independent uniform keys, nontrivial `v10Sym a x`
    (`(a, x) ≠ (0, 0)`): `4420^n · # ≤ (52!)^(n+2)`; the final round adds no factor. -/
theorem fullTrail_card_le_4420_v10Sym (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    (n : ℕ) {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullTrail (v10Sym a x) n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  fullTrail_card_le_4420_v10Sym_of_check check3_KC check3_KS a x hne n hy

/-- (PROVED) Whole cipher, independent uniform keys, at least one mix round, every `σ ≠ 1`:
    `64^(n+1) · # ≤ (52!)^(n+2)`. The characteristic only. `n ≥ 1` is needed: see
    `fullTrail_card_le_64_of_check`. -/
theorem fullTrail_card_le_64 (σ : Relabel) (h1 : σ ≠ 1) (n : ℕ) (hn : 0 < n)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 ^ (n + 1) * (univ.filter fun L : Fin (n + 2) → Key => FullTrail σ n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  fullTrail_card_le_64_of_check check3_KC check3_KS σ h1 n hn hy

open Classical in
/-- (PROVED) Whole cipher, independent uniform keys, `v10Sym` cluster, `(a, x) ≠ (0, 0)`:
    `4420^n · # ≤ (52!)^(n+2)`. Only paths inside `v10Sym`; not the differential. -/
theorem fullStaysInV10_card_le_4420 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) (n : ℕ)
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 ^ n * (univ.filter fun L : Fin (n + 2) → Key => FullStaysInV10 a x n y L).card ≤
      Nat.factorial 52 ^ (n + 2) :=
  fullStaysInV10_card_le_4420_of_check check3_KC check3_KS a x hne n hy

/-- (PROVED) Real schedule, whole cipher, every `σ ≠ 1`: at most `52!/64` master keys follow the
    characteristic. The first mix round's bound (round 0, key `K_0`). -/
theorem realFullTrail_card_le_64 (σ : Relabel) (h1 : σ ≠ 1) {y : Fin 52 → Nat} (hy : IsDeck y) :
    64 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullTrail σ 5 y (realKeys π)).card ≤
      Nat.factorial 52 :=
  realFullTrail_card_le_64_of_check check3_KC check3_KS σ h1 hy

open Classical in
/-- (PROVED) Real schedule, whole cipher, `v10Sym` cluster, `(a, x) ≠ (0, 0)`: at most
    `52!/4420` master keys. The first mix round's bound (round 0, key `K_0`). -/
theorem realFullStaysInV10_card_le_4420 (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0))
    {y : Fin 52 → Nat} (hy : IsDeck y) :
    4420 * (univ.filter fun π : Equiv.Perm (Fin 52) => FullStaysInV10 a x 5 y (realKeys π)).card ≤
      Nat.factorial 52 :=
  realFullStaysInV10_card_le_4420_of_check check3_KC check3_KS a x hne hy

end DoubleDeal.Security.FullCipher
