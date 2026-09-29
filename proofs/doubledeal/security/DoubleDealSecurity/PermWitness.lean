/-
  A permutation with prescribed images of two / three distinct points, for every type
  with decidable equality (no cipher content): `exists_perm_two`, `exists_perm_three`.

  Split out of `PermCount.lean` so that the pair-swap witness decks of `SumRanks.lean`,
  `SumRanksV10Iff.lean` and `SumRanksDP/Main.lean` add only this module to the import
  closure of `SumRanks.lean`: it imports only `Mathlib.GroupTheory.Perm.Basic`, which
  `Relabel.lean` already imports. `checks/scan_sorry.py` pins the exact import sets of this
  file, `SumRanks.lean`, `Relabel.lean` and `Decks.lean` (`PINNED_IMPORTS`).
  The `PermCount` namespace is deliberate: a companion file split out for import size keeps
  the family namespace (the same pattern as `GridCycleSurvivalLists` in `GridCycleSurvival`).
-/
import Mathlib.GroupTheory.Perm.Basic

namespace DoubleDeal.Security.PermCount

theorem exists_perm_two {α : Type*} [DecidableEq α] (i j a b : α) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ π : Equiv.Perm α, π i = a ∧ π j = b := by
  let π1 : Equiv.Perm α := Equiv.swap i a
  let b1 := π1.symm b
  have hπ1 : π1 i = a := Equiv.swap_apply_left i a
  have hib1 : i ≠ b1 := by
    intro e
    have : π1 b1 = b := Equiv.apply_symm_apply π1 b
    rw [← e, hπ1] at this
    exact hab this
  refine ⟨π1 * Equiv.swap j b1, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hib1, hπ1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.apply_symm_apply π1 b

theorem exists_perm_three {α : Type*} [DecidableEq α] (i j k a b c : α) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ π : Equiv.Perm α, π i = a ∧ π j = b ∧ π k = c := by
  obtain ⟨π2, h1, h2⟩ := exists_perm_two i j a b hij hab
  let c1 := π2.symm c
  have hc1 : π2 c1 = c := π2.apply_symm_apply c
  have hic : i ≠ c1 := fun e => hac (by rw [← h1, e, hc1])
  have hjc : j ≠ c1 := fun e => hbc (by rw [← h2, e, hc1])
  refine ⟨π2 * Equiv.swap k c1, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hik hic, h1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hjk hjc, h2]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hc1]

end DoubleDeal.Security.PermCount
