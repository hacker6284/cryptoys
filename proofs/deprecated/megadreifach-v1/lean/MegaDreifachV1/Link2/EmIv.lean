/-
  LINK 2. `Generated.iv_cook12` refines `Em.ivCook12`, which equals the
  M11 lists `ivCook12Cp/Co/Ep/Eo` (IV.lean).
-/
import MegaDreifachV1.Link2.EmBlock
import MegaDreifachV1.IV

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

theorem identity_refines : Megadreifach.identity = .ok (embedPos MegaDreifachV1.identity) := by
  rfl

/-- Identity cooked by the first `i` unit face turns. -/
def ivPre (i : Nat) : Position :=
  (List.range i).foldl (fun g f => if hf : f < 12 then faceTurn g ⟨f, hf⟩ 1 else g)
    MegaDreifachV1.identity

theorem ivPre_succ (i : Nat) (hi : i < 12) : ivPre (i + 1) = faceTurn (ivPre i) ⟨i, hi⟩ 1 := by
  unfold ivPre
  rw [List.range_succ, List.foldl_append]
  simp [hi]

theorem iv_cook12_refines : Megadreifach.iv_cook12 = .ok (embedPos ivCook12) := by
  unfold Megadreifach.iv_cook12
  rw [identity_refines, ok_bind]
  dsimp only
  rw [except_bind_pure]
  apply chain_loop (f := fun i => embedPos (ivPre i)) (fromN := 0) (toN := 11) (hle := by decide)
  · intro i _ hi
    dsimp only
    rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hi),
      show (1 : Int) = Int.ofNat 1 from rfl,
      show Int.ofNat i = Int.ofNat (⟨i, by omega⟩ : Fin 12).val from rfl,
      face_turn_refines, ok_bind]
    dsimp only
    rw [pure_bind, ← ivPre_succ i (by omega)]
    exact loopTailR i 11 hi (by decide) _
  · rfl

/-- The concrete IV is the M11 `ivCook12Of` instance at the algebraic unit face turn. -/
theorem ivCook12_eq_of :
    ivCook12 = ivCook12Of (fun f g => if hf : f < 12 then faceTurn g ⟨f, hf⟩ 1 else g) := rfl

/-- The concrete IV has exactly the M11 reference arrays. -/
theorem ivCook12_lists :
    listOf ivCook12.cp = ivCook12Cp ∧ listOfOri ivCook12.co = ivCook12Co ∧
      listOf ivCook12.ep = ivCook12Ep ∧ listOfOri ivCook12.eo = ivCook12Eo := by
  decide!

/-- M11 without the `hpres` hypothesis: the concrete IV is legal (kernel `decide!`). -/
theorem ivCook12_isLegal : isLegal Em.ivCook12 := by
  unfold isLegal
  rw [(ivCook12_lists).1, (ivCook12_lists).2.1, (ivCook12_lists).2.2.1, (ivCook12_lists).2.2.2]
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide⟩
  · unfold Injective; decide!
  · unfold Injective; decide!

/-- The concrete IV as `posOfLists` of the M11 reference arrays. -/
theorem ivCook12_eq_lists :
    Em.ivCook12 = Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo := by
  have h := posOfLists_listOf Em.ivCook12
  rw [ivCook12_lists.1, ivCook12_lists.2.1, ivCook12_lists.2.2.1, ivCook12_lists.2.2.2] at h
  exact h.symm

end MegaDreifachV1.Link2
