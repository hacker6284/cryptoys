/-
  LINK 2. One E_m round: `Generated.f3_step` refines `Em.f3Step` and
  `Generated.g2_step` refines `Em.g2Step`, each under the `RecipeOk`
  side condition of the final `recipe_a` call (the corner lookup and the
  re-orientation both succeed).

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifachV1.Link2.EmSpin
import MegaDreifachV1.Link2.FaceTurn

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

private theorem sEq_ofNat4 (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

theorem noon_phys_refines' (phys : Fin 12) (o : Grip) :
    Megadreifach.noon_phys (Int.ofNat phys.val) (embedGrip o) =
      .ok (Int.ofNat (noonPhys phys o).val) := noon_phys_refines phys o

theorem atL_grip1 (o : Grip) :
    SudoRt.atL (embedGrip o) (Int.ofNat 1) = .ok (Int.ofNat (o 1).val) :=
  atL_grip o 1 (by decide)

/-! ## F3 -/

/-- `Generated.f3_step` refines `Em.f3Step` when the closing `recipe_a` succeeds. -/
theorem f3_step_refines (g : Position) (o : Grip)
    (h : RecipeOk (faceTurn g (o 0) 1) (o 0) o) :
    Megadreifach.f3_step (embedPos g) (embedGrip o) =
      .ok (embedPos (f3Step (g, o)).1, embedGrip (f3Step (g, o)).2) := by
  unfold Megadreifach.f3_step
  rw [show Megadreifach.held_up = Int.ofNat 0 from rfl, atL_grip0, ok_bind,
    show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
  try dsimp only
  rw [ok_bind, recipe_a_refines _ _ _ h, ok_bind]
  rfl

/-! ## G2 -/

/-- The part of `g2Step` before the closing `recipeA`: `(g3, oW, held)`. -/
def g2Mid (st : Position × Grip) (card : Nat) : Position × Grip × Fin 12 :=
  let g := st.1
  let o := st.2
  let rank := card / 4
  let amt := card % 4 + 1
  let (g1, oW, held) :=
    if h : rank < 12 then (faceTurn g (o ⟨rank, h⟩) amt, o, (⟨rank, h⟩ : Fin 12))
    else (faceTurn g (o 0) ((5 - amt) % 5), spinAboutUp o amt, (0 : Fin 12))
  let noon := noonPhys (oW held) oW
  let g2 := if noon ≠ oW held then faceTurn g1 noon 1 else g1
  let g3 := faceTurn g2 (oW 1) 1
  (g3, oW, held)

theorem g2Step_eq (st : Position × Grip) (card : Nat) :
    g2Step st card =
      ((g2Mid st card).1,
        recipeA (g2Mid st card).1 ((g2Mid st card).2.1 (g2Mid st card).2.2)
          (g2Mid st card).2.1) := by
  unfold g2Step g2Mid
  by_cases h : card / 4 < 12
  · simp only [dif_pos h]
  · simp only [dif_neg h]

/-- Side condition for `g2_step`: the closing `recipe_a` succeeds. -/
def G2Ok (st : Position × Grip) (card : Nat) : Prop :=
  RecipeOk (g2Mid st card).1 ((g2Mid st card).2.1 (g2Mid st card).2.2) (g2Mid st card).2.1

private theorem fits8 (k : Nat) (hk : k ≤ 8) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 8) hk

/-- `Generated.g2_step` refines `Em.g2Step` for every card value, under `G2Ok`. -/
theorem g2_step_refines (g : Position) (o : Grip) (card : Nat) (hok : G2Ok (g, o) card) :
    Megadreifach.g2_step (embedPos g) (embedGrip o) (Int.ofNat card) =
      .ok (embedPos (g2Step (g, o) card).1, embedGrip (g2Step (g, o) card).2) := by
  rw [g2Step_eq]
  unfold G2Ok at hok
  generalize hm : g2Mid (g, o) card = m at hok ⊢
  obtain ⟨g3, oW, held⟩ := m
  dsimp only at hok ⊢
  have hamt4 : card % 4 + 1 ≤ 4 := by have := Nat.mod_lt card (by decide : 4 > 0); omega
  unfold Megadreifach.g2_step
  rw [show (4 : Int) = Int.ofNat 4 from rfl, divI_ofNat _ (by decide : (4 : Nat) ≠ 0), ok_bind,
    modI_ofNat _ (by decide : (4 : Nat) ≠ 0), ok_bind]
  try dsimp only
  rw [addI_ofNat_one _ (fits8 _ (by omega)), ok_bind]
  unfold g2Mid at hm
  by_cases hr : card / 4 < 12
  · have hdec : decide (Int.ofNat (card / 4) < (12 : Int)) = true := by
      simp only [decide_eq_true_eq]; exact Int.ofNat_lt.mpr hr
    rw [hdec, if_pos rfl]
    simp only [dif_pos hr] at hm
    rw [atL_grip o _ hr, ok_bind, face_turn_refines, ok_bind]
    try dsimp only
    rw [ok_bind, noon_phys_refines', ok_bind, ok_bind, sEq_ofNat4]
    by_cases hn : noonPhys (o ⟨card / 4, hr⟩) o = o ⟨card / 4, hr⟩
    · have hd : decide ((noonPhys (o ⟨card / 4, hr⟩) o).val = (o ⟨card / 4, hr⟩).val) = true := by
        simp [hn]
      rw [hd]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      simp only [hn, ne_eq, not_true_eq_false, ite_false] at hm
      rw [show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
        show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
      try dsimp only
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      rw [ok_bind, recipe_a_refines _ _ _ hok, ok_bind]
      rfl
    · have hd : decide ((noonPhys (o ⟨card / 4, hr⟩) o).val = (o ⟨card / 4, hr⟩).val) = false := by
        simp [Fin.val_inj, hn]
      rw [hd]
      simp only [Bool.not_false, ite_true]
      simp only [hn, ne_eq, not_false_eq_true, ite_true] at hm
      rw [show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
      try dsimp only
      rw [show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
        face_turn_refines, ok_bind]
      try dsimp only
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      rw [ok_bind, recipe_a_refines _ _ _ hok, ok_bind]
      rfl
  · have hdec : decide (Int.ofNat (card / 4) < (12 : Int)) = false := by
      simp only [decide_eq_false_iff_not]; intro hc; exact hr (Int.ofNat_lt.mp hc)
    rw [hdec]
    simp only [Bool.false_eq_true, ite_false]
    simp only [dif_neg hr] at hm
    rw [show Megadreifach.held_up = Int.ofNat 0 from rfl, atL_grip0, ok_bind,
      show (5 : Int) = Int.ofNat 5 from rfl,
      subI_ofNat 5 (card % 4 + 1) (fits8 5 (by decide)) (by omega), ok_bind,
      modI_ofNat _ (by decide : (5 : Nat) ≠ 0), ok_bind, face_turn_refines, ok_bind]
    try dsimp only
    rw [spin_about_up_refines, ok_bind]
    try dsimp only
    generalize hO : spinAboutUp o (card % 4 + 1) = O at hm ⊢
    rw [atL_grip0, ok_bind, noon_phys_refines', ok_bind, ok_bind, sEq_ofNat4]
    by_cases hn : noonPhys (O 0) O = O 0
    · have hd : decide ((noonPhys (O 0) O).val = (O 0).val) = true := by simp [hn]
      rw [hd]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      simp only [hn, ne_eq, not_true_eq_false, ite_false] at hm
      rw [show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
        show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
      try dsimp only
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      rw [ok_bind, recipe_a_refines _ _ _ hok, ok_bind]
      rfl
    · have hd : decide ((noonPhys (O 0) O).val = (O 0).val) = false := by
        simp [Fin.val_inj, hn]
      rw [hd]
      simp only [Bool.not_false, ite_true]
      simp only [hn, ne_eq, not_false_eq_true, ite_true] at hm
      rw [show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
      try dsimp only
      rw [show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
        face_turn_refines, ok_bind]
      try dsimp only
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      rw [ok_bind, recipe_a_refines _ _ _ hok, ok_bind]
      rfl

end MegaDreifachV1.Link2
