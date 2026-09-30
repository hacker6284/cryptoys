/-
  LINK 2. One E_m round (v2): `Generated.f3_step` refines `Em.f3Step` and
  `Generated.g2_step` refines `Em.g2Step`, for every round / deal position
  number, each under the `ReadOk` side condition of its `read_grip` call (the
  noon is a neighbour, the corner / edge lookups succeed, and the read colours
  admit a re-orientation).

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.EmSpin
import MegaDreifach.Link2.FaceTurn

namespace MegaDreifach.Link2

open MegaDreifach.Em

theorem visual_noon_refines' (p : Fin 12) (o : Grip) :
    Megadreifach.visual_noon (Int.ofNat p.val) (embedGrip o) =
      .ok (Int.ofNat (visualNoon p o).val) := visual_noon_refines p o

theorem visual_noon_refines_nat (p : Nat) (hp : p < 12) (o : Grip) :
    Megadreifach.visual_noon (Int.ofNat p) (embedGrip o) =
      .ok (Int.ofNat (visualNoon ⟨p, hp⟩ o).val) := visual_noon_refines ⟨p, hp⟩ o

theorem atL_grip1 (o : Grip) :
    SudoRt.atL (embedGrip o) (Int.ofNat 1) = .ok (Int.ofNat (o 1).val) :=
  atL_grip o 1 (by decide)

/-! ## F3 -/

/-- Side condition for `f3_step`: its `read_grip` succeeds. -/
def F3Ok (st : Position × Grip) (rnd : Nat) : Prop :=
  ReadOk (faceTurn st.1 (st.2 0) 1) (st.2 0) (visualNoon 0 st.2) rnd

/-- `Generated.f3_step` refines `Em.f3Step` (round `rnd`) when its read succeeds. -/
theorem f3_step_refines (g : Position) (o : Grip) (rnd : Nat) (h : F3Ok (g, o) rnd) :
    Megadreifach.f3_step (embedPos g) (embedGrip o) (Int.ofNat rnd) =
      .ok (embedPos (f3Step (g, o) rnd).1, embedGrip (f3Step (g, o) rnd).2) := by
  unfold Megadreifach.f3_step
  rw [show Megadreifach.held_up = Int.ofNat 0 from rfl, atL_grip0, ok_bind]
  try dsimp only
  rw [show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind]
  try dsimp only
  rw [visual_noon_refines_nat 0 (by decide) o, ok_bind,
    read_grip_refines _ _ (visualNoon ⟨0, by decide⟩ o) _ h, ok_bind]
  rfl

/-! ## G2 -/

/-- The part of `g2Step` before the read: `(g1, oW, held)` after the held-face
    turn (King: after the Up counter-turn and the grip spin). -/
def g2Mid (st : Position × Grip) (card : Nat) : Position × Grip × Fin 12 :=
  let g := st.1
  let o := st.2
  let rank := card / 4
  let amt := card % 4 + 1
  if h : rank < 12 then (faceTurn g (o ⟨rank, h⟩) amt, o, (⟨rank, h⟩ : Fin 12))
  else (faceTurn g (o 0) ((5 - amt) % 5), spinAboutUp o amt, (0 : Fin 12))

theorem g2Step_eq (st : Position × Grip) (card pos : Nat) :
    g2Step st card pos =
      (faceTurn (faceTurn (g2Mid st card).1 (visualNoon (g2Mid st card).2.2 (g2Mid st card).2.1) 1)
          ((g2Mid st card).2.1 1) 1,
        readGrip (g2Mid st card).1 ((g2Mid st card).2.1 (g2Mid st card).2.2)
          (visualNoon (g2Mid st card).2.2 (g2Mid st card).2.1) pos) := by
  unfold g2Step g2Mid
  by_cases h : card / 4 < 12
  · simp only [dif_pos h]
  · simp only [dif_neg h]

/-- Side condition for `g2_step`: its `read_grip` succeeds. -/
def G2Ok (st : Position × Grip) (card pos : Nat) : Prop :=
  ReadOk (g2Mid st card).1 ((g2Mid st card).2.1 (g2Mid st card).2.2)
    (visualNoon (g2Mid st card).2.2 (g2Mid st card).2.1) pos

private theorem fits8 (k : Nat) (hk : k ≤ 8) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 8) hk

/-- `Generated.g2_step` refines `Em.g2Step` for every card value and deal position,
    under `G2Ok`. -/
theorem g2_step_refines (g : Position) (o : Grip) (card pos : Nat) (hok : G2Ok (g, o) card pos) :
    Megadreifach.g2_step (embedPos g) (embedGrip o) (Int.ofNat card) (Int.ofNat pos) =
      .ok (embedPos (g2Step (g, o) card pos).1, embedGrip (g2Step (g, o) card pos).2) := by
  rw [g2Step_eq]
  unfold G2Ok at hok
  generalize hm : g2Mid (g, o) card = m at hok ⊢
  obtain ⟨g1, oW, held⟩ := m
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
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    rw [atL_grip o _ hr, ok_bind, face_turn_refines, ok_bind]
    try dsimp only
    rw [visual_noon_refines_nat (card / 4) hr o]
    simp only [ok_bind]
    rw [read_grip_refines _ _ _ _ hok]
    simp only [ok_bind]
    try dsimp only
    rw [show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind,
      show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
      face_turn_refines, ok_bind]
    rfl
  · have hdec : decide (Int.ofNat (card / 4) < (12 : Int)) = false := by
      simp only [decide_eq_false_iff_not]; intro hc; exact hr (Int.ofNat_lt.mp hc)
    rw [hdec]
    simp only [Bool.false_eq_true, ite_false]
    simp only [dif_neg hr] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    rw [show Megadreifach.held_up = Int.ofNat 0 from rfl, atL_grip0, ok_bind,
      show (5 : Int) = Int.ofNat 5 from rfl,
      subI_ofNat 5 (card % 4 + 1) (fits8 5 (by decide)) (by omega), ok_bind,
      modI_ofNat _ (by decide : (5 : Nat) ≠ 0), ok_bind, face_turn_refines, ok_bind]
    try dsimp only
    rw [spin_about_up_refines, ok_bind]
    try dsimp only
    rw [atL_grip0, visual_noon_refines_nat 0 (by decide) _]
    simp only [ok_bind]
    rw [read_grip_refines _ _ (visualNoon ⟨0, by decide⟩ _) _ hok]
    simp only [ok_bind]
    try dsimp only
    rw [show (1 : Int) = Int.ofNat 1 from rfl, face_turn_refines, ok_bind,
      show Megadreifach.held_front = Int.ofNat 1 from rfl, atL_grip1, ok_bind,
      face_turn_refines, ok_bind]
    rfl

end MegaDreifach.Link2
