/-
  LINK 2 side conditions. Every `recipe_a` call inside `em_block` succeeds.

  `GripOk o` (the grip's Front is a neighbour of its Up) is enough for
  `RecipeOk g phys o` at every position `g` and physical face `phys`, and
  `GripOk` holds for the identity grip, is kept by `spin_about_up`, and holds
  for every grip `recipeA` returns. The finite facts are checked by kernel
  `decide!` over small tables (no `native_decide`).
-/
import MegaDreifachV1.Link2.EmStep

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

/-- The grip's Front face is a neighbour of its Up face. -/
def GripOk (o : Grip) : Prop := o 1 ∈ nbrs (o 0)

theorem gripOk_id : GripOk gripId := by
  unfold GripOk gripId; decide

/-! ## Finite tables -/

theorem noonCore_mem_table :
    allFin12 (fun p => allFin12 (fun u => allFin12 (fun f =>
      !decide (f ∈ nbrs u) || decide (noonCore p u f ∈ nbrs p)))) = true := by
  decide!

theorem noonPhys_mem (p : Fin 12) (o : Grip) (h : GripOk o) : noonPhys p o ∈ nbrs p := by
  have := allFin12_spec (allFin12_spec (allFin12_spec noonCore_mem_table p) (o 0)) (o 1)
  unfold GripOk at h
  simpa [h] using this

theorem slot_table :
    allFin12 (fun p => allFin12 (fun x =>
      !decide (x ∈ nbrs p) ||
        (cornerSlot? p x (nbr p ((niPre p x 5 + 1) % 5))).isSome)) = true := by
  decide!

/-- Position of `face` among the corner faces `(f0, f1, f2)` (as in `colourOn`). -/
def locOf (face f1 f2 : Fin 12) : Nat := if face = f2 then 2 else if face = f1 then 1 else 0

theorem loc_table :
    allFin12 (fun p => allFin12 (fun x =>
      !decide (x ∈ nbrs p) ||
        (let s := cornerSlot p x (nbr p ((niPre p x 5 + 1) % 5))
         decide (locOf p (cornerFace s.val 1) (cornerFace s.val 2) ≠
           locOf x (cornerFace s.val 1) (cornerFace s.val 2))))) = true := by
  decide!

/-- Two different faces of one corner cubie are adjacent. -/
theorem corner_adj_table :
    (List.range 20).all (fun c => (List.range 3).all (fun j => (List.range 3).all (fun k =>
      decide (j = k) || decide (cornerFace c k ∈ nbrs (cornerFace c j))))) = true := by
  decide!

theorem corner_adj (c j k : Nat) (hc : c < 20) (hj : j < 3) (hk : k < 3) (hjk : j ≠ k) :
    cornerFace c k ∈ nbrs (cornerFace c j) := by
  have h := corner_adj_table
  simp only [List.all_eq_true, List.mem_range] at h
  have := h c hc j hj k hk
  simpa [hjk] using this

theorem colourOn_eq (face f1 f2 : Fin 12) (c : Nat) (ori : Fin 3) :
    colourOn face f1 f2 (cornerFace c 0) (cornerFace c 1) (cornerFace c 2) ori =
      cornerFace c ((locOf face f1 f2 + 3 - ori.val) % 3) := by
  unfold colourOn
  show (let k := (locOf face f1 f2 + 3 - ori.val) % 3
      if k = 0 then cornerFace c 0 else if k = 1 then cornerFace c 1 else cornerFace c 2) = _
  have hk : (locOf face f1 f2 + 3 - ori.val) % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize (locOf face f1 f2 + 3 - ori.val) % 3 = k at hk ⊢
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals rfl

theorem locOf_le (face f1 f2 : Fin 12) : locOf face f1 f2 ≤ 2 := by
  unfold locOf; split
  · omega
  · split <;> omega

/-- The two colours read by `recipeA` are adjacent faces. -/
theorem colours_adj (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p) :
    (coloursAt g p x (nbr p ((niPre p x 5 + 1) % 5))).2 ∈
      nbrs (coloursAt g p x (nbr p ((niPre p x 5 + 1) % 5))).1 := by
  have hloc := allFin12_spec (allFin12_spec loc_table p) x
  simp only [hx, decide_True, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hloc
  unfold coloursAt
  generalize cornerSlot p x (nbr p ((niPre p x 5 + 1) % 5)) = s at hloc ⊢
  dsimp only
  rw [colourOn_eq, colourOn_eq]
  have h1 := locOf_le p (cornerFace s.val 1) (cornerFace s.val 2)
  have h2 := locOf_le x (cornerFace s.val 1) (cornerFace s.val 2)
  have hr := (g.co s).isLt
  apply corner_adj _ _ _ (g.cp s).isLt (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  omega

/-! ## `RecipeOk` from `GripOk` -/

theorem absReorient?_some_iff (c1 c2 : Fin 12) :
    (absReorient? c1 c2).isSome = decide (c2 ∈ nbrs c1) := by
  have := allFin12_spec (allFin12_spec absReorient?_isSome_iff c1) c2
  simpa using this

theorem recipeOk_of_gripOk (g : Position) (phys : Fin 12) (o : Grip) (h : GripOk o) :
    RecipeOk g phys o := by
  have hn := noonPhys_mem phys o h
  constructor
  · have := allFin12_spec (allFin12_spec slot_table phys) (noonPhys phys o)
    simpa [hn] using this
  · rw [absReorient?_some_iff]
    exact decide_eq_true (colours_adj g phys _ hn)

/-! ## `GripOk` is preserved -/

theorem absReorient?_spec (c1 c2 : Fin 12) (r : Grip) (h : absReorient? c1 c2 = some r) :
    r 0 = c1 ∧ r 1 = c2 := by
  unfold absReorient? at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some'.mp h
  have := List.find?_some hs
  simpa using this

theorem gripOk_recipeA (g : Position) (phys : Fin 12) (o : Grip) (h : GripOk o) :
    GripOk (recipeA g phys o) := by
  have hr := (recipeOk_of_gripOk g phys o h).rot
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hr
  have hsp := absReorient?_spec _ _ r hr'
  have hA : recipeA g phys o = r := by rw [recipeA_eq, absReorient, hr']; rfl
  have hadj := colours_adj g phys (noonPhys phys o) (noonPhys_mem phys o h)
  rw [hA]
  unfold GripOk
  rw [hsp.1, hsp.2]
  exact hadj

theorem spin_table :
    allFin12 (fun u => allFin12 (fun x => (List.range 5).all (fun k =>
      !decide (x ∈ nbrs u) || decide (spinPhys u k x ∈ nbrs u)))) = true := by
  decide!

theorem gripOk_spin (o : Grip) (k : Nat) (h : GripOk o) : GripOk (spinAboutUp o k) := by
  unfold spinAboutUp
  split
  · exact h
  · unfold GripOk at h ⊢
    have hup : spinPhys (o 0) (k % 5) (o 0) = o 0 := by unfold spinPhys; simp
    show spinPhys (o 0) (k % 5) (o 1) ∈ nbrs (spinPhys (o 0) (k % 5) (o 0))
    rw [hup]
    have := allFin12_spec (allFin12_spec spin_table (o 0)) (o 1)
    simp only [List.all_eq_true, List.mem_range] at this
    simpa [h] using this (k % 5) (Nat.mod_lt _ (by decide))

theorem g2Ok_of_gripOk (g : Position) (o : Grip) (card : Nat) (h : GripOk o) :
    G2Ok (g, o) card := by
  unfold G2Ok
  apply recipeOk_of_gripOk
  unfold g2Mid
  by_cases hr : card / 4 < 12
  · simp only [dif_pos hr]; exact h
  · simp only [dif_neg hr]; exact gripOk_spin o _ h

theorem gripOk_g2Step (st : Position × Grip) (card : Nat) (h : GripOk st.2) :
    GripOk (g2Step st card).2 := by
  rw [g2Step_eq]
  apply gripOk_recipeA
  unfold g2Mid
  by_cases hr : card / 4 < 12
  · simp only [dif_pos hr]; exact h
  · simp only [dif_neg hr]; exact gripOk_spin _ _ h

theorem gripOk_f3Step (st : Position × Grip) (h : GripOk st.2) : GripOk (f3Step st).2 :=
  gripOk_recipeA _ _ _ h

/-- Unconditional forms of the step refinements on well-formed grips. -/
theorem f3_step_refines' (g : Position) (o : Grip) (h : GripOk o) :
    Megadreifach.f3_step (embedPos g) (embedGrip o) =
      .ok (embedPos (f3Step (g, o)).1, embedGrip (f3Step (g, o)).2) :=
  f3_step_refines g o (recipeOk_of_gripOk _ _ _ h)

theorem g2_step_refines' (g : Position) (o : Grip) (card : Nat) (h : GripOk o) :
    Megadreifach.g2_step (embedPos g) (embedGrip o) (Int.ofNat card) =
      .ok (embedPos (g2Step (g, o) card).1, embedGrip (g2Step (g, o) card).2) :=
  g2_step_refines g o card (g2Ok_of_gripOk g o card h)

end MegaDreifachV1.Link2
