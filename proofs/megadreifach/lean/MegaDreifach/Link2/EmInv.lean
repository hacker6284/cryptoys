/-
  LINK 2 side conditions. Every `read_grip` call inside `em_block` succeeds (v2).

  `GripOk o` (the grip is one of the 60 rotations `rotAt s`) gives, for every
  hold position `h`, that the visual noon `visualNoon h o` is a neighbour of the
  held face `o h`; and a neighbour pair is enough for `ReadOk g phys noon pos` at
  every position `g` and read position `pos` (both the corner read and the edge
  read show two adjacent colours, so `abs_reorient` finds a rotation). `GripOk`
  holds for the identity grip, is kept by `spin_about_up`, and holds for every
  grip `readGrip` returns on a neighbour pair. The finite facts are checked by
  kernel `decide!` over small tables (no `native_decide`).
-/
import MegaDreifach.Link2.EmStep

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- The grip is one of the 60 rotations of `rots_flat`. -/
def GripOk (o : Grip) : Prop := ∃ s, s < 60 ∧ o = rotAt s

theorem gripId_eq_rotAt0 : ∀ h : Fin 12, gripId h = rotAt 0 h := by decide

theorem gripOk_id : GripOk gripId := ⟨0, by decide, funext gripId_eq_rotAt0⟩

/-! ## Finite tables -/

/-- In each of the 60 rotations, every hold position's visual noon is a neighbour
    of the face held there. -/
theorem visualNoon_table :
    (List.range 60).all (fun s => allFin12 (fun h =>
      decide (visualNoon h (rotAt s) ∈ nbrs (rotAt s h)))) = true := by
  decide!

theorem visualNoon_mem (o : Grip) (hg : GripOk o) (h : Fin 12) : visualNoon h o ∈ nbrs (o h) := by
  obtain ⟨s, hs, rfl⟩ := hg
  have ht := visualNoon_table
  rw [List.all_eq_true] at ht
  have := allFin12_spec (ht s (List.mem_range.mpr hs)) h
  simpa using this

theorem cslot_table :
    allFin12 (fun p => allFin12 (fun x =>
      !decide (x ∈ nbrs p) || (cornerSlot? p x (cornerAfterNoon p x)).isSome)) = true := by
  decide!

theorem eslot_table :
    allFin12 (fun p => allFin12 (fun x =>
      !decide (x ∈ nbrs p) || (edgeSlot? p x).isSome)) = true := by
  decide!

/-- Position of `face` among the corner faces `(f0, f1, f2)` (as in `colourOn`). -/
def locOf (face f1 f2 : Fin 12) : Nat := if face = f2 then 2 else if face = f1 then 1 else 0

theorem loc_table :
    allFin12 (fun p => allFin12 (fun x =>
      !decide (x ∈ nbrs p) ||
        (let s := cornerSlot p x (cornerAfterNoon p x)
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

/-- The two faces of one edge piece are adjacent (both ways). -/
theorem edge_adj_table :
    (List.range 30).all (fun e =>
      decide (edgeFace e 1 ∈ nbrs (edgeFace e 0)) && decide (edgeFace e 0 ∈ nbrs (edgeFace e 1))) =
      true := by
  decide!

theorem edge_adj (e : Nat) (he : e < 30) :
    edgeFace e 1 ∈ nbrs (edgeFace e 0) ∧ edgeFace e 0 ∈ nbrs (edgeFace e 1) := by
  have h := edge_adj_table
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h e he

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

/-- The two colours of the corner read are adjacent faces. -/
theorem colours_adj (g : Position) (p x : Fin 12) (hx : x ∈ nbrs p) :
    (coloursAt g p x (cornerAfterNoon p x)).2 ∈ nbrs (coloursAt g p x (cornerAfterNoon p x)).1 := by
  have hloc := allFin12_spec (allFin12_spec loc_table p) x
  simp only [hx, decide_True, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hloc
  unfold coloursAt
  generalize cornerSlot p x (cornerAfterNoon p x) = s at hloc ⊢
  dsimp only
  rw [colourOn_eq, colourOn_eq]
  have h1 := locOf_le p (cornerFace s.val 1) (cornerFace s.val 2)
  have h2 := locOf_le x (cornerFace s.val 1) (cornerFace s.val 2)
  have hr := (g.co s).isLt
  apply corner_adj _ _ _ (g.cp s).isLt (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  omega

/-- The two colours of the edge read are adjacent faces (any position, any faces). -/
theorem edge_colours_adj (g : Position) (a b : Fin 12) :
    (edgeColoursAt g a b).2 ∈ nbrs (edgeColoursAt g a b).1 := by
  unfold edgeColoursAt
  have he := edge_adj _ (g.ep (edgeSlot a b)).isLt
  dsimp only
  split <;> split
  all_goals first | exact he.1 | exact he.2

/-- Both reads show two adjacent colours when `noon` is a neighbour of `phys`. -/
theorem readColours_adj (g : Position) (phys noon : Fin 12) (pos : Nat) (hn : noon ∈ nbrs phys) :
    (readColours g phys noon pos).2 ∈ nbrs (readColours g phys noon pos).1 := by
  unfold readColours
  split
  · exact colours_adj g phys noon hn
  · exact edge_colours_adj g phys noon

/-! ## `ReadOk` from a neighbour pair -/

theorem absReorient?_some_iff (c1 c2 : Fin 12) :
    (absReorient? c1 c2).isSome = decide (c2 ∈ nbrs c1) := by
  have := allFin12_spec (allFin12_spec absReorient?_isSome_iff c1) c2
  simpa using this

theorem readOk_of_mem (g : Position) (phys noon : Fin 12) (pos : Nat) (hn : noon ∈ nbrs phys) :
    ReadOk g phys noon pos := by
  constructor
  · exact hn
  · have := allFin12_spec (allFin12_spec cslot_table phys) noon
    simpa [hn] using this
  · have := allFin12_spec (allFin12_spec eslot_table phys) noon
    simpa [hn] using this
  · rw [absReorient?_some_iff]
    exact decide_eq_true (readColours_adj g phys noon pos hn)

/-! ## `GripOk` is preserved -/

theorem absReorient?_spec (c1 c2 : Fin 12) (r : Grip) (h : absReorient? c1 c2 = some r) :
    (∃ s, s < 60 ∧ r = rotAt s) ∧ r 0 = c1 ∧ r 1 = c2 := by
  unfold absReorient? at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some'.mp h
  have hmem := List.mem_of_find?_eq_some hs
  have := List.find?_some hs
  refine ⟨⟨s, List.mem_range.mp hmem, rfl⟩, ?_⟩
  simpa using this

theorem gripOk_absReorient (c1 c2 : Fin 12) (h : c2 ∈ nbrs c1) : GripOk (absReorient c1 c2) := by
  have hs : (absReorient? c1 c2).isSome := by rw [absReorient?_some_iff]; exact decide_eq_true h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have hA : absReorient c1 c2 = r := by unfold absReorient; rw [hr]; rfl
  rw [hA]
  exact (absReorient?_spec c1 c2 r hr).1

theorem gripOk_readGrip (g : Position) (phys noon : Fin 12) (pos : Nat) (hn : noon ∈ nbrs phys) :
    GripOk (readGrip g phys noon pos) :=
  gripOk_absReorient _ _ (readColours_adj g phys noon pos hn)

/-- `Grip` equality on all 12 hold positions, as a Boolean. -/
def gripEqB (a b : Grip) : Bool := allFin12 (fun h => decide (a h = b h))

theorem gripEqB_spec {a b : Grip} (h : gripEqB a b = true) : a = b :=
  funext fun i => of_decide_eq_true (allFin12_spec h i)

/-- Spinning a rotation about its Up face gives the rotation with the spun Up and
    Front (kernel `decide!` over 60 rotations × 5 amounts). -/
theorem spin_table :
    (List.range 60).all (fun s => (List.range 5).all (fun k =>
      let o' := spinAboutUp (rotAt s) k
      (absReorient? (o' 0) (o' 1)).isSome && gripEqB o' (absReorient (o' 0) (o' 1)))) = true := by
  decide!

theorem spinAboutUp_mod (o : Grip) (k : Nat) : spinAboutUp o k = spinAboutUp o (k % 5) := by
  unfold spinAboutUp
  rw [Nat.mod_mod]

theorem gripOk_spin (o : Grip) (k : Nat) (h : GripOk o) : GripOk (spinAboutUp o k) := by
  obtain ⟨s, hs, rfl⟩ := h
  rw [spinAboutUp_mod]
  have ht := spin_table
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at ht
  obtain ⟨h1, h2⟩ := ht s hs (k % 5) (Nat.mod_lt _ (by decide))
  rw [gripEqB_spec h2]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h1
  have hA : absReorient (spinAboutUp (rotAt s) (k % 5) 0) (spinAboutUp (rotAt s) (k % 5) 1) = r := by
    unfold absReorient; rw [hr]; rfl
  rw [hA]
  exact (absReorient?_spec _ _ r hr).1

theorem gripOk_g2Mid (st : Position × Grip) (card : Nat) (h : GripOk st.2) :
    GripOk (g2Mid st card).2.1 := by
  unfold g2Mid
  by_cases hr : card / 4 < 12
  · simp only [dif_pos hr]; exact h
  · simp only [dif_neg hr]; exact gripOk_spin _ _ h

theorem g2Ok_of_gripOk (g : Position) (o : Grip) (card pos : Nat) (h : GripOk o) :
    G2Ok (g, o) card pos :=
  readOk_of_mem _ _ _ _ (visualNoon_mem _ (gripOk_g2Mid (g, o) card h) _)

theorem f3Ok_of_gripOk (g : Position) (o : Grip) (rnd : Nat) (h : GripOk o) : F3Ok (g, o) rnd :=
  readOk_of_mem _ _ _ _ (visualNoon_mem o h 0)

theorem gripOk_g2Step (st : Position × Grip) (card pos : Nat) (h : GripOk st.2) :
    GripOk (g2Step st card pos).2 := by
  rw [g2Step_eq]
  exact gripOk_readGrip _ _ _ _ (visualNoon_mem _ (gripOk_g2Mid st card h) _)

theorem gripOk_f3Step (st : Position × Grip) (rnd : Nat) (h : GripOk st.2) :
    GripOk (f3Step st rnd).2 :=
  gripOk_readGrip _ _ _ _ (visualNoon_mem st.2 h 0)

/-- Unconditional forms of the step refinements on rotation grips. -/
theorem f3_step_refines' (g : Position) (o : Grip) (rnd : Nat) (h : GripOk o) :
    Megadreifach.f3_step (embedPos g) (embedGrip o) (Int.ofNat rnd) =
      .ok (embedPos (f3Step (g, o) rnd).1, embedGrip (f3Step (g, o) rnd).2) :=
  f3_step_refines g o rnd (f3Ok_of_gripOk g o rnd h)

theorem g2_step_refines' (g : Position) (o : Grip) (card pos : Nat) (h : GripOk o) :
    Megadreifach.g2_step (embedPos g) (embedGrip o) (Int.ofNat card) (Int.ofNat pos) =
      .ok (embedPos (g2Step (g, o) card pos).1, embedGrip (g2Step (g, o) card pos).2) :=
  g2_step_refines g o card pos (g2Ok_of_gripOk g o card pos h)

end MegaDreifach.Link2
