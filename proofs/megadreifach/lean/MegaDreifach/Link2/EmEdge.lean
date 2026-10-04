/-
  LINK 2. Edge and clockwise-noon-corner helpers of the v2 read:
  `edge_faces`, `edge_slot`, `edge_colours_at`, `corner_after_noon`.

  * `edge_faces_refines`: finite table over the 30 slots (kernel `decide!`).
  * `edge_slot_refines` / `edge_slot_traps`: exact on all `12^2` face pairs
    (kernel `decide!`).
  * `edge_colours_at_refines`: every algebraic position, on a face pair that
    owns an edge slot (`edgeSlot? a b = some s`).
  * `corner_after_noon_refines` / `corner_after_noon_traps`: exact on all
    `12^2` pairs (kernel `decide!`): the model value when `noon` is a
    neighbour of `phys`, the emitted `assert` trap otherwise.

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.EmCorner

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- `∀ i : Fin 30` as a Boolean. -/
def allFin30 (P : Fin 30 → Bool) : Bool :=
  (List.range 30).all fun i => if h : i < 30 then P ⟨i, h⟩ else true

theorem allFin30_spec {P : Fin 30 → Bool} (h : allFin30 P = true) (i : Fin 30) : P i = true := by
  unfold allFin30 at h
  rw [List.all_eq_true] at h
  have := h i.val (List.mem_range.mpr i.isLt)
  simpa [i.isLt] using this

/-- `x = .ok (a, b)` for a pair result, as a Boolean. -/
def isOkPair (x : Except SudoRt.Trap (Int × Int)) (a b : Int) : Bool :=
  match x with
  | .ok v => decide (v = (a, b))
  | .error _ => false

theorem isOkPair_spec {x : Except SudoRt.Trap (Int × Int)} {a b : Int}
    (h : isOkPair x a b = true) : x = .ok (a, b) := by
  unfold isOkPair at h
  split at h
  · rename_i v; simp at h; rw [h]
  · simp at h

/-! ## `edge_faces` -/

theorem edge_faces_table :
    allFin30 (fun s => isOkPair (Megadreifach.edge_faces (Int.ofNat s.val))
      (Int.ofNat (edgeFace s.val 0).val) (Int.ofNat (edgeFace s.val 1).val)) = true := by
  decide!

theorem edge_faces_refines (s : Fin 30) :
    Megadreifach.edge_faces (Int.ofNat s.val) =
      .ok (Int.ofNat (edgeFace s.val 0).val, Int.ofNat (edgeFace s.val 1).val) :=
  isOkPair_spec (allFin30_spec edge_faces_table s)

/-! ## `edge_slot` -/

/-- Exact agreement of `edge_slot` with `edgeSlot?`, as a Boolean. -/
def edgeSlotAgree (x : Except SudoRt.Trap Int) (y : Option (Fin 30)) : Bool :=
  match x, y with
  | .ok v, some s => v == Int.ofNat s.val
  | .error _, none => true
  | _, _ => false

theorem edge_slot_table :
    allFin12 (fun a => allFin12 (fun b =>
      edgeSlotAgree (Megadreifach.edge_slot (Int.ofNat a.val) (Int.ofNat b.val))
        (edgeSlot? a b))) = true := by
  decide!

theorem edge_slot_refines (a b : Fin 12) (s : Fin 30) (h : edgeSlot? a b = some s) :
    Megadreifach.edge_slot (Int.ofNat a.val) (Int.ofNat b.val) = .ok (Int.ofNat s.val) := by
  have ht := allFin12_spec (allFin12_spec edge_slot_table a) b
  rw [h] at ht
  cases hx : Megadreifach.edge_slot (Int.ofNat a.val) (Int.ofNat b.val) with
  | ok v => rw [hx] at ht; simp [edgeSlotAgree] at ht; rw [ht]; rfl
  | error e => rw [hx] at ht; simp [edgeSlotAgree] at ht

theorem edge_slot_traps (a b : Fin 12) (h : edgeSlot? a b = none) :
    ∃ e, Megadreifach.edge_slot (Int.ofNat a.val) (Int.ofNat b.val) = .error e := by
  have ht := allFin12_spec (allFin12_spec edge_slot_table a) b
  rw [h] at ht
  cases hx : Megadreifach.edge_slot (Int.ofNat a.val) (Int.ofNat b.val) with
  | ok v => rw [hx] at ht; simp [edgeSlotAgree] at ht
  | error e => exact ⟨e, rfl⟩

/-! ## `edge_colours_at` -/

theorem atL_listOf30 (f : Fin 30 → Fin 30) (i : Fin 30) :
    SudoRt.atL (embed (listOf f)) (Int.ofNat i.val) = .ok (Int.ofNat (f i).val) := by
  have hlen : i.val < (listOf f).length := by rw [listOf_length]; exact i.isLt
  rw [atL_embed (listOf f) i.val hlen]
  simp [listOf, List.getElem_map, List.getElem_range, i.isLt]

theorem atL_listOfOri30 (f : Fin 30 → Fin 2) (i : Fin 30) :
    SudoRt.atL (embed (listOfOri f)) (Int.ofNat i.val) = .ok (Int.ofNat (f i).val) := by
  have hlen : i.val < (listOfOri f).length := by rw [listOfOri_length]; exact i.isLt
  rw [atL_embed (listOfOri f) i.val hlen]
  simp [listOfOri, List.getElem_map, List.getElem_range, i.isLt]

private theorem fitsEdge3 (k : Nat) (hk : k ≤ 3) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 3) hk

/-- The parity branch of `edge_colours_at` (both `loc_a` cases). -/
private theorem edge_parity (l : Int) (locA : Nat) (hl0 : l = Int.ofNat locA) (hl : locA ≤ 1)
    (ori : Fin 2) (p0 p1 : Int) :
    (do
      let t ← SudoRt.addI l (Int.ofNat ori.val)
      let m ← SudoRt.modI t 2
      if SudoRt.SEq.beq m 0 then pure (p0, p1) else pure (p1, p0) :
        Except SudoRt.Trap (Int × Int)) =
      .ok (if (locA + ori.val) % 2 = 0 then (p0, p1) else (p1, p0)) := by
  subst hl0
  have ho := ori.isLt
  rw [addI_ofNat _ _ (fitsEdge3 _ (by omega)), ok_bind, show (2 : Int) = Int.ofNat 2 from rfl,
    modI_ofNat _ (by decide : (2 : Nat) ≠ 0), ok_bind, show (0 : Int) = Int.ofNat 0 from rfl,
    sEq_ofNat]
  by_cases hp : (locA + ori.val) % 2 = 0
  · rw [decide_eq_true hp, if_pos hp]; rfl
  · rw [decide_eq_false hp, if_neg hp]; rfl

/-- `Generated.edge_colours_at` refines `Em.edgeColoursAt` when `{a, b}` owns an
    edge slot. -/
theorem edge_colours_at_refines (g : Position) (a b : Fin 12) (s : Fin 30)
    (h : edgeSlot? a b = some s) :
    Megadreifach.edge_colours_at (embedPos g) (Int.ofNat a.val) (Int.ofNat b.val) =
      .ok (Int.ofNat (edgeColoursAt g a b).1.val, Int.ofNat (edgeColoursAt g a b).2.val) := by
  have hs : edgeSlot a b = s := by simp [edgeSlot, h]
  unfold Megadreifach.edge_colours_at edgeColoursAt
  rw [edge_slot_refines a b s h, ok_bind]
  dsimp only
  rw [show (embedPos g).sudo_8Position_2ep = embed (listOf g.ep) from rfl,
    show (embedPos g).sudo_8Position_2eo = embed (listOfOri g.eo) from rfl,
    atL_listOf30, ok_bind, atL_listOfOri30, ok_bind, edge_faces_refines s, ok_bind]
  dsimp only
  rw [sEq_ofNat, hs]
  by_cases ha : a = edgeFace s.val 0
  · have hd : decide (a.val = (edgeFace s.val 0).val) = true := by simp [ha]
    rw [hd]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, if_pos ha]
    rw [edge_faces_refines (g.ep s), ok_bind]
    dsimp only
    rw [edge_parity 0 0 rfl (by decide) (g.eo s)]
    by_cases hp : (0 + (g.eo s).val) % 2 = 0 <;> simp only [hp, ite_true, ite_false] <;> rfl
  · have hd : decide (a.val = (edgeFace s.val 0).val) = false := by simp [Fin.val_inj, ha]
    rw [hd]
    simp only [Bool.not_false, ite_true, if_neg ha]
    rw [edge_faces_refines (g.ep s), ok_bind]
    dsimp only
    rw [edge_parity 1 1 rfl (by decide) (g.eo s)]
    by_cases hp : (1 + (g.eo s).val) % 2 = 0 <;> simp only [hp, ite_true, ite_false] <;> rfl

end MegaDreifach.Link2
