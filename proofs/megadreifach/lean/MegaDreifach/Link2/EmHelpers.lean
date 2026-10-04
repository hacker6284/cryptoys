/-
  LINK 2. Table-driven E_m helpers refine their algebraic models.

  * `face_nbrs_refines`, `corner_faces_refines`: finite tables (kernel `decide!`).
  * the list views of positions (`posL`, `posOfLists_listOf`).
  The grip lemmas (`visual_noon`, `abs_reorient`, `corner_after_noon`) are in
  `EmGrip.lean`: they are v2-only, and this module is shared with the v3 package.

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.Compose
import MegaDreifach.Em

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- Boolean check `x = .ok y` (so finite tables can be closed by `decide!`). -/
def isOkEq (x : Except SudoRt.Trap Int) (y : Int) : Bool :=
  match x with
  | .ok v => v == y
  | .error _ => false

theorem isOkEq_spec {x : Except SudoRt.Trap Int} {y : Int} (h : isOkEq x y = true) :
    x = .ok y := by
  unfold isOkEq at h
  split at h
  · rename_i v; simp at h; rw [h]
  · simp at h

/-- `∀ i : Fin 12` as a Boolean. -/
def allFin12 (P : Fin 12 → Bool) : Bool :=
  (List.range 12).all fun i => if h : i < 12 then P ⟨i, h⟩ else true

theorem allFin12_spec {P : Fin 12 → Bool} (h : allFin12 P = true) (i : Fin 12) : P i = true := by
  unfold allFin12 at h
  rw [List.all_eq_true] at h
  have := h i.val (List.mem_range.mpr i.isLt)
  simpa [i.isLt] using this

/-- `x = .ok a` for an array result, as a Boolean. -/
def isOkArr (x : Except SudoRt.Trap (Array Int)) (a : Array Int) : Bool :=
  match x with
  | .ok v => decide (v = a)
  | .error _ => false

theorem isOkArr_spec {x : Except SudoRt.Trap (Array Int)} {a : Array Int}
    (h : isOkArr x a = true) : x = .ok a := by
  unfold isOkArr at h
  split at h
  · rename_i v; simp at h; rw [h]
  · simp at h

/-- A face ring as the emitted array. -/
def nbrsArr (f : Fin 12) : Array Int := embed ((nbrs f).map (·.val))

theorem face_nbrs_table :
    allFin12 (fun f => isOkArr (Megadreifach.face_nbrs (Int.ofNat f.val)) (nbrsArr f)) = true := by
  decide!

theorem face_nbrs_refines (f : Fin 12) :
    Megadreifach.face_nbrs (Int.ofNat f.val) = .ok (nbrsArr f) :=
  isOkArr_spec (allFin12_spec face_nbrs_table f)

theorem nbrsArr_size (f : Fin 12) : (nbrsArr f).size = 5 := by
  simp [nbrsArr, size_embed, nbrs]

theorem atL_nbrsArr (f : Fin 12) (i : Nat) (hi : i < 5) :
    SudoRt.atL (nbrsArr f) (Int.ofNat i) = .ok (Int.ofNat (nbr f i).val) := by
  rw [nbrsArr, atL_embed _ i (by simp [nbrs]; exact hi)]
  simp [nbrs, nbr, hi]

/-- `x = .ok (a, b, c)` for a triple result, as a Boolean. -/
def isOkTri (x : Except SudoRt.Trap (Int × Int × Int)) (a b c : Int) : Bool :=
  match x with
  | .ok v => decide (v = (a, b, c))
  | .error _ => false

theorem isOkTri_spec {x : Except SudoRt.Trap (Int × Int × Int)} {a b c : Int}
    (h : isOkTri x a b c = true) : x = .ok (a, b, c) := by
  unfold isOkTri at h
  split at h
  · rename_i v; simp at h; rw [h]
  · simp at h

/-- `∀ i : Fin 20` as a Boolean. -/
def allFin20 (P : Fin 20 → Bool) : Bool :=
  (List.range 20).all fun i => if h : i < 20 then P ⟨i, h⟩ else true

theorem allFin20_spec {P : Fin 20 → Bool} (h : allFin20 P = true) (i : Fin 20) : P i = true := by
  unfold allFin20 at h
  rw [List.all_eq_true] at h
  have := h i.val (List.mem_range.mpr i.isLt)
  simpa [i.isLt] using this

theorem corner_faces_table :
    allFin20 (fun s => isOkTri (Megadreifach.corner_faces (Int.ofNat s.val))
      (Int.ofNat (cornerFace s.val 0).val) (Int.ofNat (cornerFace s.val 1).val)
      (Int.ofNat (cornerFace s.val 2).val)) = true := by
  decide!

theorem corner_faces_refines (s : Fin 20) :
    Megadreifach.corner_faces (Int.ofNat s.val) =
      .ok (Int.ofNat (cornerFace s.val 0).val, Int.ofNat (cornerFace s.val 1).val,
        Int.ofNat (cornerFace s.val 2).val) :=
  isOkTri_spec (allFin20_spec corner_faces_table s)

/-! ## List views of positions (used by the heavy KAT witnesses) -/

theorem listOfOri_getD {n m : Nat} (f : Fin n → Fin m) (s : Fin n) :
    (listOfOri f).getD s.val 0 = (f s).val := by
  have hs : s.val < (List.range n).length := by rw [List.length_range]; exact s.isLt
  unfold listOfOri
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs]
  simp [s.isLt]

theorem rd_listOfOri {n m : Nat} (hm : 0 < m) (f : Fin n → Fin m) (s : Fin n) :
    Em.rd (listOfOri f) m hm s.val = f s := by
  apply Fin.ext
  show (listOfOri f).getD s.val 0 % m = (f s).val
  rw [listOfOri_getD]
  exact Nat.mod_eq_of_lt (f s).isLt

theorem listOf_eq_listOfOri {n : Nat} (f : Fin n → Fin n) : listOf f = listOfOri f := rfl

theorem posOfLists_listOf (p : Position) :
    Em.posOfLists (listOf p.cp) (listOfOri p.co) (listOf p.ep) (listOfOri p.eo) = p := by
  apply Position.ext <;> funext s <;> simp only [Em.posOfLists, listOf_eq_listOfOri] <;>
    exact rd_listOfOri _ _ s

/-- List view of a position. -/
def posL (p : Position) : List (List Nat) :=
  [listOf p.cp, listOfOri p.co, listOf p.ep, listOfOri p.eo]

/-- A kernel check on the list view `posL p` gives a `Position` equation. -/
theorem eq_posOfLists_of_posL (p : Position) (a b c d : List Nat)
    (h : posL p = [a, b, c, d]) : p = Em.posOfLists a b c d := by
  unfold posL at h
  simp only [List.cons.injEq] at h
  obtain ⟨ha, hb, hc, hd, -⟩ := h
  rw [← ha, ← hb, ← hc, ← hd, posOfLists_listOf]

end MegaDreifach.Link2
