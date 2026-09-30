/-
  LINK 2. Corner-colour helpers of E_m: `corner_slot`, `colour_on`,
  `colours_at`.

  * `corner_slot_refines` / `corner_slot_traps`: exact on all `12^3` face
    triples (finite table, kernel `decide!`).
  * `colour_on_refines`: symbolic, all inputs (`Fin 12` faces/colours,
    `Fin 3` twist).
  * `colours_at_refines`: every algebraic position, on a face triple that is
    a corner (`cornerSlot? a b c = some slot`).

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifachV1.Link2.EmHelpers

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

/-! ## `corner_slot` -/

/-- Exact agreement of `corner_slot` with `cornerSlot?`, as a Boolean. -/
def slotAgree (x : Except SudoRt.Trap Int) (y : Option (Fin 20)) : Bool :=
  match x, y with
  | .ok v, some s => v == Int.ofNat s.val
  | .error _, none => true
  | _, _ => false

theorem corner_slot_table :
    allFin12 (fun a => allFin12 (fun b => allFin12 (fun c =>
      slotAgree (Megadreifach.corner_slot (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val))
        (cornerSlot? a b c)))) = true := by
  decide!

theorem corner_slot_refines (a b c : Fin 12) (s : Fin 20) (h : cornerSlot? a b c = some s) :
    Megadreifach.corner_slot (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val) =
      .ok (Int.ofNat s.val) := by
  have ht := allFin12_spec (allFin12_spec (allFin12_spec corner_slot_table a) b) c
  rw [h] at ht
  cases hx : Megadreifach.corner_slot (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val) with
  | ok v => rw [hx] at ht; simp [slotAgree] at ht; rw [ht]; rfl
  | error e => rw [hx] at ht; simp [slotAgree] at ht

theorem corner_slot_traps (a b c : Fin 12) (h : cornerSlot? a b c = none) :
    ∃ e, Megadreifach.corner_slot (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val) =
      .error e := by
  have ht := allFin12_spec (allFin12_spec (allFin12_spec corner_slot_table a) b) c
  rw [h] at ht
  cases hx : Megadreifach.corner_slot (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val) with
  | ok v => rw [hx] at ht; simp [slotAgree] at ht
  | error e => exact ⟨e, rfl⟩

/-! ## `colour_on` -/

private theorem sEq_ofNat' (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

/-- `Generated.colour_on` refines `Em.colourOn` on all face/colour ids and twists. -/
theorem colour_on_refines (face f0 f1 f2 c0 c1 c2 : Fin 12) (ori : Fin 3) :
    Megadreifach.colour_on (Int.ofNat face.val) (Int.ofNat f0.val) (Int.ofNat f1.val)
        (Int.ofNat f2.val) (Int.ofNat c0.val) (Int.ofNat c1.val) (Int.ofNat c2.val)
        (Int.ofNat ori.val) =
      .ok (Int.ofNat (colourOn face f1 f2 c0 c1 c2 ori).val) := by
  unfold Megadreifach.colour_on colourOn
  rw [sEq_ofNat', sEq_ofNat']
  have e1 : decide (face.val = f1.val) = decide (face = f1) := by
    by_cases h : face = f1 <;> simp [h, Fin.val_inj]
  have e2 : decide (face.val = f2.val) = decide (face = f2) := by
    by_cases h : face = f2 <;> simp [h, Fin.val_inj]
  rw [e1, e2]
  obtain ⟨o, ho⟩ := ori
  by_cases h1 : face = f1 <;> by_cases h2 : face = f2
  · simp only [eq_true h1, eq_true h2, decide_True, ite_true]
    (match o, ho with
       | 0, _ => rfl
       | 1, _ => rfl
       | 2, _ => rfl)
  · simp only [eq_true h1, eq_false h2, decide_True, decide_False, ite_true, ite_false,
      Bool.false_eq_true]
    (match o, ho with
       | 0, _ => rfl
       | 1, _ => rfl
       | 2, _ => rfl)
  · simp only [eq_false h1, eq_true h2, decide_True, decide_False, ite_true, ite_false,
      Bool.false_eq_true]
    (match o, ho with
       | 0, _ => rfl
       | 1, _ => rfl
       | 2, _ => rfl)
  · simp only [eq_false h1, eq_false h2, decide_False, ite_false, Bool.false_eq_true]
    (match o, ho with
       | 0, _ => rfl
       | 1, _ => rfl
       | 2, _ => rfl)

/-! ## `colours_at` -/

private theorem atL_listOf20 (f : Fin 20 → Fin 20) (i : Fin 20) :
    SudoRt.atL (embed (listOf f)) (Int.ofNat i.val) = .ok (Int.ofNat (f i).val) := by
  have hlen : i.val < (listOf f).length := by rw [listOf_length]; exact i.isLt
  rw [atL_embed (listOf f) i.val hlen]
  simp [listOf, List.getElem_map, List.getElem_range, i.isLt]

private theorem atL_listOfOri20 (f : Fin 20 → Fin 3) (i : Fin 20) :
    SudoRt.atL (embed (listOfOri f)) (Int.ofNat i.val) = .ok (Int.ofNat (f i).val) := by
  have hlen : i.val < (listOfOri f).length := by rw [listOfOri_length]; exact i.isLt
  rw [atL_embed (listOfOri f) i.val hlen]
  simp [listOfOri, List.getElem_map, List.getElem_range, i.isLt]

/-- `Generated.colours_at` refines `Em.coloursAt` when `{a, b, c}` is a corner. -/
theorem colours_at_refines (g : Position) (a b c : Fin 12) (s : Fin 20)
    (h : cornerSlot? a b c = some s) :
    Megadreifach.colours_at (embedPos g) (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat c.val) =
      .ok (Int.ofNat (coloursAt g a b c).1.val, Int.ofNat (coloursAt g a b c).2.val) := by
  have hs : cornerSlot a b c = s := by simp [cornerSlot, h]
  unfold Megadreifach.colours_at coloursAt
  rw [corner_slot_refines a b c s h, ok_bind]
  dsimp only
  rw [corner_faces_refines s, ok_bind]
  dsimp only
  rw [show (embedPos g).sudo_8Position_2cp = embed (listOf g.cp) from rfl,
    show (embedPos g).sudo_8Position_2co = embed (listOfOri g.co) from rfl,
    atL_listOf20, ok_bind, atL_listOfOri20, ok_bind, corner_faces_refines (g.cp s), ok_bind]
  dsimp only
  rw [colour_on_refines, ok_bind, colour_on_refines, ok_bind, hs]
  rfl

end MegaDreifachV1.Link2
