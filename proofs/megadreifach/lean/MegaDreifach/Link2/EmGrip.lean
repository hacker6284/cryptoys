/-
  LINK 2. The v2 grip helpers refine their algebraic models (split out of `EmHelpers.lean`
  and `EmEdge.lean`, unchanged, so that those stay free of v2-only emitted functions and
  can be re-elaborated against the v3 emit).

  * `visual_noon_refines`: `Generated.visual_noon` ≃ `Em.visualNoon` on every
    hold position `p : Fin 12` and every grip `o : Fin 12 → Fin 12` (symbolic;
    no table).
  * `abs_reorient_refines` / `abs_reorient_traps`: exact on all `12^2` colour
    pairs (kernel `decide!`).
  * `corner_after_noon_refines` / `corner_after_noon_traps` (kernel `decide!`).

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.EmEdge

namespace MegaDreifach.Link2

open MegaDreifach.Em

private theorem atL_listOf12 (o : Grip) (i : Nat) (hi : i < 12) :
    SudoRt.atL (embed (listOf o)) (Int.ofNat i) = .ok (Int.ofNat (o ⟨i, hi⟩).val) := by
  have hlen : i < (listOf o).length := by rw [listOf_length]; exact hi
  rw [atL_embed (listOf o) i hlen]
  simp [listOf, List.getElem_map, List.getElem_range, hi]

/-! ## `visual_noon` -/

/-- `Generated.visual_noon` refines `Em.visualNoon` for every hold position and grip. -/
theorem visual_noon_refines (p : Fin 12) (o : Grip) :
    Megadreifach.visual_noon (Int.ofNat p.val) (embed (listOf o)) =
      .ok (Int.ofNat (visualNoon p o).val) := by
  obtain ⟨p, hp⟩ := p
  unfold Megadreifach.visual_noon visualNoon
  rw [show Megadreifach.held_up = Int.ofNat 0 from rfl,
    show Megadreifach.held_front = Int.ofNat 1 from rfl,
    show Megadreifach.lower_ring_first = Int.ofNat 6 from rfl,
    show Megadreifach.held_down = Int.ofNat 11 from rfl,
    show Megadreifach.down_noon_hold = Int.ofNat 6 from rfl]
  dsimp only
  by_cases h0 : p = 0
  · subst h0
    rw [atL_listOf12 o 1 (by decide)]
    rfl
  · have hb : SudoRt.SEq.beq (Int.ofNat p) (Int.ofNat 0) = false := by
      show decide (Int.ofNat p = Int.ofNat 0) = false
      simp only [decide_eq_false_iff_not]; intro hc; exact h0 (Int.ofNat.inj hc)
    rw [hb, if_neg h0]
    simp only [Bool.false_eq_true, ite_false]
    split
    · rename_i hc
      have h6 : p < 6 := Int.ofNat_lt.mp (of_decide_eq_true hc)
      rw [if_pos h6, atL_listOf12 o 0 (by decide)]
      rfl
    · rename_i hc
      have h6 : ¬ p < 6 := fun h => hc (decide_eq_true (Int.ofNat_lt.mpr h))
      rw [if_neg h6]
      split
      · rename_i hc'
        have h11 : p < 11 := Int.ofNat_lt.mp (of_decide_eq_true hc')
        rw [dif_pos h11, show (5 : Int) = Int.ofNat 5 from rfl,
          subI_ofNat p 5 (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 12)
            (by omega)) (by omega), ok_bind, atL_listOf12 o (p - 5) (by omega)]
        rfl
      · rename_i hc'
        have h11 : ¬ p < 11 := fun h => hc' (decide_eq_true (Int.ofNat_lt.mpr h))
        rw [dif_neg h11, atL_listOf12 o 6 (by decide)]
        rfl

/-! ## Finite tables: `face_nbrs`, `corner_faces`, `rot_at` -/

/-! ## `abs_reorient` (exact: result on adjacent pairs, trap otherwise) -/

/-- The emitted grip array of an algebraic grip. -/
def embedGrip (o : Grip) : Array Int := embed (listOf o)

/-- Exact agreement of `abs_reorient` with `absReorient?`, as a Boolean. -/
def absAgree (x : Except SudoRt.Trap (Array Int)) (y : Option Grip) : Bool :=
  match x, y with
  | .ok a, some r => decide (a = embedGrip r)
  | .error _, none => true
  | _, _ => false

theorem abs_reorient_table :
    allFin12 (fun c1 => allFin12 (fun c2 =>
      absAgree (Megadreifach.abs_reorient (Int.ofNat c1.val) (Int.ofNat c2.val))
        (absReorient? c1 c2))) = true := by
  decide!

/-- `Generated.abs_reorient` returns the algebraic rotation whenever one exists. -/
theorem abs_reorient_refines (c1 c2 : Fin 12) (r : Grip) (h : absReorient? c1 c2 = some r) :
    Megadreifach.abs_reorient (Int.ofNat c1.val) (Int.ofNat c2.val) = .ok (embedGrip r) := by
  have ht := allFin12_spec (allFin12_spec abs_reorient_table c1) c2
  rw [h] at ht
  cases hx : Megadreifach.abs_reorient (Int.ofNat c1.val) (Int.ofNat c2.val) with
  | ok a => rw [hx] at ht; simp [absAgree] at ht; rw [ht]
  | error e => rw [hx] at ht; simp [absAgree] at ht

/-- … and traps (the emitted `assert false`) exactly when none exists. -/
theorem abs_reorient_traps (c1 c2 : Fin 12) (h : absReorient? c1 c2 = none) :
    ∃ e, Megadreifach.abs_reorient (Int.ofNat c1.val) (Int.ofNat c2.val) = .error e := by
  have ht := allFin12_spec (allFin12_spec abs_reorient_table c1) c2
  rw [h] at ht
  cases hx : Megadreifach.abs_reorient (Int.ofNat c1.val) (Int.ofNat c2.val) with
  | ok a => rw [hx] at ht; simp [absAgree] at ht
  | error e => exact ⟨e, rfl⟩

/-- `abs_reorient c1 c2` succeeds iff `c2` is a neighbour of `c1`. -/
theorem absReorient?_isSome_iff :
    allFin12 (fun c1 => allFin12 (fun c2 =>
      (absReorient? c1 c2).isSome == decide (c2 ∈ nbrs c1))) = true := by
  decide!

/-! ## `corner_after_noon` -/

/-- Exact agreement of `corner_after_noon` with the model: the model value when
    `ok`, a trap otherwise. -/
def canAgree (x : Except SudoRt.Trap Int) (ok : Bool) (y : Int) : Bool :=
  match x with
  | .ok v => ok && v == y
  | .error _ => !ok

theorem corner_after_noon_table :
    allFin12 (fun p => allFin12 (fun n =>
      canAgree (Megadreifach.corner_after_noon (Int.ofNat p.val) (Int.ofNat n.val))
        (decide (n ∈ nbrs p)) (Int.ofNat (cornerAfterNoon p n).val))) = true := by
  decide!

theorem corner_after_noon_refines (p n : Fin 12) (h : n ∈ nbrs p) :
    Megadreifach.corner_after_noon (Int.ofNat p.val) (Int.ofNat n.val) =
      .ok (Int.ofNat (cornerAfterNoon p n).val) := by
  have ht := allFin12_spec (allFin12_spec corner_after_noon_table p) n
  cases hx : Megadreifach.corner_after_noon (Int.ofNat p.val) (Int.ofNat n.val) with
  | ok v => rw [hx] at ht; simp [canAgree, h] at ht; rw [ht]; rfl
  | error e => rw [hx] at ht; simp [canAgree, h] at ht

theorem corner_after_noon_traps (p n : Fin 12) (h : n ∉ nbrs p) :
    ∃ e, Megadreifach.corner_after_noon (Int.ofNat p.val) (Int.ofNat n.val) = .error e := by
  have ht := allFin12_spec (allFin12_spec corner_after_noon_table p) n
  cases hx : Megadreifach.corner_after_noon (Int.ofNat p.val) (Int.ofNat n.val) with
  | ok v => rw [hx] at ht; simp [canAgree, h] at ht
  | error e => exact ⟨e, rfl⟩

end MegaDreifach.Link2
