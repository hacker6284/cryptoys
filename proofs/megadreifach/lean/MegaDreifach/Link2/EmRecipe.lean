/-
  LINK 2. `Generated.recipe_a` refines `Em.recipeA`.

  `recipe_a g phys o` = `noon_phys` (`noon_phys_refines`), `face_nbrs`,
  a 5-step last-hit loop for the noon index (`chain_loop`), the next
  clockwise neighbour, `colours_at` (`colours_at_refines`) and
  `abs_reorient` (`abs_reorient_refines`).

  Domain: any algebraic position and grip, plus the two side conditions that
  keep the two emitted `assert false` branches unreachable:
  `cornerSlot? phys noon nextCw = some s` and
  `absReorient? c1 c2 = some r`.  `RecipeOk` packages them.

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifach.Link2.EmCorner

namespace MegaDreifach.Link2

open MegaDreifach.Em

/-- Last index `j < i` with `nbr phys j = noon` (else `0`). -/
def niPre (phys noon : Fin 12) (i : Nat) : Nat :=
  (List.range i).foldl (fun acc j => if nbr phys j = noon then j else acc) 0

theorem niPre_succ (phys noon : Fin 12) (i : Nat) :
    niPre phys noon (i + 1) = if nbr phys i = noon then i else niPre phys noon i := by
  simp [niPre, List.range_succ, List.foldl_append]

theorem niPre_le (phys noon : Fin 12) (i : Nat) : niPre phys noon i ≤ i := by
  induction i with
  | zero => simp [niPre]
  | succ i ih => rw [niPre_succ]; split <;> omega

/-- Noon corner of `recipe_a`: `(phys, noon, next clockwise)`. -/
def recipeNextCw (phys : Fin 12) (o : Grip) : Fin 12 :=
  nbr phys ((niPre phys (noonPhys phys o) 5 + 1) % 5)

/-- Side conditions under which `recipe_a` does not hit an `assert false`. -/
structure RecipeOk (g : Position) (phys : Fin 12) (o : Grip) : Prop where
  slot : (cornerSlot? phys (noonPhys phys o) (recipeNextCw phys o)).isSome
  rot : (absReorient? (coloursAt g phys (noonPhys phys o) (recipeNextCw phys o)).1
          (coloursAt g phys (noonPhys phys o) (recipeNextCw phys o)).2).isSome

private theorem fits6 (k : Nat) (hk : k ≤ 6) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 6) hk

private theorem sEq_ofNat2 (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

/-- Close the inclusive-loop tail at index `i ≤ toN` (any result type `ρ`). -/
theorem loopTailR {α ρ : Type} (i toN : Nat) (hi : i ≤ toN) (htoN : toN ≤ 30) (st : α) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := ρ) (Int.ofNat i, st)) : Except SudoRt.Trap _)
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', st))) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  by_cases heq : i = toN
  · subst heq; simp [beq_int_iff]; rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    have hf : FitsLen (i + 1) :=
      FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 31) (by omega)
    rw [ite_int_beq, if_neg hneI, addI_ofNat_one i hf, ok_bind, if_neg heq]
    rfl

theorem recipeA_eq (g : Position) (phys : Fin 12) (o : Grip) :
    recipeA g phys o =
      absReorient (coloursAt g phys (noonPhys phys o) (recipeNextCw phys o)).1
        (coloursAt g phys (noonPhys phys o) (recipeNextCw phys o)).2 := rfl

/-- `Generated.recipe_a` refines `Em.recipeA` on `RecipeOk`. -/
theorem recipe_a_refines (g : Position) (phys : Fin 12) (o : Grip) (h : RecipeOk g phys o) :
    Megadreifach.recipe_a (embedPos g) (Int.ofNat phys.val) (embedGrip o) =
      .ok (embedGrip (recipeA g phys o)) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h.slot
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.rot
  have hrA : recipeA g phys o = r := by
    rw [recipeA_eq, absReorient, hr]; rfl
  rw [hrA]
  unfold Megadreifach.recipe_a
  rw [show embedGrip o = embed (listOf o) from rfl, noon_phys_refines, ok_bind,
    face_nbrs_refines, ok_bind]
  dsimp only
  rw [except_bind_pure]
  apply chain_loop (f := fun i => Int.ofNat (niPre phys (noonPhys phys o) i))
    (fromN := 0) (toN := 4) (hle := by decide)
  · intro i _ hi
    dsimp only
    rw [show (4 : Int) = Int.ofNat 4 from rfl, if_neg (ofNat_not_gt hi), atL_nbrsArr phys i (by omega), ok_bind, sEq_ofNat2]
    have hfin : ((nbr phys i).val = (noonPhys phys o).val) = (nbr phys i = noonPhys phys o) :=
      propext Fin.val_inj
    by_cases heq : nbr phys i = noonPhys phys o
    · have hd : decide ((nbr phys i).val = (noonPhys phys o).val) = true := by
        simp [Fin.val_inj, heq]
      rw [hd, if_pos rfl, pure_bind]
      dsimp only
      rw [niPre_succ, if_pos heq]
      exact loopTailR i 4 hi (by decide) _
    · have hd : decide ((nbr phys i).val = (noonPhys phys o).val) = false := by
        simp [Fin.val_inj, heq]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      rw [niPre_succ, if_neg heq]
      exact loopTailR i 4 hi (by decide) _
  · dsimp only
    rw [show (4 + 1 : Nat) = 5 from rfl]
    have hni : niPre phys (noonPhys phys o) 5 ≤ 5 := niPre_le _ _ _
    rw [addI_ofNat_one _ (fits6 _ (by omega)), ok_bind,
      show (5 : Int) = Int.ofNat 5 from rfl, modI_ofNat _ (by decide : (5 : Nat) ≠ 0), ok_bind,
      atL_nbrsArr phys _ (Nat.mod_lt _ (by decide)), ok_bind]
    rw [show nbr phys ((niPre phys (noonPhys phys o) 5 + 1) % 5) = recipeNextCw phys o from rfl,
      colours_at_refines g phys (noonPhys phys o) (recipeNextCw phys o) s hs, ok_bind]
    dsimp only
    rw [abs_reorient_refines _ _ r hr, except_bind_pure]

end MegaDreifach.Link2
