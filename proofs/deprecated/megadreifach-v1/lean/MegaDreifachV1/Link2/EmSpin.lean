/-
  LINK 2. `Generated.spin_about_up` refines `Em.spinAboutUp` on every grip
  `o : Fin 12 → Fin 12` and every amount `k`.

  The emitted body: `k mod 5`; on `0` return `o`; otherwise build `phys` from
  `range_list(12)` by two 5-step write loops (up ring `+k`, down ring `-k`),
  two point writes (`up`, `down`), then `out[h] = phys[o[h]]`.
  The write loops are `chain_loop`s over `List.set` folds; the resulting
  table equals `spinPhys up k` for every `up : Fin 12`, `k ∈ 1..4`
  (48-case kernel `decide`).

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifachV1.Link2.EmRecipe
import MegaDreifachV1.Link2.Inverse
import MegaDreifachV1.Link2.EvenRank

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

/-! ## Small arithmetic -/

theorem narrowI_small (x : Int) (h1 : -1000 ≤ x) (h2 : x ≤ 1000) :
    SudoRt.narrowI x = .ok x := by
  unfold SudoRt.narrowI
  have : ¬ ((x < SudoRt.i64Min || x > SudoRt.i64Max) = true) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    constructor
    · show ¬ x < -9223372036854775808; omega
    · show ¬ x > 9223372036854775807; omega
  rw [if_neg this]

theorem sub_add5 (i k : Nat) (hi : i ≤ 4) (hk : k ≤ 4) :
    (SudoRt.subI (Int.ofNat i) (Int.ofNat k) >>= fun t => SudoRt.addI t (5 : Int)) =
      .ok (Int.ofNat (i + 5 - k)) := by
  unfold SudoRt.subI SudoRt.addI
  simp only [ofNat_eq_natCast]
  rw [narrowI_small _ (by omega) (by omega), ok_bind, narrowI_small _ (by omega) (by omega)]
  congr 1
  push_cast [Nat.sub_add_comm, show k ≤ i + 5 by omega]
  omega

/-! ## `opposites` -/

theorem opposites_table :
    allFin12 (fun u => isOkEq (SudoRt.atL Megadreifach.opposites (Int.ofNat u.val))
      (Int.ofNat (opp u).val)) = true := by
  decide!

theorem atL_opposites (u : Fin 12) :
    SudoRt.atL Megadreifach.opposites (Int.ofNat u.val) = .ok (Int.ofNat (opp u).val) :=
  isOkEq_spec (allFin12_spec opposites_table u)

/-! ## The `phys` table -/

/-- After `i` up-ring writes. -/
def upPre (up : Fin 12) (k i : Nat) : List Nat :=
  (List.range i).foldl (fun acc j => acc.set (nbr up j).val (nbr up ((j + k) % 5)).val)
    (List.range 12)

/-- After all up-ring writes and `i` down-ring writes. -/
def downPre (up : Fin 12) (k i : Nat) : List Nat :=
  (List.range i).foldl
    (fun acc j => acc.set (nbr (opp up) j).val (nbr (opp up) ((j + 5 - k) % 5)).val)
    (upPre up k 5)

/-- Final `phys` table (after the two point writes). -/
def physFinal (up : Fin 12) (k : Nat) : List Nat :=
  ((downPre up k 5).set up.val up.val).set (opp up).val (opp up).val

theorem upPre_succ (up : Fin 12) (k i : Nat) :
    upPre up k (i + 1) = (upPre up k i).set (nbr up i).val (nbr up ((i + k) % 5)).val := by
  simp [upPre, List.range_succ, List.foldl_append]

theorem downPre_succ (up : Fin 12) (k i : Nat) :
    downPre up k (i + 1) =
      (downPre up k i).set (nbr (opp up) i).val (nbr (opp up) ((i + 5 - k) % 5)).val := by
  simp [downPre, List.range_succ, List.foldl_append]

theorem upPre_length (up : Fin 12) (k i : Nat) : (upPre up k i).length = 12 := by
  induction i with
  | zero => simp [upPre]
  | succ i ih => rw [upPre_succ, List.length_set, ih]

theorem downPre_length (up : Fin 12) (k i : Nat) : (downPre up k i).length = 12 := by
  induction i with
  | zero => simp [downPre, upPre_length]
  | succ i ih => rw [downPre_succ, List.length_set, ih]

/-- The emitted `phys` table is the algebraic relabelling `spinPhys`. -/
theorem physFinal_table :
    allFin12 (fun up => (List.range 4).all fun j =>
      decide (physFinal up (j + 1) = (List.range 12).map
        (fun x => if h : x < 12 then (spinPhys up (j + 1) ⟨x, h⟩).val else 0))) = true := by
  decide!

theorem physFinal_eq (up : Fin 12) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 4) :
    physFinal up k = (List.range 12).map
      (fun x => if h : x < 12 then (spinPhys up k ⟨x, h⟩).val else 0) := by
  have ht := allFin12_spec physFinal_table up
  rw [List.all_eq_true] at ht
  have := ht (k - 1) (List.mem_range.mpr (by omega))
  rw [show k - 1 + 1 = k from by omega] at this
  simpa using this

theorem physFinal_getElem (up : Fin 12) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 4) (x : Fin 12)
    (hx : x.val < (physFinal up k).length) :
    (physFinal up k)[x.val] = (spinPhys up k x).val := by
  have h := physFinal_eq up k hk1 hk
  simp only [h, List.getElem_map, List.getElem_range, x.isLt, dite_true]


private theorem sEq_ofNat3 (a b : Nat) :
    SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
  rw [sEq_int]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (Int.ofNat a = Int.ofNat b) := fun e => h (Int.ofNat.inj e)
    simp [h]
    exact this

theorem subI_small (i k : Nat) (hi : i ≤ 4) (hk : k ≤ 4) :
    SudoRt.subI (Int.ofNat i) (Int.ofNat k) = .ok ((i : Int) - (k : Int)) := by
  unfold SudoRt.subI
  simp only [ofNat_eq_natCast]
  exact narrowI_small _ (by omega) (by omega)

theorem addI_small5 (i k : Nat) (hi : i ≤ 4) (hk : k ≤ 4) :
    SudoRt.addI ((i : Int) - (k : Int)) (Int.ofNat 5) = .ok (Int.ofNat (i + 5 - k)) := by
  unfold SudoRt.addI
  rw [show Int.ofNat 5 = (5 : Int) from rfl, narrowI_small _ (by omega) (by omega)]
  congr 1
  simp only [ofNat_eq_natCast]
  omega

/-! ## Output loop prefixes -/

private theorem push_embed' (xs : List Nat) (b : Nat) :
    (embed xs).push (Int.ofNat b) = embed (xs ++ [b]) := by
  apply Array.ext'
  simp [embed, toList_push]

private theorem map_range_take (F : Nat → Nat) (k n : Nat) (hk : k ≤ n) :
    ((List.range n).map F).take k = (List.range k).map F := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

private theorem take_push (F : Nat → Nat) (n i : Nat) (hi : i < n) :
    (embed (((List.range n).map F).take i)).push (Int.ofNat (F i)) =
      embed (((List.range n).map F).take (i + 1)) := by
  rw [push_embed', map_range_take F i n (Nat.le_of_lt hi),
    map_range_take F (i + 1) n (Nat.succ_le_of_lt hi)]
  simp [List.range_succ]

/-! ## Main refinement -/

theorem atL_grip (o : Grip) (i : Nat) (hi : i < 12) :
    SudoRt.atL (embedGrip o) (Int.ofNat i) = .ok (Int.ofNat (o ⟨i, hi⟩).val) := by
  have hlen : i < (listOf o).length := by rw [listOf_length]; exact hi
  rw [embedGrip, atL_embed (listOf o) i hlen]
  simp [listOf, List.getElem_map, List.getElem_range, hi]


theorem atL_grip0 (o : Grip) :
    SudoRt.atL (embedGrip o) (Int.ofNat 0) = .ok (Int.ofNat (o 0).val) :=
  atL_grip o 0 (by decide)

/-- Output cell `h` of `spin_about_up`. -/
def spinOut (o : Grip) (up : Fin 12) (k : Nat) (h : Nat) : Nat :=
  if hh : h < 12 then (spinPhys up k (o ⟨h, hh⟩)).val else 0

theorem listOf_spinAboutUp (o : Grip) (k : Nat) (hk : k % 5 ≠ 0) :
    listOf (spinAboutUp o k) = (List.range 12).map (spinOut o (o 0) (k % 5)) := by
  unfold spinAboutUp
  rw [if_neg hk]
  rfl

/-- `Generated.spin_about_up` refines `Em.spinAboutUp` for every grip and amount. -/
theorem spin_about_up_refines (o : Grip) (k : Nat) :
    Megadreifach.spin_about_up (embedGrip o) (Int.ofNat k) = .ok (embedGrip (spinAboutUp o k)) := by
  unfold Megadreifach.spin_about_up
  rw [show (5 : Int) = Int.ofNat 5 from rfl, modI_ofNat k (by decide : (5 : Nat) ≠ 0), ok_bind]
  dsimp only
  rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat3]
  by_cases h0 : k % 5 = 0
  · rw [decide_eq_true h0]
    simp only [ite_true]
    unfold spinAboutUp
    rw [if_pos h0]
    rfl
  · rw [decide_eq_false h0]
    simp only [Bool.false_eq_true, ite_false]
    have hk1 : 1 ≤ k % 5 := Nat.pos_of_ne_zero h0
    have hk4 : k % 5 ≤ 4 := by have := Nat.mod_lt k (by decide : 5 > 0); omega
    rw [show Megadreifach.held_up = Int.ofNat 0 from rfl, atL_grip0 o, ok_bind,
      atL_opposites, ok_bind, face_nbrs_refines, ok_bind, face_nbrs_refines, ok_bind,
      show (12 : Int) = Int.ofNat 12 from rfl,
      range_list_refines 12 (by decide) (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 12) (Nat.le_refl _)), ok_bind]
    rw [except_bind_pure]
    -- up-ring writes
    apply chain_loop (f := fun i => embed (upPre (o 0) (k % 5) i)) (fromN := 0) (toN := 4)
      (hle := by decide)
    · intro i _ hi
      dsimp only
      rw [show (4 : Int) = Int.ofNat 4 from rfl, if_neg (ofNat_not_gt hi),
        atL_nbrsArr _ i (by omega), ok_bind,
        addI_ofNat _ _ (FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 8)
          (by omega)), ok_bind,
        modI_ofNat _ (by decide : (5 : Nat) ≠ 0), ok_bind,
        atL_nbrsArr _ _ (Nat.mod_lt _ (by decide)), ok_bind,
        putL_embed _ _ _ (by rw [upPre_length]; exact (nbr _ _).isLt), ok_bind, pure_bind]
      dsimp only
      rw [← upPre_succ]
      exact loopTailR i 4 hi (by decide) _
    · dsimp only
      rw [except_bind_pure]
      -- down-ring writes
      apply chain_loop (f := fun i => embed (downPre (o 0) (k % 5) i)) (fromN := 0) (toN := 4)
        (hle := by decide)
      · intro i _ hi
        dsimp only
        rw [show (4 : Int) = Int.ofNat 4 from rfl, if_neg (ofNat_not_gt hi),
          atL_nbrsArr _ i (by omega), ok_bind,
          subI_small i (k % 5) hi hk4, ok_bind, addI_small5 i (k % 5) hi hk4, ok_bind,
          modI_ofNat _ (by decide : (5 : Nat) ≠ 0), ok_bind,
          atL_nbrsArr _ _ (Nat.mod_lt _ (by decide)), ok_bind,
          putL_embed _ _ _ (by rw [downPre_length]; exact (nbr _ _).isLt), ok_bind, pure_bind]
        dsimp only
        rw [← downPre_succ]
        exact loopTailR i 4 hi (by decide) _
      · rw [show (4 + 1 : Nat) = 5 from rfl,
          putL_embed _ _ _ (by rw [downPre_length]; exact (o 0).isLt), ok_bind,
          putL_embed _ _ _ (by rw [List.length_set, downPre_length]; exact (opp (o 0)).isLt),
          ok_bind]
        rw [except_bind_pure]
        -- output loop
        have hlenF : (physFinal (o 0) (k % 5)).length = 12 := by
          rw [physFinal, List.length_set, List.length_set, downPre_length]
        apply chain_loop (f := fun i => embed
            (((List.range 12).map (spinOut o (o 0) (k % 5))).take i))
          (fromN := 0) (toN := 11) (hle := by decide)
        · intro i _ hi
          dsimp only
          have hi12 : i < 12 := by omega
          have hget := physFinal_getElem (o 0) (k % 5) hk1 hk4 (o ⟨i, hi12⟩)
            (by rw [hlenF]; exact (o _).isLt)
          rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hi),
            atL_grip o i hi12, ok_bind]
          rw [show (((downPre (o 0) (k % 5) 5).set (↑(o 0)) ↑(o 0)).set ↑(opp (o 0))
              ↑(opp (o 0))) = physFinal (o 0) (k % 5) from rfl,
            atL_embed _ _ (by rw [hlenF]; exact (o _).isLt), ok_bind, hget, appendL_spec]
          dsimp only
          rw [pure_bind]
          dsimp only
          have hcell : (spinPhys (o 0) (k % 5) (o ⟨i, hi12⟩)).val = spinOut o (o 0) (k % 5) i := by
            simp [spinOut, hi12]
          rw [hcell, take_push _ 12 i hi12]
          exact loopTailR i 11 hi (by decide) _
        · dsimp only
          rw [show embedGrip (spinAboutUp o k) = embed (listOf (spinAboutUp o k)) from rfl,
            listOf_spinAboutUp o k h0]
          rw [List.take_of_length_le (by simp)]
          rfl

end MegaDreifachV1.Link2
