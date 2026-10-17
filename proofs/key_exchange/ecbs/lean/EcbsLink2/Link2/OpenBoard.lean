/-
  The board a key walk hands to `walk_chord`: `new_board`, then the base point
  in homes 3 and 4. The opening copy, with the marker still `-1`, writes that
  point into homes 0 and 1. Strict, hole, control, and slides stay the board
  `new_board` returned. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.CopyMirror
import EcbsLink2.Link2.ClimbEmit
import EcbsLink2.Link2.EntryRung

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem set_reset_bool :
    (((Array.mkArray 8 false).set ⟨6, by simp [Array.size_mkArray]⟩ true).set
        ⟨6, by simp [Array.size_set, Array.size_mkArray]⟩ false) =
      Array.mkArray 8 false := by
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    simp [Array.getElem_set, Array.getElem_mkArray]

private theorem set_reset_home (xs : Array Int) :
    (((Array.mkArray 8 (#[] : Array Int)).set ⟨6, by simp [Array.size_mkArray]⟩ xs).set
        ⟨6, by simp [Array.size_set, Array.size_mkArray]⟩ (#[] : Array Int)) =
      Array.mkArray 8 (#[] : Array Int) := by
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    by_cases hi : i = 6
    · simp [hi, Array.getElem_set, Array.getElem_mkArray]
    · simp only [Array.getElem_set]
      split
      · rename_i heq
        exact absurd heq.symm hi
      · simp only [Array.getElem_set, Array.getElem_mkArray, hi]

theorem built_szH (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4home.size = 8 := by
  simp [builtBoard, midBoard, placed, blankOf, Array.size_set, Array.size_mkArray]

theorem built_szD (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held.size = 8 := by
  simp [builtBoard, midBoard, placed, blankOf, Array.size_set, Array.size_mkArray]

theorem built_held_arr (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held = Array.mkArray 8 false := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_bool]

theorem built_home_arr (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4home = Array.mkArray 8 (#[] : Array Int) := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_home]

theorem built_tier_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_1t = embTier t := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_slides0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_ctrl_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) := by
  simp [builtBoard, midBoard, placed, blankOf, tierR]

theorem built_mx0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_tmax0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_9tally_max = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_ops_arr (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_bench_off (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_8bench_on = false := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_marker_down (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_6marker = -1 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_flag_off (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_9marker_on = false := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_tally0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_9tally_len = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_t0_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_6tally0 = Int.ofNat (tallyOrigin t) := by
  have hsum : t.script + 2 + (rungList (t.n - 1)).length + 1 = tallyOrigin t := by
    unfold tallyOrigin tierR
    omega
  simp [builtBoard, midBoard, placed, blankOf, hsum]

theorem built_row_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_3row = embed (paintedRow t) := by
  simp [builtBoard, midBoard, placed, blankOf, paintedRow]

theorem built_ladder_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [builtBoard, tierClimb]

theorem built_l0_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_7ladder0 = Int.ofNat (t.script + 2) := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_nr_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_6nrungs = Int.ofNat (tierR t) := by
  simp [builtBoard, midBoard, placed, blankOf, tierR]

theorem built_park_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_9park_hole = Int.ofNat (t.script + 2 + tierR t) := by
  simp [builtBoard, midBoard, placed, blankOf, tierR]

theorem built_from_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_11parked_from = -1 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_ridx_eq (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_8rung_idx = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

theorem built_high_eq (t : Spec.Tier) (hR : 0 < tierR t) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      Int.ofNat (t.script + tierR t + 1) := by
  have hne : rungList (t.n - 1) ≠ [] := by
    intro hnil
    apply absurd hR
    unfold tierR
    simp [hnil]
  have hsum : t.script + 2 + (rungList (t.n - 1)).length - 1 = t.script + tierR t + 1 := by
    unfold tierR
    omega
  simp [builtBoard, midBoard, placed, blankOf, hne, hsum]

theorem built_high_lt (t : Spec.Tier) :
    t.script + tierR t + 1 < tallyOrigin t := by
  unfold tallyOrigin
  omega

theorem homeIx (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_szH]; exact hi

theorem heldIx (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_szD]; exact hi

theorem place_stay (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hge : ¬ peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    placeBoard b home hH hD xs moves peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs)
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } } := by
  unfold placeBoard
  dsimp only
  rw [if_neg hge]

theorem place_raise (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat)
    (hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) :
    placeBoard b home hH hD xs moves peak =
      { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs)
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs)
          sudo_5Costs_4peak := Int.ofNat
            (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } } := by
  unfold placeBoard
  dsimp only
  rw [if_pos hlt]

private theorem set_proof_irrel {α : Type} (a : Array α) (i : Nat)
    (h h' : i < a.size) (v : α) :
    a.set ⟨i, h⟩ v = a.set ⟨i, h'⟩ v := by
  have : (⟨i, h⟩ : Fin a.size) = ⟨i, h'⟩ := Fin.ext rfl
  simp [this]

theorem occ_one :
    countHeld ((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
  decide

theorem occ_two :
    countHeld ((((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true).set
      ⟨4, by simp [Array.size_set, Array.size_mkArray]⟩ true)) 7 = 2 := by
  decide

theorem occ_three :
    countHeld (((((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true).set
      ⟨4, by simp [Array.size_set, Array.size_mkArray]⟩ true).set
      ⟨0, by simp [Array.size_set, Array.size_mkArray]⟩ true)) 7 = 3 := by
  decide

theorem occ_four :
    countHeld ((((((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true).set
      ⟨4, by simp [Array.size_set, Array.size_mkArray]⟩ true).set
      ⟨0, by simp [Array.size_set, Array.size_mkArray]⟩ true).set
      ⟨1, by simp [Array.size_set, Array.size_mkArray]⟩ true)) 7 = 4 := by
  decide

theorem put_occ1 (t : Spec.Tier) :
    countHeld ((builtBoard t).sudo_5Board_4held.set ⟨3, heldIx t 3 (by decide)⟩ true) 7 = 1 := by
  simpa [heldIx, ← built_held_arr] using occ_one

/-- Base across written. Peak stays 1, because one held home does not pass it. -/
def putAcross (t : Spec.Tier) (x : List Nat) : Ecbs.Board :=
  let b := builtBoard t
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨3, homeIx t 3 (by decide)⟩ (embed x)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨3, heldIx t 3 (by decide)⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x) } }

theorem putAcross_place (t : Spec.Tier) (x : List Nat) :
    placeBoard (builtBoard t) 3 (homeIx t 3 (by decide)) (heldIx t 3 (by decide)) x 0 1 =
      putAcross t x := by
  have hge : ¬ 1 < countHeld
      ((builtBoard t).sudo_5Board_4held.set ⟨3, heldIx t 3 (by decide)⟩ true) 7 := by
    rw [put_occ1]
    decide
  rw [place_stay (builtBoard t) 3 (homeIx t 3 (by decide)) (heldIx t 3 (by decide)) x 0 1 hge]
  simp [putAcross, Nat.zero_add]

theorem putAcross_szH (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4home.size = 8 := by
  simp [putAcross, Array.size_set, built_szH]

theorem putAcross_szD (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4held.size = 8 := by
  simp [putAcross, Array.size_set, built_szD]

theorem putAcross_home4 (t : Spec.Tier) (x : List Nat) :
    4 < (putAcross t x).sudo_5Board_4home.size := by
  rw [putAcross_szH]; decide

theorem putAcross_held4 (t : Spec.Tier) (x : List Nat) :
    4 < (putAcross t x).sudo_5Board_4held.size := by
  rw [putAcross_szD]; decide

theorem put_occ2 (t : Spec.Tier) (x : List Nat) :
    countHeld ((putAcross t x).sudo_5Board_4held.set ⟨4, putAcross_held4 t x⟩ true) 7 = 2 := by
  simpa [putAcross, putAcross_held4, heldIx, ← built_held_arr] using occ_two

/-- Base across and base up. Peak is 2. -/
def baseBoard (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  let b := putAcross t x
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨4, putAcross_home4 t x⟩ (embed y)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨4, putAcross_held4 t x⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x + pegCount y)
      sudo_5Costs_4peak := 2 } }

theorem base_place (t : Spec.Tier) (x y : List Nat) :
    placeBoard (putAcross t x) 4 (putAcross_home4 t x) (putAcross_held4 t x)
      y (pegCount x) 1 = baseBoard t x y := by
  have hlt : 1 < countHeld
      ((putAcross t x).sudo_5Board_4held.set ⟨4, putAcross_held4 t x⟩ true) 7 := by
    rw [put_occ2]
    decide
  rw [place_raise (putAcross t x) 4 (putAcross_home4 t x) (putAcross_held4 t x)
    y (pegCount x) 1 hlt, put_occ2]
  rfl

theorem base_szH (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4home.size = 8 := by
  simp [baseBoard, putAcross, Array.size_set, built_szH]

theorem base_szD (t : Spec.Tier) (x y : List Nat) :
    (baseBoard t x y).sudo_5Board_4held.size = 8 := by
  simp [baseBoard, putAcross, Array.size_set, built_szD]

theorem base_home0 (t : Spec.Tier) (x y : List Nat) :
    0 < (baseBoard t x y).sudo_5Board_4home.size := by
  rw [base_szH]; decide

theorem base_held0 (t : Spec.Tier) (x y : List Nat) :
    0 < (baseBoard t x y).sudo_5Board_4held.size := by
  rw [base_szD]; decide

theorem base_home1 (t : Spec.Tier) (x y : List Nat) :
    1 < (baseBoard t x y).sudo_5Board_4home.size := by
  rw [base_szH]; decide

theorem base_held1 (t : Spec.Tier) (x y : List Nat) :
    1 < (baseBoard t x y).sudo_5Board_4held.size := by
  rw [base_szD]; decide

/-- The walk flag is on. Homes are still the base point in 3 and 4. -/
def flagged (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  { baseBoard t x y with sudo_5Board_9marker_on := true }

theorem flag_occ3 (t : Spec.Tier) (x y : List Nat) :
    countHeld ((flagged t x y).sudo_5Board_4held.set ⟨0, base_held0 t x y⟩ true) 7 = 3 := by
  simpa [flagged, baseBoard, putAcross, base_held0, heldIx, ← built_held_arr] using occ_three

theorem place_szH (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  rw [place_home_eq, Array.size_set]

theorem place_szD (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  rw [place_held_eq, Array.size_set]

/-- White opening. Homes 0 and 1 hold the base point. The two copies are
    `placeBoard`, so strict, hole, control, slides, and the marker stay. -/
def openAcross (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  placeBoard (flagged t x y) 0 (base_home0 t x y) (base_held0 t x y)
    x (pegCount x + pegCount y) 2

theorem openAcross_home1 (t : Spec.Tier) (x y : List Nat) :
    1 < (openAcross t x y).sudo_5Board_4home.size := by
  rw [openAcross, place_szH]
  simp [flagged]
  rw [base_szH]
  decide

theorem openAcross_held1 (t : Spec.Tier) (x y : List Nat) :
    1 < (openAcross t x y).sudo_5Board_4held.size := by
  rw [openAcross, place_szD]
  simp [flagged]
  rw [base_szD]
  decide

def openWhite (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  placeBoard (openAcross t x y) 1 (openAcross_home1 t x y) (openAcross_held1 t x y)
    y (pegCount x + pegCount y + pegCount x) 3

theorem place_row (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_3row = b.sudo_5Board_3row := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_ladder (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_l0 (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_nr (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_park (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9park_hole = b.sudo_5Board_9park_hole := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_from (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_11parked_from =
      b.sudo_5Board_11parked_from := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_ridx (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_tally (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_t0 (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_high (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_tmax (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_bench (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_flag (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
  unfold placeBoard; dsimp only; split <;> rfl

theorem place_tier (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold placeBoard; dsimp only; split <;> rfl

end EcbsLink2.Link2
