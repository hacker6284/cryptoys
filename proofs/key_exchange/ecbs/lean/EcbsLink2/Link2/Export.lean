/-
  Exported `multiply` and `cube_number`: `new_board`, `put`, `mul` or `cube`,
  `settle`, `value`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.Cube

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

private theorem built_held (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held = Array.mkArray 8 false := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_bool]

private theorem built_home (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4home = Array.mkArray 8 (#[] : Array Int) := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_home]

private theorem built_moves (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_5moves = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem built_peak (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_4peak = 1 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem built_ops0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem countHeld_across :
    countHeld ((Array.mkArray 8 false).set ⟨0, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
  decide

private theorem put_built_across (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (hf : FitsLen (pegCount xs)) :
    let hH : 0 < (builtBoard t).sudo_5Board_4home.size := by
      simp [built_home, Array.size_mkArray]
    let hD : 0 < (builtBoard t).sudo_5Board_4held.size := by
      simp [built_held, Array.size_mkArray]
    Ecbs.put (builtBoard t) ((0 : Nat) : Int) (embed xs) =
      .ok (placeBoard (builtBoard t) 0 hH hD xs 0 1) := by
  intro hH hD
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of h.fits_n) (by omega)
  rw [put_refines (builtBoard t) 0 xs 0 1 hH hD
    (by simp [built_held, Array.size_mkArray])
    (by simp [built_held, Array.getElem_mkArray])
    (by
      have ht : (builtBoard t).sudo_5Board_1t = embTier t := by
        simp [builtBoard, midBoard, placed, blankOf]
      rw [ht, hx]
      exact ofNat_eq_natCast _)
    (by rw [hx]; exact hfn)
    (by simp [built_moves])
    (by simp [built_peak])
    (by simpa [Nat.zero_add] using hf)]

private theorem place_across_peak (t : Spec.Tier) (xs : List Nat)
    (hH : 0 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 0 < (builtBoard t).sudo_5Board_4held.size) :
    placeBoard (builtBoard t) 0 hH hD xs 0 1 =
      { builtBoard t with
        sudo_5Board_4home := (builtBoard t).sudo_5Board_4home.set ⟨0, hH⟩ (embed xs)
        sudo_5Board_4held := (builtBoard t).sudo_5Board_4held.set ⟨0, hD⟩ true
        sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (pegCount xs) } } := by
  unfold placeBoard
  dsimp only
  have hocc : countHeld ((builtBoard t).sudo_5Board_4held.set ⟨0, hD⟩ true) 7 = 1 := by
    simpa [← built_held] using countHeld_across
  rw [hocc]
  simp [Nat.zero_add, show ¬ ((1 : Nat) < 1) from by decide]

private theorem countHeld_two :
    countHeld ((((Array.mkArray 8 false).set ⟨0, by simp [Array.size_mkArray]⟩ true).set
        ⟨1, by simp [Array.size_set, Array.size_mkArray]⟩ true)) 7 = 2 := by
  decide

private theorem across_home (t : Spec.Tier) : 0 < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_home]
  simp [Array.size_mkArray]

private theorem across_held (t : Spec.Tier) : 0 < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held]
  simp [Array.size_mkArray]

/-- Across written, peak still 1, moves equal to the nonzero count. -/
def boardAcross (t : Spec.Tier) (xs : List Nat) : Ecbs.Board :=
  let b := builtBoard t
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨0, across_home t⟩ (embed xs)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨0, across_held t⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount xs) } }

private theorem boardAcross_eq (t : Spec.Tier) (xs : List Nat)
    (hH : 0 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 0 < (builtBoard t).sudo_5Board_4held.size) :
    placeBoard (builtBoard t) 0 hH hD xs 0 1 = boardAcross t xs := by
  rw [place_across_peak]
  rfl

end EcbsLink2.Link2
