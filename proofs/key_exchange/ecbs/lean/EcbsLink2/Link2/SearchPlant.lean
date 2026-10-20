/-
  The search plants `basisPeg` in the base-across home before `curve_side`.
  On a fresh board that is `new_board`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchLoop
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.InvertTie
import EcbsLink2.Link2.InvertStep
import EcbsLink2.Link2.WalkCopy
import EcbsLink2.Link2.CurveTest

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem bind_assoc {α β γ : Type}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m <;> simp [ok_bind, error_bind]

theorem search_plant (t : Spec.Tier) (hOk : BoardOk t) (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put b Ecbs.base_across x) = .ok b' ∧
        b'.sudo_5Board_4home[searchBase]? = some (embed (basisPeg t.n j)) ∧
        b'.sudo_5Board_4held[searchBase]? = some true ∧
        b'.sudo_5Board_1t = embTier t := by
  have hx : (basisPeg t.n j).length = t.n := basisPeg_length t.n j
  have hH : searchBase < (builtBoard t).sudo_5Board_4home.size := by
    rw [built_home_blank]
    simp [searchBase, Array.size_mkArray]
  have hD : searchBase < (builtBoard t).sudo_5Board_4held.size := by
    rw [built_held_blank]
    simp [searchBase, Array.size_mkArray]
  have hempty : (builtBoard t).sudo_5Board_4held[searchBase]'(hD) = false := by
    have hb : searchBase < (Array.mkArray 8 false).size := by
      simp [searchBase, Array.size_mkArray]
    exact cell_eq_of (built_held_blank t) (hb := hb)
      (by simp [searchBase, Array.getElem_mkArray])
  have hfn : FitsLen t.n := by
    have h4 : t.n ≤ 4 * t.n + 8 := by omega
    exact FitsLen.of_le (fits_of hOk.fits_n) h4
  have hpeg : pegCount (basisPeg t.n j) ≤ t.n := by
    have h := pegCount_le (basisPeg t.n j)
    rwa [hx] at h
  have hfit : FitsLen (0 + pegCount (basisPeg t.n j)) := by
    exact FitsLen.of_le hfn (by omega)
  have hn : (builtBoard t).sudo_5Board_1t.sudo_4Tier_1n =
      ((basisPeg t.n j).length : Int) := by
    rw [built_tier, hx]
    simp [embTier]
  have hput := put_refines (builtBoard t) searchBase (basisPeg t.n j) 0 1
    hH hD (held7_le t) hempty hn (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl) (by rw [built_peak1]; rfl) hfit
  rw [new_board_refines t hOk, ok_bind]
  have htail :
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put (builtBoard t) Ecbs.base_across x) =
        Ecbs.put (builtBoard t) ((searchBase : Nat) : Int) (embed (basisPeg t.n j)) := by
    rw [bind_assoc, basis_fill t.n j hj, ok_bind, ← searchBase_int]
  rw [htail]
  let b' := placeBoard (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
  refine ⟨b', hput, ?_, ?_, ?_⟩
  · rw [place_home_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set]
  · rw [place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · rw [place_tier_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, built_tier]

/-- After the plant, `curve_side` copies that peg into the empty bottom. -/
theorem search_copy (t : Spec.Tier) (hOk : BoardOk t) (j : Nat) (hj : j < t.n) :
    ∃ bP bC,
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) = .ok bC ∧
        (do
            let b ← Ecbs.new_board (embTier t)
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            Ecbs.put b Ecbs.base_across x) = .ok bP ∧
        bC.sudo_5Board_4home[searchBottom]? = some (embed (basisPeg t.n j)) ∧
        bC.sudo_5Board_4held[searchBottom]? = some true ∧
        bC.sudo_5Board_4home[searchBase]? = some (embed (basisPeg t.n j)) ∧
        bC.sudo_5Board_4held[searchBase]? = some true := by
  have hx : (basisPeg t.n j).length = t.n := basisPeg_length t.n j
  have hH : searchBase < (builtBoard t).sudo_5Board_4home.size := by
    rw [built_home_blank]; simp [searchBase, Array.size_mkArray]
  have hD : searchBase < (builtBoard t).sudo_5Board_4held.size := by
    rw [built_held_blank]; simp [searchBase, Array.size_mkArray]
  have hempty0 : (builtBoard t).sudo_5Board_4held[searchBase]'(hD) = false := by
    have hb : searchBase < (Array.mkArray 8 false).size := by
      simp [searchBase, Array.size_mkArray]
    exact cell_eq_of (built_held_blank t) (hb := hb)
      (by simp [searchBase, Array.getElem_mkArray])
  have hfn : FitsLen t.n := by
    exact FitsLen.of_le (fits_of hOk.fits_n) (by omega : t.n ≤ 4 * t.n + 8)
  have hpeg : pegCount (basisPeg t.n j) ≤ t.n := by
    have h := pegCount_le (basisPeg t.n j)
    rwa [hx] at h
  have hfit0 : FitsLen (0 + pegCount (basisPeg t.n j)) :=
    FitsLen.of_le hfn (by omega)
  have hn0 : (builtBoard t).sudo_5Board_1t.sudo_4Tier_1n =
      ((basisPeg t.n j).length : Int) := by
    rw [built_tier, hx]; simp [embTier]
  have hput := put_refines (builtBoard t) searchBase (basisPeg t.n j) 0 1
    hH hD (held7_le t) hempty0 hn0 (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl) (by rw [built_peak1]; rfl) hfit0
  have hplantDo :
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put b Ecbs.base_across x) =
        .ok (placeBoard (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1) := by
    rw [new_board_refines t hOk, ok_bind]
    rw [bind_assoc, basis_fill t.n j hj, ok_bind, ← searchBase_int]
    exact hput
  let bP0 := placeBoard (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
  have h2H : searchBottom < bP0.sudo_5Board_4home.size := by
    rw [place_home_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, Array.size_set]
    rw [built_home_blank]; simp [searchBottom, Array.size_mkArray]
  have h2D : searchBottom < bP0.sudo_5Board_4held.size := by
    rw [place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, Array.size_set]
    rw [built_held_blank]; simp [searchBottom, Array.size_mkArray]
  have h3H : searchBase < bP0.sudo_5Board_4home.size := by
    rw [place_home_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, Array.size_set]
    exact hH
  have h3D : searchBase < bP0.sudo_5Board_4held.size := by
    rw [place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, Array.size_set]
    exact hD
  have h7 : 7 ≤ bP0.sudo_5Board_4held.size := by
    rw [place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, Array.size_set]
    exact held7_le t
  have hsrc : bP0.sudo_5Board_4held[searchBase]'(h3D) = true := by
    have hheld := place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
    have hset : ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true)[searchBase]'
        (by rw [Array.size_set]; exact hD) = true := by
      simp [Array.getElem_set]
    exact cell_eq_of hheld hset
  have harr : bP0.sudo_5Board_4home[searchBase]'(h3H) = embed (basisPeg t.n j) := by
    have hhome := place_home_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
    have hset : ((builtBoard t).sudo_5Board_4home.set ⟨searchBase, hH⟩
        (embed (basisPeg t.n j)))[searchBase]'(by rw [Array.size_set]; exact hH) =
        embed (basisPeg t.n j) := by
      simp [Array.getElem_set]
    exact cell_eq_of hhome hset
  have hempty2 : bP0.sudo_5Board_4held[searchBottom]'(h2D) = false := by
    have hheld := place_held_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
    have hidx : searchBottom < (builtBoard t).sudo_5Board_4held.size := by
      rw [built_held_blank]; simp [searchBottom, Array.size_mkArray]
    have hold : (builtBoard t).sudo_5Board_4held[searchBottom]'(hidx) = false := by
      have hb : searchBottom < (Array.mkArray 8 false).size := by
        simp [searchBottom, Array.size_mkArray]
      exact cell_eq_of (built_held_blank t) (hb := hb)
        (by simp [searchBottom, Array.getElem_mkArray])
    have hset : ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true)[searchBottom]'
        (by rw [Array.size_set]; exact hidx) = false := by
      have hne : searchBase ≠ searchBottom := by decide
      simp [Array.getElem_set, hne, hold]
    exact cell_eq_of hheld hset
  have hmoves : bP0.sudo_5Board_4cost.sudo_5Costs_5moves =
      (pegCount (basisPeg t.n j) : Int) := by
    rw [place_moves_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1]
    simp [ofNat_eq_natCast]
  have hpeak : bP0.sudo_5Board_4cost.sudo_5Costs_4peak =
      (if 1 < countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        then countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        else 1 : Nat) := by
    have hp := place_peak_nat (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1
      (by rw [built_peak1]; rfl)
    simpa [ofNat_eq_natCast] using hp
  have hn : bP0.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [place_tier_eq (builtBoard t) searchBase hH hD (basisPeg t.n j) 0 1, built_tier]
    simp [embTier]
  have hfit : FitsLen (pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j)) := by
    apply FitsLen.of_le (fits_of hOk.fits_n)
    have h2 : pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j) ≤ 2 * t.n := by
      omega
    omega
  have hcopy := curve_copy_across bP0 (basisPeg t.n j) t.n (pegCount (basisPeg t.n j))
      (if 1 < countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        then countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        else 1)
      h2H h2D h3H h3D h7 hsrc harr hempty2
      hn hx hfn hmoves hpeak hfit
  refine ⟨bP0, placeBoard bP0 searchBottom h2H h2D (basisPeg t.n j)
      (pegCount (basisPeg t.n j))
      (if 1 < countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        then countHeld ((builtBoard t).sudo_5Board_4held.set ⟨searchBase, hD⟩ true) 7
        else 1), ?_, hplantDo, ?_, ?_, ?_, ?_⟩
  · rw [new_board_refines t hOk, ok_bind, bind_assoc, basis_fill t.n j hj, ok_bind,
      ← searchBase_int, hput, ok_bind]
    simpa [bP0, show Ecbs.bottom = ((searchBottom : Nat) : Int) from searchBottom_int,
      show Ecbs.base_across = ((searchBase : Nat) : Int) from searchBase_int] using hcopy
  · rw [place_home_eq bP0 searchBottom h2H h2D (basisPeg t.n j) _ _]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h2H)]
    simp [Array.getElem_set]
  · rw [place_held_eq bP0 searchBottom h2H h2D (basisPeg t.n j) _ _]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h2D)]
    simp [Array.getElem_set]
  · rw [place_home_eq bP0 searchBottom h2H h2D (basisPeg t.n j) _ _]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, h2H⟩ _ (by decide : searchBottom ≠ searchBase)]
    rw [Array.getElem?_eq_getElem h3H, harr]
  · rw [place_held_eq bP0 searchBottom h2H h2D (basisPeg t.n j) _ _]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, h2D⟩ true (by decide : searchBottom ≠ searchBase)]
    rw [Array.getElem?_eq_getElem h3D]
    exact congrArg some hsrc

end EcbsLink2.Link2
