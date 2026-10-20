/-
  The search plants `basisPeg` in the base-across home before `curve_side`.
  On a fresh board that is `new_board`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchLoop
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.InvertTie
import EcbsLink2.Link2.InvertStep
import EcbsLink2.Link2.WalkCopy

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

end EcbsLink2.Link2
