/-
  The two base puts that `walk_key` starts with. `new_board` then those puts
  is `baseBoard`, with the move and peak counters named. This file does not
  tie `walk_key`: the restatement that pasted `walk_chord` or `walk_fform`
  back onto the export was not a refinement.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem peg_fit (t : Spec.Tier) (hOk : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) : FitsLen (pegCount xs) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (by omega)
  exact FitsLen.of_le hfn (by rw [← hx]; exact pegCount_le xs)

private theorem peg_sum_fit (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    FitsLen (pegCount x + pegCount y) := by
  have hfn : FitsLen (2 * t.n) := FitsLen.of_le (fits_of hOk.fits_n) (by omega)
  exact FitsLen.of_le hfn (by
    have hxP := pegCount_le x
    have hyP := pegCount_le y
    rw [hx] at hxP
    rw [hy] at hyP
    omega)

private theorem built_n (t : Spec.Tier) (xs : List Nat) (hx : xs.length = t.n) :
    (builtBoard t).sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int) := by
  rw [built_tier_eq, hx]
  rfl

private theorem built_held3 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held[3]'(heldIx t 3 (by decide)) = false := by
  simp [built_held_arr, Array.getElem_mkArray]

private theorem key_put_across (t : Spec.Tier) (hOk : BoardOk t) (x : List Nat)
    (hx : x.length = t.n) :
    put (builtBoard t) base_across (embed x) = .ok (putAcross t x) := by
  have hput := put_refines (builtBoard t) 3 x 0 1
    (homeIx t 3 (by decide)) (heldIx t 3 (by decide))
    (by rw [built_szD]; decide) (built_held3 t)
    (built_n t x hx) (by rw [hx]; exact FitsLen.of_le (fits_of hOk.fits_n) (by omega))
    (built_moves0 t) (built_peak1 t) (by simpa using peg_fit t hOk x hx)
  unfold base_across
  erw [hput]
  rw [putAcross_place]

private theorem key_put_up (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    put (putAcross t x) base_up (embed y) = .ok (baseBoard t x y) := by
  have hmv : (putAcross t x).sudo_5Board_4cost.sudo_5Costs_5moves =
      (pegCount x : Int) := by
    simp [putAcross, ofNat_eq_natCast]
  have hpk : (putAcross t x).sudo_5Board_4cost.sudo_5Costs_4peak = (1 : Int) := by
    simp [putAcross, built_peak1]
  have hempty : (putAcross t x).sudo_5Board_4held[4]'(putAcross_held4 t x) = false := by
    simp [putAcross, Array.getElem_set, built_held_arr, Array.getElem_mkArray]
  have hlen : (putAcross t x).sudo_5Board_1t.sudo_4Tier_1n = (y.length : Int) := by
    simp [putAcross, built_n t y hy]
  have hput := put_refines (putAcross t x) 4 y (pegCount x) 1
    (putAcross_home4 t x) (putAcross_held4 t x)
    (by rw [putAcross_szD]; decide) hempty hlen
    (by rw [hy]; exact FitsLen.of_le (fits_of hOk.fits_n) (by omega))
    hmv hpk (peg_sum_fit t hOk x y hx hy)
  unfold base_up
  erw [hput]
  rw [base_place]

/-- `new_board`, then the base across and the base up. Moves are the two
    nonzero counts and the peak is 2. -/
theorem key_seated (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    (do
        let b ← new_board (embTier t)
        let b ← put b base_across (embed x)
        put b base_up (embed y)) = .ok (baseBoard t x y) ∧
      (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (pegCount x + pegCount y) ∧
      (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_4peak = 2 ∧
      (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_6slides = 0 ∧
      (baseBoard t x y).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [new_board_refines t hOk, ok_bind, key_put_across t hOk x hx, ok_bind,
      key_put_up t hOk x y hx hy]
  · simp [baseBoard, putAcross]
  · simp [baseBoard]
  · simp [baseBoard, putAcross, builtBoard, midBoard, placed, blankOf]
  · simp [baseBoard, putAcross, built_ctrl_eq]

end EcbsLink2.Link2
