/-
  ECBS Link 2: `place` is `put`, including the home, the held flag, the move
  count and the peak. Proof-only. `place` does not clear `bench_on`.
-/
import EcbsLink2.Link2.Board

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem atL_cast {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := by
  rw [← ofNat_eq_natCast i]
  exact atL_ofNat a i h

private theorem putL_cast {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (i : Int) v = .ok (a.set ⟨i, h⟩ v) := by
  rw [← ofNat_eq_natCast i]
  exact putL_ofNat a i v h

private theorem addI_cast_ofNat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (a : Int) (Int.ofNat b) = .ok (Int.ofNat (a + b)) := by
  rw [ofNat_eq_natCast b]
  exact addI_cast a b h

private theorem decide_gt_ofNat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

/-- Pegs placed: the nonzeros of `xs`. -/
def pegCount (xs : List Nat) : Nat := (xs.filter (· ≠ 0)).length

/-- The board after `place` writes `xs` at `home` on an empty home whose moves and
    peak are the naturals `moves` and `peak`. Peak becomes the held-count of homes
    `0 .. 6` when that count is strictly larger. -/
def placeBoard (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) : Ecbs.Board :=
  let b1 : Ecbs.Board :=
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs)
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }
  let occ := countHeld b1.sudo_5Board_4held 7
  if peak < occ then
    { b1 with sudo_5Board_4cost := { b1.sudo_5Board_4cost with
      sudo_5Costs_4peak := Int.ofNat occ } }
  else
    b1

private theorem pegCount_embed (xs : List Nat) :
    nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  rfl

/-- `place` on an empty home. The length of `xs` is the tier's `n` and fits an i64,
    `moves` and `peak` are the board's current counters as naturals, and the sum of
    `moves` and the nonzero count fits an i64. Homes `0 .. 6` are present so `note_peak`
    can count them. The bench flag is left alone. -/
theorem place_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (moves peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int))
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.place b (home : Int) (embed xs) =
      .ok (placeBoard b home hH hD xs moves peak) := by
  unfold Ecbs.place Ecbs.put Ecbs.need_empty Ecbs.note_peak placeBoard
  dsimp only
  have hlen : SudoRt.listLen (embed xs) = (xs.length : Int) := by
    rw [listLen_embed, ofNat_eq_natCast]
  rw [hlen, hn, sudoAssertEq_int rfl 427, ok_bind]
  rw [atL_cast _ _ hD, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
  rw [putL_cast _ _ _ hH, ok_bind, putL_cast _ _ _ hD, ok_bind]
  have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
  rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind, hmoves,
    addI_cast_ofNat _ _ hfit, ok_bind]
  have h7' : 7 ≤
      (b.sudo_5Board_4held.set ⟨home, hD⟩ true).size := by
    rw [Array.size_set]
    exact h7
  -- The board `occupied` sees is the one with the new home, held flag and moves.
  have hocc := occupied_refines
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed xs)
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }) h7'
  rw [hocc, ok_bind, hpeak, decide_gt_ofNat]
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
  · have hcI : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = true := by
      rw [decide_eq_true_eq]; exact hlt
    rw [hcI, if_pos rfl, ok_bind, ok_bind]
    simp only [hlt, ite_true]
  · have hcI : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = false := by
      rw [decide_eq_false_iff_not]; exact hlt
    rw [hcI]
    simp only [Bool.false_eq_true, if_false, ite_false, ok_bind, hlt]

/-- `place` is `put` and then the board. -/
theorem put_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (moves peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int))
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.put b (home : Int) (embed xs) =
      .ok (placeBoard b home hH hD xs moves peak) := by
  have hp := place_refines b home xs moves peak hH hD h7 hempty hn hf hmoves hpeak hfit
  unfold Ecbs.place at hp
  dsimp only at hp
  rw [except_bind_pure] at hp
  exact hp

end EcbsLink2.Link2
