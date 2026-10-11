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

theorem pegCount_le (xs : List Nat) : pegCount xs ≤ xs.length := by
  unfold pegCount
  induction xs with
  | nil => simp [List.filter]
  | cons x xs ih =>
    simp only [List.filter, List.length_cons]
    split
    · simp only [List.length_cons]
      omega
    · exact Nat.le_succ_of_le ih

theorem pegCount_take_le (xs : List Nat) (n : Nat) : pegCount (xs.take n) ≤ n := by
  have h1 := pegCount_le (xs.take n)
  have h2 : (xs.take n).length ≤ n := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  exact Nat.le_trans h1 h2

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

/-- `copy_band` with `mirror = false`: read the held source, write that prefix into an
    empty home, charge the nonzero count, then `note_peak`. -/
theorem copy_band_refines (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (moves peak : Nat)
    (hHd : dst < b.sudo_5Board_4home.size)
    (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : src < b.sudo_5Board_4home.size)
    (hDs : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsrc : b.sudo_5Board_4held[src] = true)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int))
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.copy_band b (dst : Int) (src : Int) false =
      .ok (placeBoard b dst hHd hDd xs moves peak) := by
  unfold Ecbs.copy_band Ecbs.need_empty Ecbs.note_peak placeBoard
  simp only [Bool.false_eq_true, if_false]
  have hv := value_held_refines b src xs xs.length hDs hHs hsrc harr hn (Nat.le_refl _) hf
  rw [hv, ok_bind]
  rw [List.take_length]
  rw [atL_cast _ _ hDd, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok, ok_bind]
  rw [putL_cast _ _ _ hHd, ok_bind, putL_cast _ _ _ hDd, ok_bind]
  have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
  rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind, hmoves,
    addI_cast_ofNat _ _ hfit, ok_bind]
  have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true).size := by
    rw [Array.size_set]; exact h7
  have hocc := occupied_refines
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨dst, hHd⟩ (embed xs)
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨dst, hDd⟩ true
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }) h7'
  rw [hocc, ok_bind, hpeak, decide_gt_ofNat]
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7
  · have hcI : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7) = true := by
      rw [decide_eq_true_eq]; exact hlt
    rw [hcI, if_pos rfl, ok_bind]
    simp only [hlt, ite_true, pure_eq_ok]
  · simp only [decide_False, Bool.false_eq_true, if_false, ok_bind, pure_eq_ok, hlt]

/-- `copy_band` with `mirror = false` when the source home is empty and the bench
    is on, aimed at that home. The written prefix is the first `n` bench entries.
    `place` does not clear `bench_on`, so the bench stays aimed at the source. -/
theorem copy_band_bench_refines (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n moves peak : Nat)
    (hHd : dst < b.sudo_5Board_4home.size)
    (hDd : dst < b.sudo_5Board_4held.size)
    (hDs : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsrc : b.sudo_5Board_4held[src] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (src : Int))
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount (xs.take n))) :
    Ecbs.copy_band b (dst : Int) (src : Int) false =
      .ok (placeBoard b dst hHd hDd (xs.take n) moves peak) := by
  unfold Ecbs.copy_band Ecbs.need_empty Ecbs.note_peak placeBoard
  simp only [Bool.false_eq_true, if_false]
  have hv := value_bench_refines b src xs n hDs hsrc hon hto hbench hn hlen hf
  rw [hv, ok_bind]
  rw [atL_cast _ _ hDd, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok, ok_bind]
  rw [putL_cast _ _ _ hHd, ok_bind, putL_cast _ _ _ hDd, ok_bind]
  have htake : (xs.take n).length = n := by rw [List.length_take, Nat.min_eq_left hlen]
  have hfs : FitsLen (embed (xs.take n)).size := by rw [size_embed, htake]; exact hf
  rw [npeg_refines (embed (xs.take n)) hfs, pegCount_embed, ok_bind, hmoves,
    addI_cast_ofNat _ _ hfit, ok_bind]
  have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true).size := by
    rw [Array.size_set]; exact h7
  have hocc := occupied_refines
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨dst, hHd⟩ (embed (xs.take n))
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨dst, hDd⟩ true
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount (xs.take n)) } }) h7'
  rw [hocc, ok_bind, hpeak, decide_gt_ofNat]
  by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7
  · have hcI : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7) = true := by
      rw [decide_eq_true_eq]; exact hlt
    rw [hcI, if_pos rfl, ok_bind]
    simp only [hlt, ite_true, pure_eq_ok]
  · simp only [decide_False, Bool.false_eq_true, if_false, ok_bind, pure_eq_ok, hlt]

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

/-- `clear` of a held home. The workbench branch is not taken, because the home is held.
    Moves grow by the nonzero count. The home array becomes empty and the flag falls. -/
theorem clear_held_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hf : FitsLen xs.length)
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.clear b (home : Int) =
      .ok { b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } } := by
  unfold Ecbs.clear
  by_cases hb : b.sudo_5Board_8bench_on = true
  · simp only [hb, if_true]
    by_cases hto : SudoRt.SEq.beq b.sudo_5Board_8bench_to (home : Int) = true
    · simp only [hto, if_true, atL_cast _ _ hD, hheld]
      simp only [Bool.not_true, if_true, pure_eq_ok, ok_bind, Bool.false_eq_true, if_false]
      simp only [sudoAssert_true, ok_bind]
      rw [atL_cast _ _ hH, harr, ok_bind]
      have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
      rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind, hmoves,
        addI_cast_ofNat _ _ hfit, ok_bind]
      rw [putL_cast _ _ _ hD, ok_bind, putL_cast _ _ _ hH]
      rfl
    · simp only [hto, if_false, pure_eq_ok, ok_bind, Bool.false_eq_true, if_false]
      rw [atL_cast _ _ hD, hheld, ok_bind, sudoAssert_true, ok_bind]
      rw [atL_cast _ _ hH, harr, ok_bind]
      have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
      rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind, hmoves,
        addI_cast_ofNat _ _ hfit, ok_bind]
      rw [putL_cast _ _ _ hD, ok_bind, putL_cast _ _ _ hH]
      rfl
  · have hbf : b.sudo_5Board_8bench_on = false := eq_false_of_ne_true hb
    simp only [hbf, if_false, pure_eq_ok, ok_bind, Bool.false_eq_true, if_false]
    rw [atL_cast _ _ hD, hheld, ok_bind, sudoAssert_true, ok_bind]
    rw [atL_cast _ _ hH, harr, ok_bind]
    have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
    rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind, hmoves,
      addI_cast_ofNat _ _ hfit, ok_bind]
    rw [putL_cast _ _ _ hD, ok_bind, putL_cast _ _ _ hH]
    rfl

end EcbsLink2.Link2
