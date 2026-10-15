/-
  ECBS Link 2: `band` and `occupied`. Proof-only.

  `band` is `value`: the bench array when this home is the aimed bench and is not held,
  otherwise the home array, then the first `n` entries. A home that is neither held nor
  the aimed bench traps with `AssertFailed` (`where_bench`). An index past the array is
  `OutOfBounds` and is not claimed here.

  `occupied` counts held homes `0 .. 6`. Home `7` is a real slot (`home_count` is 8) and
  is not part of that count; `note_peak` uses only this count.
-/
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Held flags among the first `i` homes, index 0 first. `getD` past the array is empty. -/
def countHeld (held : Array Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => countHeld held i + if held.getD i false then 1 else 0

private theorem countHeld_zero (held : Array Bool) : countHeld held 0 = 0 := by
  conv =>
    lhs
    unfold countHeld

private theorem countHeld_succ (held : Array Bool) (i : Nat) :
    countHeld held (i + 1) = countHeld held i + if held.getD i false then 1 else 0 := by
  conv =>
    lhs
    unfold countHeld

private theorem countHeld_le (held : Array Bool) (i : Nat) : countHeld held i ≤ i := by
  induction i with
  | zero => simp [countHeld_zero]
  | succ i ih =>
    rw [countHeld_succ]
    have : (if held.getD i false then 1 else 0) ≤ 1 := by split <;> decide
    omega

private theorem getD_bool (held : Array Bool) (i : Nat) (h : i < held.size) :
    held.getD i false = held[i] := by
  simp [Array.getD_eq_get?, Array.getElem?_eq_getElem h, Option.getD_some]

private theorem atL_cast {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := by
  rw [← ofNat_eq_natCast i]
  exact atL_ofNat a i h

private theorem subI_band :
    SudoRt.subI Ecbs.band_homes (1 : Int) = .ok (Int.ofNat 6) := by
  unfold Ecbs.band_homes
  exact subI_ofNat_one 7 (by decide) (fits_small (by decide))

private theorem prefix_cast (xs : List Nat) (m : Nat) (hm : m ≤ xs.length) (hf : FitsLen m) :
    Ecbs.prefix (embed xs) (m : Int) = .ok (embed (xs.take m)) := by
  rw [← ofNat_eq_natCast m]
  exact prefix_refines xs m hm hf

/-- Homes `0 .. 6`. Requires the held array to cover those seven slots. -/
theorem occupied_refines (b : Ecbs.Board) (h7 : 7 ≤ b.sudo_5Board_4held.size) :
    Ecbs.occupied b = .ok (Int.ofNat (countHeld b.sudo_5Board_4held 7)) := by
  unfold Ecbs.occupied
  rw [subI_band, ok_bind, except_bind_pure]
  dsimp
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat 6) = 7 := by
    rw [fuelRange_le (Nat.zero_le _)]
  conv =>
    lhs
    arg 2
    rw [← hfuel]
  refine asc_goal (fromN := 0) (toN := 6)
    (fun i (c : Int) => c = Int.ofNat (countHeld b.sudo_5Board_4held i))
    (Nat.zero_le _)
    (by
      change (0 : Int) = Int.ofNat (countHeld b.sudo_5Board_4held 0)
      rw [countHeld_zero]
      rfl) ?_ ?_
  · intro i c _ hi hc
    have hix : i < b.sudo_5Board_4held.size := by omega
    have hfi : FitsLen (i + 1) := fits_small (by omega)
    have hcle := countHeld_le b.sudo_5Board_4held i
    have hfitc : FitsLen (countHeld b.sudo_5Board_4held i + 1) := fits_small (by omega)
    refine ⟨Int.ofNat (countHeld b.sudo_5Board_4held (i + 1)), rfl, ?_⟩
    dsimp only
    split
    · next hgt => exact absurd hgt (not_gt_cast hi)
    · rw [atL_ofNat b.sudo_5Board_4held i hix, ok_bind, hc, countHeld_succ, getD_bool _ _ hix]
      by_cases hb : b.sudo_5Board_4held[i] = true
      · simp only [hb, ite_true, if_true, pure_eq_ok, ok_bind]
        rw [addI_ofNat_one _ hfitc]
        exact asc_tail 6 i hfi _
      · have hbf : b.sudo_5Board_4held[i] = false := eq_false_of_ne_true hb
        simp only [hbf, ite_false, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind, Nat.add_zero]
        exact asc_tail 6 i hfi _
  · intro c hc
    simp [pure_eq_ok, hc, Prod.snd]

private theorem beq_home (b : Ecbs.Board) (home : Nat)
    (h : b.sudo_5Board_8bench_to = (home : Int)) :
    SudoRt.SEq.beq b.sudo_5Board_8bench_to (home : Int) = true := by
  rw [sEq_int, h]
  exact decide_eq_true rfl

private theorem beq_home_ne (b : Ecbs.Board) (home : Nat)
    (h : b.sudo_5Board_8bench_to ≠ (home : Int)) :
    SudoRt.SEq.beq b.sudo_5Board_8bench_to (home : Int) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  exact h

/-- A held home reads that home's array, then the first `n` entries. -/
theorem band_held_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hheldSz : home < b.sudo_5Board_4held.size)
    (hhomeSz : home < b.sudo_5Board_4home.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length) (hf : FitsLen n) :
    Ecbs.band b (home : Int) = .ok (embed (xs.take n)) := by
  unfold Ecbs.band Ecbs.value Ecbs.get_number Ecbs.where_bench
  rw [atL_cast _ _ hheldSz, hheld]
  simp only [ok_bind, ite_true, pure_eq_ok, Bool.false_eq_true, ite_false]
  rw [atL_cast _ _ hhomeSz, harr]
  simp only [ok_bind]
  rw [hn, prefix_cast xs n hlen hf, ok_bind, ok_bind]

/-- An empty home aimed at by the bench reads the bench array, then the first `n` entries.
    `place` does not clear `bench_on`, so a later `band` of that home still reads the bench
    until something else settles it. -/
theorem band_bench_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hheldSz : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length) (hf : FitsLen n) :
    Ecbs.band b (home : Int) = .ok (embed (xs.take n)) := by
  unfold Ecbs.band Ecbs.value Ecbs.get_number Ecbs.where_bench
  rw [atL_cast _ _ hheldSz, hheld]
  simp only [ok_bind, Bool.false_eq_true, ite_false, hon]
  rw [if_true, beq_home b home hto, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind,
    pure_eq_ok, ok_bind, if_pos rfl, hbench, ok_bind, hn,
    prefix_cast xs n hlen hf, ok_bind, pure_eq_ok, ok_bind]
  rw [pure_eq_ok]

/-- `value` of an empty home the bench is aimed at: the first `n` bench entries. -/
theorem value_bench_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hheldSz : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length) (hf : FitsLen n) :
    Ecbs.value b (home : Int) = .ok (embed (xs.take n)) := by
  have hb := band_bench_refines b home xs n hheldSz hheld hon hto hbench hn hlen hf
  unfold Ecbs.band at hb
  rw [except_bind_pure] at hb
  exact hb

/-- `band` is `value` and then the array. -/
theorem value_held_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hheldSz : home < b.sudo_5Board_4held.size)
    (hhomeSz : home < b.sudo_5Board_4home.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length) (hf : FitsLen n) :
    Ecbs.value b (home : Int) = .ok (embed (xs.take n)) := by
  have hb := band_held_refines b home xs n hheldSz hhomeSz hheld harr hn hlen hf
  unfold Ecbs.band at hb
  rw [except_bind_pure] at hb
  exact hb

/-- The elaborated home read: `atL` of `a.set i v` at `i` returns `v`. -/
theorem home_set_read {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (do
        let x ← SudoRt.atL (a.set ⟨i, h⟩ v) (Int.ofNat i)
        Except.ok x) =
      Except.ok v := by
  have hsz : i < (a.set ⟨i, h⟩ v).size := by rw [Array.size_set]; exact h
  rw [atL_ofNat _ i hsz]
  have hget : (a.set ⟨i, h⟩ v)[i]'hsz = v := by
    rw [Array.getElem_set]; simp
  simp [hget, ok_bind]

/-- `value` of a held home whose array was just set to the length-`n` prefix.
    `get_number` reads that home; `home_set_read` is the bind; `prefix_refines` is the rest. -/
theorem value_after_set (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n)
    (hf : FitsLen n)
    (hlen : n ≤ xs.length) :
    Ecbs.value
        { b with sudo_5Board_4home :=
            b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n)) }
        (home : Int) =
      .ok (embed (xs.take n)) := by
  unfold Ecbs.value Ecbs.get_number Ecbs.where_bench
  rw [show (home : Int) = Int.ofNat home from ofNat_eq_natCast home,
    atL_ofNat _ home hD, hheld]
  simp only [ok_bind, ite_true, pure_eq_ok, Bool.false_eq_true, if_false]
  rw [home_set_read, ok_bind, hn,
    prefix_refines (xs.take n) n (by rw [List.length_take]; omega) hf, ok_bind,
    List.take_take, Nat.min_self]

/-- Neither held nor the aimed bench: `where_bench` asserts, kind `AssertFailed`. -/
theorem band_traps (b : Ecbs.Board) (home : Nat)
    (hheldSz : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = false)
    (haim : ¬ (b.sudo_5Board_8bench_on = true ∧ b.sudo_5Board_8bench_to = (home : Int))) :
    ∃ e, Ecbs.band b (home : Int) = .error e ∧ e.kind = "AssertFailed" := by
  unfold Ecbs.band Ecbs.value Ecbs.get_number Ecbs.where_bench
  rw [atL_cast _ _ hheldSz, hheld]
  simp only [ok_bind, Bool.false_eq_true, ite_false]
  by_cases hon : b.sudo_5Board_8bench_on = true
  · have hne : b.sudo_5Board_8bench_to ≠ (home : Int) := by
      intro h
      exact haim ⟨hon, h⟩
    simp only [hon, ite_true, pure_eq_ok, ok_bind, beq_home_ne b home hne]
    unfold SudoRt.sudoAssert
    simp only [Bool.false_eq_true, if_false, error_bind]
    exact ⟨_, rfl, rfl⟩
  · have hoff : b.sudo_5Board_8bench_on = false := eq_false_of_ne_true hon
    simp only [hoff, ite_false, pure_eq_ok, ok_bind]
    unfold SudoRt.sudoAssert
    simp only [Bool.false_eq_true, if_false, error_bind]
    exact ⟨_, rfl, rfl⟩

end EcbsLink2.Link2
