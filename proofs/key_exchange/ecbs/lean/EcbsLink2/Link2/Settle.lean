/-
  `settle` slides a finished bench home: every hole from `n` up is empty, the prefix
  is written, moves and slides grow by twice the nonzero count, then `note_peak`.
  `value` of that home is the prefix. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem idx_goal {ρ β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i) =
        if i = toN then .ok (.brk (Int.ofNat i))
        else .ok (.cont (Int.ofNat (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hpost : after (Int.ofNat toN) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) (Nat.le_refl _), if_pos rfl]
    exact hpost
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    have hle' : fromN + 1 ≤ toN := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hle hne)
    rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, if_neg hne]
    dsimp
    exact ih (fromN + 1) hle'
      (fun i h1 h2 => hstep i (Nat.le_trans (Nat.le_succ fromN) h1) h2)
      (by omega)

/-- The tail check in `Ecbs.settle`: hole `i` of the bench is `0`. -/
def benchZeroStep (bench : Array Int) (toV : Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board) :=
  if i > toV then
    pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
  else do
    let lift ← (do
      let c ← SudoRt.atL bench i
      let _ ← SudoRt.sudoAssertEq c (0 : Int) 414
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ()))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
    | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
    | .cont _ =>
      if (i == toV) = true then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) i)
      else do
        let i' ← SudoRt.addI i 1
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) i')

private theorem benchZero_at (xs : List Nat) (toN i : Nat)
    (hi : i < xs.length) (hz : xs[i] = 0) (hle : i ≤ toN) (hfit : FitsLen (i + 1)) :
    benchZeroStep (embed xs) (Int.ofNat toN) (Int.ofNat i) =
      if i = toN then .ok (.brk (Int.ofNat i))
      else .ok (.cont (Int.ofNat (i + 1))) := by
  unfold benchZeroStep
  dsimp only
  have hng : ¬ Int.ofNat i > Int.ofNat toN := by
    rw [GT.gt, ofNat_lt_iff]
    exact Nat.not_lt.mpr hle
  rw [if_neg hng, atL_embed xs i hi, ok_bind]
  rw [hz, show Int.ofNat 0 = (0 : Int) from rfl, sudoAssertEq_int rfl 414, ok_bind, pure_eq_ok]
  exact asc_tail_idx (ρ := Ecbs.Board) toN i hfit

private theorem benchZero_loop {β} (xs : List Nat) (n : Nat)
    (k : Except SudoRt.Trap β) (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : n < xs.length) (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hfit : FitsLen xs.length) :
    SudoRt.runLoopOn (Int.ofNat n)
      (fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)))
      (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
      (fun _ => k) onRet = k := by
  have hle : n ≤ xs.length - 1 := by omega
  refine idx_goal (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
    (fun _ => k) onRet n (xs.length - 1) hle ?_ k rfl
  intro i hlo hi
  have hix : i < xs.length := by omega
  exact benchZero_at xs (xs.length - 1) i hix (hzero i hlo hix) hi
    (FitsLen.of_le hfit (by omega))

private theorem benchZero_skip {β} (xs : List Nat) (n : Nat)
    (k : Except SudoRt.Trap β) (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : n = xs.length) (hpos : 0 < xs.length) :
    SudoRt.runLoopOn (Int.ofNat n)
      (fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)))
      (benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)))
      (fun _ => k) onRet = k := by
  have hgt : Int.ofNat n > Int.ofNat (xs.length - 1) := by
    rw [hn]
    exact (ofNat_lt_iff (xs.length - 1) xs.length).mpr (Nat.sub_lt hpos (by decide))
  rw [fuelRange_gt hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  have hstep : benchZeroStep (embed xs) (Int.ofNat (xs.length - 1)) (Int.ofNat n) =
      .ok (.brk (Int.ofNat n)) := by
    unfold benchZeroStep
    dsimp only
    rw [if_pos hgt, pure_eq_ok]
  rw [hstep]

private theorem atL_cast {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := by
  rw [← ofNat_eq_natCast i]
  exact atL_ofNat a i h

private theorem putL_cast {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (i : Int) v = .ok (a.set ⟨i, h⟩ v) := by
  rw [← ofNat_eq_natCast i]
  exact putL_ofNat a i v h

private theorem peg_embed (xs : List Nat) :
    nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  unfold pegCount
  rfl

private theorem decide_gt_ofNat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

private theorem addI_nat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (a + b)) :=
  addI_ofNat a b h

/-- The board after a bench that is on, aimed at `home`, is slid home.
    `xs` is the bench. Holes `n ..` are empty, so the tail assert passes.
    Peak becomes the held-count of homes `0 .. 6` when that count is strictly larger. -/
def settleBoard (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) : Ecbs.Board :=
  let pegs := pegCount (xs.take n)
  if peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7 then
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
      sudo_5Board_8bench_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
        sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs)
        sudo_5Costs_4peak := Int.ofNat (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) } }
  else
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
      sudo_5Board_8bench_on := false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegs)
        sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegs) } }

theorem settle_off (b : Ecbs.Board) (hoff : b.sudo_5Board_8bench_on = false) :
    Ecbs.settle b = .ok b := by
  unfold Ecbs.settle
  simp [hoff, Bool.not_false, pure_eq_ok]

theorem settle_refines (b : Ecbs.Board) (home : Nat) (xs : List Nat)
    (n moves slides peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < xs.length) (hnle : n ≤ xs.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (xs.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (xs.take n))) :
    Ecbs.settle b = .ok (settleBoard b home hH hD xs n moves slides peak) := by
  unfold Ecbs.settle
  dsimp only
  simp only [hon, Bool.not_true, Bool.false_eq_true, if_false]
  rw [hbench, listLen_embed, subI_ofNat_one xs.length hpos hfitL, ok_bind, hn]
  rw [show (n : Int) = Int.ofNat n by rw [ofNat_eq_natCast]]
  by_cases hlt : n < xs.length
  · have hfuel :
        (if Int.ofNat n > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat n).natAbs + 1) =
        fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel]
    conv =>
      lhs
      arg 1
      arg 3
      change benchZeroStep (embed xs) (Int.ofNat (xs.length - 1))
    rw [benchZero_loop xs n _ (fun r => pure r) hlt hzero hfitL]
    rw [except_bind_pure]
    unfold Ecbs.need_empty
    rw [hto, atL_cast _ home hD, hempty]
    simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
    rw [prefix_refines xs n hnle hf, ok_bind]
    have hfs : FitsLen (embed (xs.take n)).size := by
      rw [size_embed, List.length_take, Nat.min_eq_left hnle]
      exact hf
    rw [npeg_refines (embed (xs.take n)) hfs, peg_embed, ok_bind]
    rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 _ hpeg, ok_bind]
    rw [hmoves, addI_nat moves _ hfitM, ok_bind, hslides, addI_nat slides _ hfitS, ok_bind]
    rw [putL_cast _ home _ hH, ok_bind, putL_cast _ home true hD, ok_bind]
    unfold Ecbs.note_peak settleBoard
    have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨home, hD⟩ true).size := by
      rw [Array.size_set]; exact h7
    have hocc := occupied_refines
      ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_8bench_to := (home : Int)
          sudo_5Board_5bench := embed xs
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } }) h7'
    rw [hocc, ok_bind, hpeak]
    simp only [GT.gt, ofNat_lt_iff]
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = true := by
        rw [decide_eq_true_eq]; exact hpk
      rw [hc, if_pos rfl, pure_eq_ok, ← hto, ← hbench]
      simp [hpk]
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = false := by
        rw [decide_eq_false_iff_not]; exact hpk
      rw [hc]
      simp only [Bool.false_eq_true, if_false]
      rw [pure_eq_ok, ← hto, ← hbench, ← hpeak]
      simp [hpk]
  · have heq : n = xs.length := Nat.le_antisymm hnle (Nat.le_of_not_lt hlt)
    have hfuel :
        (if Int.ofNat n > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat n).natAbs + 1) =
        fuelRange (Int.ofNat n) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel]
    conv =>
      lhs
      arg 1
      arg 3
      change benchZeroStep (embed xs) (Int.ofNat (xs.length - 1))
    rw [benchZero_skip xs n _ (fun r => pure r) heq hpos]
    rw [except_bind_pure]
    unfold Ecbs.need_empty
    rw [hto, atL_cast _ home hD, hempty]
    simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
    rw [prefix_refines xs n hnle hf, ok_bind]
    have hfs : FitsLen (embed (xs.take n)).size := by
      rw [size_embed, List.length_take, Nat.min_eq_left hnle]
      exact hf
    rw [npeg_refines (embed (xs.take n)) hfs, peg_embed, ok_bind]
    rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 _ hpeg, ok_bind]
    rw [hmoves, addI_nat moves _ hfitM, ok_bind, hslides, addI_nat slides _ hfitS, ok_bind]
    rw [putL_cast _ home _ hH, ok_bind, putL_cast _ home true hD, ok_bind]
    unfold Ecbs.note_peak settleBoard
    have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨home, hD⟩ true).size := by
      rw [Array.size_set]; exact h7
    have hocc := occupied_refines
      ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ true
          sudo_5Board_8bench_on := false
          sudo_5Board_8bench_to := (home : Int)
          sudo_5Board_5bench := embed xs
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
            sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } }) h7'
    rw [hocc, ok_bind, hpeak]
    simp only [GT.gt, ofNat_lt_iff]
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = true := by
        rw [decide_eq_true_eq]; exact hpk
      rw [hc, if_pos rfl, pure_eq_ok, ← hto, ← hbench]
      simp [hpk]
    · have hc : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7) = false := by
        rw [decide_eq_false_iff_not]; exact hpk
      rw [hc]
      simp only [Bool.false_eq_true, if_false]
      rw [pure_eq_ok, ← hto, ← hbench, ← hpeak]
      simp [hpk]

end EcbsLink2.Link2
