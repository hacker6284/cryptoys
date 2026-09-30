/-
  LINK 2. Emitted ascending `for` loops: the tail after a body that continued, and a
  driver that carries a predicate instead of an exact state (the Scramble state's
  trace is not modelled). Proof-only; builds on `MegaDreifach.Link2.Loop`.

  Temporary duplicates: `asc_tail` and `asc_tail_idx` also live in
  `DoubleDealCbcHmac.Link2.Loop`, which this package cannot import (that module imports
  `MegaDreifach.Link2.Helpers`, which needs the emitted Megadreifach module Scramble's
  Generated/ lacks). Draft PR #144 moves them to one home in `MegaDreifach.Link2.Loop`,
  next to `chain_loop`. #144 is not on `main` yet, so these copies stay; the next merge
  of `main` after #144 lands deletes them and uses `MegaDreifach.Link2`'s (otherwise the
  names are ambiguous under `open MegaDreifach.Link2`).
-/
import ScrambleV2.Link2.Embed

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem bind_ok_right' {ε α} (m : Except ε α) : (m >>= fun r => Except.ok r) = m := by
  cases m <;> rfl

theorem bind_pure_right {α} (m : Except SudoRt.Trap α) : (m >>= fun r => pure r) = m := by
  cases m <;> rfl

/-- The emitted loop tail after the body continued with `s`: break on the last index,
    else step the index. -/
theorem asc_tail {S ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i + 1), s)) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [addI_ofNat_one i hfit]
    rfl

/-- The same tail for a loop whose state is the index alone. -/
theorem asc_tail_idx {ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i)) : Except SudoRt.Trap (SudoRt.Flow Int ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont i')) =
      if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1))) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [addI_ofNat_one i hfit]
    rfl

private theorem chain_inv_fromEnd {α ρ β : Type}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (P : Nat → α → Prop) (toN delta : Nat)
    (hstep : ∀ i s, toN - delta ≤ i → i ≤ toN → P i s → ∃ s', P (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (Q : Except SudoRt.Trap β → Prop)
    (hafter : ∀ s, P (toN + 1) s → Q (after (Int.ofNat toN, s)))
    (hdelta : delta ≤ toN) (s0 : α) (h0 : P (toN - delta) s0) :
    Q (SudoRt.runLoopOn (Int.ofNat (toN - delta), s0)
      (fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN)) step after onRet) := by
  induction delta generalizing s0 with
  | zero =>
    rw [Nat.sub_zero] at h0 ⊢
    rw [fuelRange_le (Nat.le_refl _), show toN - toN + 1 = 0 + 1 from by omega, runLoopOn_succ]
    obtain ⟨s', hs', hs⟩ := hstep toN s0 (by omega) (Nat.le_refl _) h0
    simp only [hs, ↓reduceIte]
    exact hafter s' hs'
  | succ delta ih =>
    have hfrom_le : toN - (delta + 1) ≤ toN := Nat.sub_le _ _
    have hne : toN - (delta + 1) ≠ toN := by omega
    have hfuel :
        fuelRange (Int.ofNat (toN - (delta + 1))) (Int.ofNat toN) =
          fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le hfrom_le, fuelRange_le (Nat.sub_le _ _)]
      omega
    rw [hfuel, runLoopOn_succ]
    obtain ⟨s', hs', hs⟩ := hstep (toN - (delta + 1)) s0 (Nat.le_refl _) hfrom_le h0
    simp only [hs, hne, ↓reduceIte]
    have hnext : (toN - (delta + 1)) + 1 = toN - delta := by omega
    rw [hnext] at hs' ⊢
    exact ih (fun i s hi1 hi2 => hstep i s (by omega) hi2)
      (Nat.le_trans (Nat.le_succ delta) hdelta) s' hs'

/-- Drive an inclusive index from `fromN` to `toN` carrying a predicate `P i` on the
    state at the start of iteration `i`. -/
theorem chain_inv {α ρ β : Type}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (P : Nat → α → Prop) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i s, fromN ≤ i → i ≤ toN → P i s → ∃ s', P (i + 1) s' ∧
      step (Int.ofNat i, s) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, s'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), s')))
    (Q : Except SudoRt.Trap β → Prop)
    (hafter : ∀ s, P (toN + 1) s → Q (after (Int.ofNat toN, s)))
    (s0 : α) (h0 : P fromN s0) :
    Q (SudoRt.runLoopOn (Int.ofNat fromN, s0)
      (fuelRange (Int.ofNat fromN) (Int.ofNat toN)) step after onRet) := by
  have hfrom : fromN = toN - (toN - fromN) := by omega
  rw [hfrom] at h0 ⊢
  exact chain_inv_fromEnd step after onRet P toN (toN - fromN)
    (fun i s hi1 hi2 => hstep i s (by omega) hi2) Q hafter (Nat.sub_le _ _) s0 h0

end ScrambleV2.Link2
