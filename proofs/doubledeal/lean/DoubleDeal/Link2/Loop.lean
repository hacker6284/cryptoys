/-
  LINK 2. Inclusive `for` loops as emitted by the Lean backend
  (`runLoopOn` + break on the last index). Proof-only.
-/
import Doubledeal
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo

namespace DoubleDeal.Link2

/-- Emitter inclusive-loop stepper, once the body has been reduced to
    `Flow.cont` of the next state (no early `ret` / `brk`). -/
def inclAfter {α ρ} (toV i : Int) (st' : α) :
    Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ) :=
  if i == toV then
    .ok (SudoRt.Flow.brk (i, st'))
  else
    SudoRt.addI i (1 : Int) >>= fun i' => .ok (SudoRt.Flow.cont (i', st'))

theorem inclAfter_last {α ρ} (toN : Nat) (st' : α) :
    inclAfter (ρ := ρ) (Int.ofNat toN) (Int.ofNat toN) st' =
      .ok (SudoRt.Flow.brk (Int.ofNat toN, st')) := by
  unfold inclAfter
  simp [beq_int_iff]

theorem inclAfter_step {α ρ} (toN i : Nat) (st' : α)
    (hne : i ≠ toN) (hfits : FitsLen (i + 1)) :
    inclAfter (ρ := ρ) (Int.ofNat toN) (Int.ofNat i) st' =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st')) := by
  unfold inclAfter
  have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => hne (Int.ofNat.inj h)
  rw [ite_int_beq, if_neg hneI, addI_ofNat_one i hfits, ok_bind]

/-- Inclusive loop whose start index is `toN - delta`. -/
private theorem chain_loop_fromEnd {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (toN delta : Nat)
    (hstep : ∀ i, toN - delta ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN, f (toN + 1)) = goal)
    (hdelta : delta ≤ toN) :
    SudoRt.runLoopOn (Int.ofNat (toN - delta), f (toN - delta))
      (fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN))
      step after onRet = goal := by
  induction delta with
  | zero =>
    rw [Nat.sub_zero, fuelRange_le (Nat.le_refl _),
      show toN - toN + 1 = 0 + 1 from by omega, runLoopOn_succ]
    have hs := hstep toN (by omega) (Nat.le_refl _)
    simp only [hs, ↓reduceIte]
    exact hafter
  | succ delta ih =>
    have hfrom_le : toN - (delta + 1) ≤ toN := Nat.sub_le _ _
    have hne : toN - (delta + 1) ≠ toN := by omega
    have hfuel :
        fuelRange (Int.ofNat (toN - (delta + 1))) (Int.ofNat toN) =
          fuelRange (Int.ofNat (toN - delta)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le hfrom_le, fuelRange_le (Nat.sub_le _ _)]
      omega
    rw [hfuel, runLoopOn_succ]
    have hs := hstep (toN - (delta + 1)) (Nat.le_refl _) hfrom_le
    simp only [hs, hne, ↓reduceIte]
    have hnext : (toN - (delta + 1)) + 1 = toN - delta := by omega
    simp only [hnext]
    have hstep' : ∀ i, toN - delta ≤ i → i ≤ toN →
        step (Int.ofNat i, f i) =
          if i = toN then
            .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
          else
            .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))) :=
      fun i hi1 hi2 => hstep i (by omega) hi2
    exact ih hstep' (Nat.le_trans (Nat.le_succ delta) hdelta)

/-- Drive an inclusive index from `fromN` to `toN`. `f i` is the state at
    the start of iteration `i`; the body stores `f (i+1)`. The loop joins
    with `after` on the break state `(toN, f (toN+1))`. -/
theorem chain_loop {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (fromN toN : Nat)
    (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN, f (toN + 1)) = goal) :
    SudoRt.runLoopOn (Int.ofNat fromN, f fromN)
      (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  have hfrom : fromN = toN - (toN - fromN) := by omega
  rw [hfrom]
  have hdelta_le : toN - fromN ≤ toN := Nat.sub_le _ _
  have hstep0 : ∀ i, toN - (toN - fromN) ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))) := by
    intro i hi1 hi2
    exact hstep i (by omega) hi2
  exact chain_loop_fromEnd step after onRet f toN (toN - fromN) hstep0 goal hafter hdelta_le

/-- Same chain, joining by returning the final state. -/
theorem chain_loop_state {α ρ}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (onRet : ρ → Except SudoRt.Trap α)
    (f : Nat → α) (fromN toN : Nat)
    (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then
          .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1)))) :
    SudoRt.runLoopOn (Int.ofNat fromN, f fromN)
      (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step (fun σ => .ok σ.2) onRet =
      .ok (f (toN + 1)) :=
  chain_loop step (fun σ => .ok σ.2) onRet f fromN toN hle hstep
    (.ok (f (toN + 1))) rfl

end DoubleDeal.Link2
