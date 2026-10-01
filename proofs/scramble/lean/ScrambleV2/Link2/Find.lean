/-
  LINK 2. Emitted early-return search loops (`cubie_at`, `center_dir`): a loop over an
  index that continues until the first hit and returns there. Proof-only.
-/
import ScrambleV2.Link2.Loop

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-- An index loop that continues on every `i < j` and returns `r` at `j` ends in
    `onRet r`. -/
theorem find_idx {ρ β : Type}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (toN j : Nat) (hj : j ≤ toN) (r : ρ)
    (hmiss : ∀ i, i < j → step (Int.ofNat i) = .ok (.cont (Int.ofNat (i + 1))))
    (hhit : step (Int.ofNat j) = .ok (.ret r)) :
    ∀ n fromN, fromN + n = j →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = onRet r := by
  intro n
  induction n with
  | zero =>
    intro fromN h
    rw [Nat.add_zero] at h
    subst h
    rw [fuelRange_le hj, runLoopOn_succ, hhit]
  | succ n ih =>
    intro fromN h
    have hlt : fromN < j := by omega
    have hfuel : fuelRange (Int.ofNat fromN) (Int.ofNat toN) =
        fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) + 1 := by
      rw [fuelRange_le (by omega), fuelRange_le (by omega)]; omega
    rw [hfuel, runLoopOn_succ, hmiss fromN hlt]
    exact ih (fromN + 1) (by omega)

end ScrambleV2.Link2
