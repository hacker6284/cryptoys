/-
  Room for a live suffix of `walk_chord`. One cell spends `walkCharge` moves
  and one control charge. `chord_add_live_frame` asks for a further cell because
  `fitRoom` and `fitCtrl` look past the cell just run. That further cell is the
  next index of this suffix, not a spare hypothesis. The last index has
  `cellsLeft = 1` and uses `chord_add_live`, which asks for one charge.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordNext

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves one live chord can spend, including the rise's two homes.
    `cellMoveCharge` covers the copy, the climb, and the tail. The rise's
    pegs sit outside that envelope, at most `2 · n`. -/
def walkCharge (t : Spec.Tier) : Nat :=
  cellMoveCharge t + 2 * t.n

/-- Cells still to run, including `i`, when the loop ends at `toN`. -/
def cellsLeft (i toN : Nat) : Nat :=
  toN - i + 1

theorem walkCharge_split (t : Spec.Tier) :
    cellMoveCharge t + 2 * t.n = walkCharge t := rfl

theorem cellMove_le_walk (t : Spec.Tier) : cellMoveCharge t ≤ walkCharge t := by
  unfold walkCharge
  omega

private theorem rem_mul (rem c : Nat) (h : 0 < rem) :
    rem * c = (rem - 1) * c + c := by
  have hsucc : rem - 1 + 1 = rem := Nat.sub_add_cancel h
  calc rem * c = (rem - 1 + 1) * c := by rw [hsucc]
    _ = (rem - 1) * c + c := by rw [Nat.succ_mul]

private theorem fuel_mul (rem c : Nat) (h : 2 ≤ rem) :
    (rem - 1 + 1) * c = rem * c := by
  have hsucc : rem - 1 + 1 = rem := by omega
  rw [hsucc]

/-- The chord's move check, out of one `walkCharge`. -/
theorem live_move_of_walk (t : Spec.Tier) (moves : Nat) (baseX accX : List Nat)
    (hx : baseX.length = t.n) (hy : accX.length = t.n)
    (h : FitsLen (moves + walkCharge t)) :
    FitsLen (liveMoveRoom t moves baseX accX) := by
  apply FitsLen.of_le h
  have hlive := live_move_le t moves baseX accX hx hy
  unfold walkCharge
  omega

theorem live_slide_of_cell (t : Spec.Tier) (slides : Nat)
    (h : FitsLen (slides + cellSlideCharge t)) :
    FitsLen (liveSlideRoom t slides) := by
  rw [live_slide_eq]
  exact h

theorem live_ctrl_of_cell (t : Spec.Tier) (ctrl : Nat)
    (h : FitsLen (ctrl + cellCtrlCharge t)) :
    FitsLen (liveCtrlRoom t ctrl) := by
  rw [live_ctrl_eq]
  exact h

theorem live_ops_of_cell (t : Spec.Tier) (ops : Nat)
    (h : FitsLen (ops + cellOpsCharge t)) :
    FitsLen (liveOpsRoom t ops) := by
  rw [live_ops_eq]
  exact h

/-- One charge out of an envelope of `rem` charges. -/
theorem charge_of_rem (a rem c : Nat) (hrem : 0 < rem)
    (h : FitsLen (a + rem * c)) : FitsLen (a + c) := by
  apply FitsLen.of_le h
  have hsplit := rem_mul rem c hrem
  omega

/-- A non-final cell. `fuel = rem - 1` is the cells after this one, so the
    frame's `(fuel + 1)` charges are exactly `rem`. -/
theorem frame_fuel_move (t : Spec.Tier) (moves rem : Nat) (hrem : 2 ≤ rem)
    (h : FitsLen (moves + rem * walkCharge t)) :
    1 ≤ rem - 1 ∧ FitsLen (moves + ((rem - 1) + 1) * cellMoveCharge t) := by
  refine ⟨by omega, ?_⟩
  apply FitsLen.of_le h
  have hmul : ((rem - 1) + 1) * cellMoveCharge t = rem * cellMoveCharge t :=
    fuel_mul rem _ hrem
  have hle : cellMoveCharge t ≤ walkCharge t := cellMove_le_walk t
  have hprod : rem * cellMoveCharge t ≤ rem * walkCharge t :=
    Nat.mul_le_mul_left rem hle
  omega

theorem frame_fuel_ctrl (ctrl rem : Nat) (c : Nat) (hrem : 2 ≤ rem)
    (h : FitsLen (ctrl + rem * c)) :
    1 ≤ rem - 1 ∧ FitsLen (ctrl + ((rem - 1) + 1) * c) := by
  refine ⟨by omega, ?_⟩
  apply FitsLen.of_le h
  have hmul : ((rem - 1) + 1) * c = rem * c := fuel_mul rem c hrem
  omega

/-- After this cell the remaining `rem - 1` charges still fit. -/
theorem move_room_succ (t : Spec.Tier) (moves moves' rem : Nat) (hrem : 0 < rem)
    (hm : moves' ≤ moves + walkCharge t)
    (h : FitsLen (moves + rem * walkCharge t)) :
    FitsLen (moves' + (rem - 1) * walkCharge t) := by
  apply FitsLen.of_le h
  have hsplit := rem_mul rem (walkCharge t) hrem
  omega

theorem ctrl_room_succ (ctrl ctrl' rem c : Nat) (hrem : 0 < rem)
    (hc : ctrl' ≤ ctrl + c)
    (h : FitsLen (ctrl + rem * c)) :
    FitsLen (ctrl' + (rem - 1) * c) := by
  apply FitsLen.of_le h
  have hsplit := rem_mul rem c hrem
  omega

theorem cellsLeft_pos (i toN : Nat) : 0 < cellsLeft i toN := by
  unfold cellsLeft
  omega

theorem cellsLeft_last (i toN : Nat) (h : i = toN) : cellsLeft i toN = 1 := by
  unfold cellsLeft
  omega

theorem cellsLeft_succ (i toN : Nat) (hi : i < toN) :
    cellsLeft (i + 1) toN = cellsLeft i toN - 1 := by
  unfold cellsLeft
  omega

/-- The frame's fuel is the cells strictly after `i`. -/
theorem fuel_of_later (i toN : Nat) (hi : i < toN) :
    1 ≤ toN - i ∧ toN - i = cellsLeft i toN - 1 := by
  unfold cellsLeft
  omega

/-- A zero counter has the same room as the product. -/
theorem walk_room_zero (k c : Nat) (h : FitsLen (k * c)) :
    FitsLen (0 + k * c) := by
  simpa using h

/-- The rise slack is inside `walkCharge`, so one cell's move bound leaves the
    rest of the suffix. -/
theorem spend_walk (t : Spec.Tier) (moves moves' : Nat)
    (hm : moves' ≤ moves + cellMoveCharge t + 2 * t.n) :
    moves' ≤ moves + walkCharge t := by
  unfold walkCharge
  omega

/-- Room at every index of a suffix, if each cell spends at most one charge.
    `left k` is the cells still to run when `k` cells have already run. -/
theorem suffix_move_room (t : Spec.Tier) (moves0 rem : Nat)
    (spend : Nat → Nat) (h0 : spend 0 = moves0)
    (hstep : ∀ k, k < rem → spend (k + 1) ≤ spend k + walkCharge t)
    (h : FitsLen (moves0 + rem * walkCharge t)) :
    ∀ k, k ≤ rem → FitsLen (spend k + (rem - k) * walkCharge t) := by
  intro k hk
  induction k with
  | zero =>
    simpa [h0] using h
  | succ k ih =>
    have hlt : k < rem := by omega
    have ih' := ih (Nat.le_of_lt hlt)
    have hnext := move_room_succ t (spend k) (spend (k + 1)) (rem - k)
      (by omega) (hstep k hlt) ih'
    have hsub : (rem - k) - 1 = rem - (k + 1) := by omega
    simpa [hsub] using hnext

/-- Same induction for the control counter. One cell spends one `cellCtrlCharge`. -/
theorem suffix_ctrl_room (ctrl0 rem c : Nat)
    (spend : Nat → Nat) (h0 : spend 0 = ctrl0)
    (hstep : ∀ k, k < rem → spend (k + 1) ≤ spend k + c)
    (h : FitsLen (ctrl0 + rem * c)) :
    ∀ k, k ≤ rem → FitsLen (spend k + (rem - k) * c) := by
  intro k hk
  induction k with
  | zero =>
    simpa [h0] using h
  | succ k ih =>
    have hlt : k < rem := by omega
    have ih' := ih (Nat.le_of_lt hlt)
    have hnext := ctrl_room_succ (spend k) (spend (k + 1)) (rem - k) c
      (by omega) (hstep k hlt) ih'
    have hsub : (rem - k) - 1 = rem - (k + 1) := by omega
    simpa [hsub] using hnext

end EcbsLink2.Link2
