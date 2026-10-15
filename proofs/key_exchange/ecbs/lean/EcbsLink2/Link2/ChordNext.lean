/-
  What one live cell leaves for the next one. The five rooms are one charge
  each; a fuel of further cells keeps what this cell does not spend. The
  climb's recorded high is a high-water mark: `tally_clear` does not lower it,
  so the next cell does not have `RunFrame.highLt`. `tally_start_again` is the
  restart when that mark is already at or above the tally origin.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLive
import EcbsLink2.Link2.AfterClimb

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Moves one live cell can add: three length-`n` homes, the climb, and the tail.
    A length-`n` home has at most `n` pegs. -/
def cellMoveCharge (t : Spec.Tier) : Nat :=
  3 * t.n +
    tierR t * rungCharge t.n t.benchlen (rowRoom t) +
    pegCharge t.n t.benchlen + t.n + t.n * (t.n + 1) +
    3 * (t.benchlen - t.n) + 2 * t.n + tailMoveCap t.n t.benchlen

/-- Slides one live cell can add. -/
def cellSlideCharge (t : Spec.Tier) : Nat :=
  tierR t * rungSlideCharge t.n (rowRoom t) + 2 * t.n + tailSlideCap t.n

/-- Control steps one live cell can add. -/
def cellCtrlCharge (t : Spec.Tier) : Nat :=
  1 + (tierR t + 1) * (3 * rowRoom t + 5) + 6

/-- Ops one live cell can add on the climb's slot. -/
def cellOpsCharge (t : Spec.Tier) : Nat :=
  tierR t * (rowRoom t + 3) + 3

theorem live_move_le (t : Spec.Tier) (moves : Nat) (baseX accX : List Nat)
    (hx : baseX.length = t.n) (hy : accX.length = t.n) :
    liveMoveRoom t moves baseX accX ≤ moves + cellMoveCharge t := by
  have hpb : pegCount baseX ≤ t.n := by rw [← hx]; exact pegCount_le baseX
  have hpa : pegCount accX ≤ t.n := by rw [← hy]; exact pegCount_le accX
  have hps : pegCount (fieldSub t.n baseX accX) ≤ t.n := by
    simpa [fieldSub_length] using pegCount_le (fieldSub t.n baseX accX)
  unfold liveMoveRoom cellMoveCharge runMoves
  omega

theorem live_slide_eq (t : Spec.Tier) (slides : Nat) :
    liveSlideRoom t slides = slides + cellSlideCharge t := by
  unfold liveSlideRoom cellSlideCharge
  omega

theorem live_ctrl_eq (t : Spec.Tier) (ctrl : Nat) :
    liveCtrlRoom t ctrl = ctrl + cellCtrlCharge t := by
  unfold liveCtrlRoom cellCtrlCharge
  omega

theorem live_ops_eq (t : Spec.Tier) (ops : Nat) :
    liveOpsRoom t ops = ops + cellOpsCharge t := by
  unfold liveOpsRoom cellOpsCharge
  omega

private theorem charge_left (a a' c fuel : Nat)
    (ha : a' ≤ a + c) (h : FitsLen (a + (fuel + 1) * c)) :
    FitsLen (a' + fuel * c) := by
  have hsplit : (fuel + 1) * c = fuel * c + c := by rw [Nat.succ_mul]
  apply FitsLen.of_le h
  rw [hsplit]
  omega

private theorem charge_head (a c fuel : Nat) (h : FitsLen (a + (fuel + 1) * c)) :
    FitsLen (a + c) := by
  apply FitsLen.of_le h
  have hc : c ≤ (fuel + 1) * c :=
    Nat.le_mul_of_pos_left c (Nat.succ_pos fuel)
  omega

/-- One cell spends at most one charge. `fuel` further charges remain, and the
    charge this cell needs is `FitsLen.of_le` of the same room. -/
theorem cell_rooms_left (t : Spec.Tier)
    (moves slides ctrl ops moves' slides' ctrl' ops' fuel : Nat)
    (hm : moves' ≤ moves + cellMoveCharge t)
    (hs : slides' ≤ slides + cellSlideCharge t)
    (hc : ctrl' ≤ ctrl + cellCtrlCharge t)
    (ho : ops' ≤ ops + cellOpsCharge t)
    (hM : FitsLen (moves + (fuel + 1) * cellMoveCharge t))
    (hS : FitsLen (slides + (fuel + 1) * cellSlideCharge t))
    (hC : FitsLen (ctrl + (fuel + 1) * cellCtrlCharge t))
    (hO : FitsLen (ops + (fuel + 1) * cellOpsCharge t)) :
    FitsLen (moves + cellMoveCharge t) ∧
      FitsLen (slides + cellSlideCharge t) ∧
      FitsLen (ctrl + cellCtrlCharge t) ∧
      FitsLen (ops + cellOpsCharge t) ∧
      FitsLen (moves' + fuel * cellMoveCharge t) ∧
      FitsLen (slides' + fuel * cellSlideCharge t) ∧
      FitsLen (ctrl' + fuel * cellCtrlCharge t) ∧
      FitsLen (ops' + fuel * cellOpsCharge t) :=
  ⟨charge_head moves (cellMoveCharge t) fuel hM,
    charge_head slides (cellSlideCharge t) fuel hS,
    charge_head ctrl (cellCtrlCharge t) fuel hC,
    charge_head ops (cellOpsCharge t) fuel hO,
    charge_left moves moves' (cellMoveCharge t) fuel hm hM,
    charge_left slides slides' (cellSlideCharge t) fuel hs hS,
    charge_left ctrl ctrl' (cellCtrlCharge t) fuel hc hC,
    charge_left ops ops' (cellOpsCharge t) fuel ho hO⟩

/-- The script marker walks `step` holes per cell. `fuel` later cells still
    sit before `script` after this cell takes its step. -/
theorem marker_room_left (mark script step fuel : Nat)
    (h : mark + step * (fuel + 1) < script) :
    mark + step + step * fuel < script := by
  have hsplit : step * (fuel + 1) = step * fuel + step := by rw [Nat.mul_succ]
  omega

/-- At the end of the ladder the recorded high is the last tally peg, so it
    is not below the tally origin. -/
theorem climb_high_ge
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base) (hm : 0 < s.tally) :
    s.t0 ≤ s.high ∧ ¬ s.high < s.t0 := by
  have hEq : s.high = s.t0 + s.tally - 1 := h.highTop hm
  omega

/-- The board `tally_clear` leaves still holds that high. `RunFrame.highLt`
    asks for a high strictly below the origin, and this board does not have one. -/
theorem settle_high_mark
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hon : s.onBench = true) (hge : 0 ≤ s.fromHole)
    (ht : s.tally ≤ base.mMax) (hm : 0 < s.tally) :
    ∃ bZ : Ecbs.Board,
      bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) ∧
      s.t0 ≤ s.high ∧ ¬ s.high < s.t0 := by
  obtain ⟨_, _, _, bZ, hpack⟩ := final_cube_both h hon hge ht hm
  have hhigh : bZ.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
    hpack.2.2.2.2.2.2.2.2.2
  refine ⟨bZ, hhigh, ?_⟩
  exact climb_high_ge h hm

/-- `tally_start` when the recorded high is already at or above the origin and
    `tally_max` already records a positive length. The white peg is written.
    The high and the maximum stay. -/
theorem tally_start_again (b : Ecbs.Board) (t0 high control ctrl tmax : Nat)
    (hLen0 : b.sudo_5Board_9tally_len = 0)
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 < b.sudo_5Board_3row.size)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hle : t0 ≤ high)
    (hFitT : FitsLen t0)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitC : FitsLen (ctrl + 1))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : 1 ≤ tmax) :
    Ecbs.tally_start b =
      .ok { b with
        sudo_5Board_3row := b.sudo_5Board_3row.set ⟨t0, hrow⟩ (1 : Int)
        sudo_5Board_9tally_len := 1
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } } := by
  unfold Ecbs.tally_start
  rw [hLen0, sudoAssertEq_int rfl 344, ok_bind]
  have hrow0 : t0 + 0 < b.sudo_5Board_3row.size := by simpa using hrow
  conv =>
    pattern (Ecbs.tally_put b (0 : Int) (1 : Int))
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  rw [tally_put_keep b t0 0 1 high control hT0 hrow0 hCtrlN (by simpa using hic)
      hHigh (by simpa using hle) (by simpa using hFitT), ok_bind]
  conv => zeta
  dsimp only
  rw [hCtrl, ← ofNat_eq_natCast ctrl, addI_ofNat_one ctrl hFitC, ok_bind]
  have hlen1 : (1 : Int) = ((1 : Nat) : Int) := rfl
  rw [tally_note_keep _ 1 tmax hlen1 (by simpa using hMax) hNote, ok_bind, pure_eq_ok]
  simp [hrow]

end EcbsLink2.Link2
