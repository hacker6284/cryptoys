/-
  The emitted climb keeps the ladder array. `climbRung_ladder` is one rung.
  `climbEmit_ladder` is the induction. The ladder on the tally board is
  `tierClimb`; this file only carries whatever array the step is given.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ClimbStep
import EcbsLink2.Link2.MulKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem climbStepBoard_ladder (x : Int) (b : Ecbs.Board) (rung : Nat) (last : Bool)
    (b' : Ecbs.Board) (h : climbStepBoard x b rung last = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  unfold climbStepBoard at h
  exact climbRung_ladder b rung last x b.sudo_5Board_9tally_len.toNat b' h

/-- The ladder array is the one the first board stored. A rung does not write it. -/
theorem climbEmit_ladder (x : Int) (b : Ecbs.Board) (rs : List Nat) (b' : Ecbs.Board)
    (h : climbEmit (climbStepBoard x) b rs = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  induction rs generalizing b with
  | nil =>
    simp [climbEmit] at h
    cases h
    rfl
  | cons r rs ih =>
    rw [climbEmit] at h
    cases hs : climbStepBoard x b r rs.isEmpty with
    | error _ =>
      rw [hs] at h
      simp only [error_bind] at h
      cases h
    | ok b1 =>
      rw [hs, ok_bind] at h
      exact (ih b1 h).trans (climbStepBoard_ladder x b r rs.isEmpty b1 hs)

end EcbsLink2.Link2
