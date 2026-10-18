/-
  A live F-form cell whose `fform_add` returns false ends the walk.
  That is the reroll: `.ok ((true, false), …)` with the marker off.
  `fform_add` does not invert, so this stepper does not raise the
  chord's check trap. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkFform

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- From a live cell, one `fform_add` that returns false is the reroll.
    The loop does not take another cell. -/
theorem fform_loop_reroll (cells : List Nat) (i toN c : Nat)
    (b0 b bF bA : Ecbs.Board)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hc : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_point b = .ok bF)
    (hadd : Ecbs.fform_add bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (false, bA)) :
    SudoRt.runLoopOn (Int.ofNat i, (b0, true))
        (fuelRange (Int.ofNat i) (Int.ofNat toN))
        (fformStep (embed cells) (Int.ofNat toN)) chordAfter (fun r => pure r) =
      .ok ((true, false), { bA with sudo_5Board_9marker_on := false }) := by
  have hstep := fformStep_reroll cells i toN c b0 b bF bA hi hlen hc hc0 hc2 hml hfrob hadd
  rw [fuelRange_le hi, runLoopOn_succ, hstep]
  simp [pure_eq_ok]

end EcbsLink2.Link2
