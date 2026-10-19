/-
  A zero cell, packed as the next `FformAt`. The frame and the cubed
  projective point come from `zero_cell_proj`. The counters are the ones
  `bottomFlag` writes.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformZeroAt
import EcbsLink2.Link2.FformAtPack
import EcbsLink2.Link2.FformComb
import EcbsLink2.Link2.FformCharge
import EcbsLink2.Link2.FformSumRoom
import EcbsLink2.Link2.FformRunRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem flag_on_peak (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := rfl

private theorem flag_on_strict (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

private theorem flag_on_hole (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl

private theorem flag_on_mon (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_9marker_on = true := rfl

/-- The comb's peak, strict peak, and bench hole, as the naturals the cube writes. -/
theorem bottomFlag_peak
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4peak := by
    unfold bottomFlag
    exact flag_on_peak (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (countHeld ((seatAt a).sudo_5Board_4held.set ⟨2, seatAt_held2ix a⟩ false) 7)) := by
    unfold bottomOff
    exact cube_off_peak (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff

theorem bottomFlag_strict
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (countHeld (seatAt a).sudo_5Board_4held 7)) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    unfold bottomFlag
    exact flag_on_strict (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (countHeld (seatAt a).sudo_5Board_4held 7)) := by
    unfold bottomOff
    exact cube_off_strict (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff

theorem bottomFlag_hole
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip n bench y)))
        (topIdx (combStrip n bench z))) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    unfold bottomFlag
    exact flag_on_hole (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole (raisedHole a.hole1 (topIdx (combStrip n bench y)))
        (topIdx (combStrip n bench z))) := by
    unfold bottomOff
    exact cube_off_hole (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  exact hflag.trans hoff

end EcbsLink2.Link2
