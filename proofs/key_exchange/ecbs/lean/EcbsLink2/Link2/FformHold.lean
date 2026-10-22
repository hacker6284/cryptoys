/-
  Homes the comb does not write stay held. The across cube, the up settle,
  the up cube, the up's settle, and the bottom comb each clear one home.
  Home 3 and home 4 are none of those.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCount

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

theorem upFeed_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hi : i < 8) :
    (upFeed a).sudo_5Board_4held[i]'(by rw [upFeed_held a, a.hszDOn]; exact hi) =
      a.b1On.sudo_5Board_4held[i]'(by rw [a.hszDOn]; exact hi) :=
  at_eq (upFeed_held a) (by rw [upFeed_held a, a.hszDOn]; exact hi)
    (by rw [a.hszDOn]; exact hi)

theorem upSettled_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (h0 : (0 : Nat) ≠ i) (hi : i < 8) :
    (upSettled a).sudo_5Board_4held[i]'(by rw [up_held_size a]; exact hi) =
      (upFeed a).sudo_5Board_4held[i]'(by rw [upFeed_held a, a.hszDOn]; exact hi) := by
  simpa [upSettled] using
    settle_held_ne (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1 i h0
      (by rw [upFeed_held a, a.hszDOn]; exact hi)

theorem upBoard_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (h1 : (1 : Nat) ≠ i) (hi : i < 8) :
    (upBoard a).sudo_5Board_4held[i]'(by rw [up_board_held_size a]; exact hi) =
      (upSettled a).sudo_5Board_4held[i]'(by rw [up_held_size a]; exact hi) := by
  simpa [upBoard] using
    off_held_ne (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a) i h1
      (by rw [up_held_size a]; exact hi)

theorem pointFeed_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hi : i < 8) :
    (pointFeed a).sudo_5Board_4held[i]'(by rw [pointFeed_held_eq a, up_board_held_size a]; exact hi) =
      (upBoard a).sudo_5Board_4held[i]'(by rw [up_board_held_size a]; exact hi) :=
  at_eq (pointFeed_held_eq a)
    (by rw [pointFeed_held_eq a, up_board_held_size a]; exact hi)
    (by rw [up_board_held_size a]; exact hi)

theorem feed_settle_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (h1 : (1 : Nat) ≠ i) (hi : i < 8) :
    (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4held[i]'(by
        rw [settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
          (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set,
          pointFeed_held_eq a, up_board_held_size a]; exact hi) =
      (pointFeed a).sudo_5Board_4held[i]'(by
        rw [pointFeed_held_eq a, up_board_held_size a]; exact hi) :=
  settle_held_ne (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) i h1
    (by rw [pointFeed_held_eq a, up_board_held_size a]; exact hi)

theorem seatAt_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (h1 : (1 : Nat) ≠ i) (hi : i < 8) :
    (seatAt a).sudo_5Board_4held[i]'(by rw [seatAt_szD a]; exact hi) =
      (pointFeed a).sudo_5Board_4held[i]'(by
        rw [pointFeed_held_eq a, up_board_held_size a]; exact hi) := by
  simpa [seatAt] using feed_settle_held_from a i h1 hi

/-- A home other than 0, 1, and 2 is still the flag the across cube left. -/
theorem bottomFlag_held_from
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) (i : Nat) (h0 : (0 : Nat) ≠ i) (h1 : (1 : Nat) ≠ i)
    (h2 : (2 : Nat) ≠ i) (hi : i < 8) :
    (bottomFlag a z).sudo_5Board_4held[i]'(by rw [bottomFlag_szD a z]; exact hi) =
      a.b1On.sudo_5Board_4held[i]'(by rw [a.hszDOn]; exact hi) := by
  have hflag := off_held_ne (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) i h2
    (by rw [seatAt_szD a]; exact hi)
  have hseat := seatAt_held_from a i h1 hi
  have hfeed := pointFeed_held_from a i hi
  have hboard := upBoard_held_from a i h1 hi
  have hset := upSettled_held_from a i h0 hi
  have hon := upFeed_held_from a i hi
  have hchain : (seatAt a).sudo_5Board_4held[i]'(by rw [seatAt_szD a]; exact hi) =
      a.b1On.sudo_5Board_4held[i]'(by rw [a.hszDOn]; exact hi) :=
    hseat.trans (hfeed.trans (hboard.trans (hset.trans hon)))
  simpa [bottomFlag, bottomOff] using hflag.trans hchain

theorem bottomFlag_held3
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (h3 : a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true) :
    (bottomFlag a z).sudo_5Board_4held[3]'(by rw [bottomFlag_szD a z]; decide) = true := by
  rw [bottomFlag_held_from a z 3 (by decide) (by decide) (by decide) (by decide), h3]

theorem bottomFlag_held4
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (h4 : a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true) :
    (bottomFlag a z).sudo_5Board_4held[4]'(by rw [bottomFlag_szD a z]; decide) = true := by
  rw [bottomFlag_held_from a z 4 (by decide) (by decide) (by decide) (by decide), h4]

end

end EcbsLink2.Link2
