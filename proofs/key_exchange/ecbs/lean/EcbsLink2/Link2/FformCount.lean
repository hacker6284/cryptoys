/-
  Held flags and cost counters on the comb `frobenius_point` returns.
  The numbers are the ones the three cubes and the two settles write.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformKept

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem off_op1 (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by
      rw [cube_off_ops, Array.size_set]; exact hops) =
      Int.ofNat (cOps + 1) := by
  have hset := cube_off_ops b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  have hget := at_eq hset
    (by rw [cube_off_ops, Array.size_set]; exact hops)
    (by rw [Array.size_set]; exact hops)
  exact hget.trans (set_eq b.sudo_5Board_4cost.sudo_5Costs_3ops 1 hops (Int.ofNat (cOps + 1)))

theorem off_held_src (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4held[src]'(by
      rw [cube_off_held, Array.size_set]; exact hF) = false := by
  have hset := cube_off_held b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  have hget := at_eq hset
    (by rw [cube_off_held, Array.size_set]; exact hF)
    (by rw [Array.size_set]; exact hF)
  exact hget.trans (set_eq b.sudo_5Board_4held src hF false)

theorem off_held_ne (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (i : Nat) (hne : src ≠ i) (hi : i < b.sudo_5Board_4held.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4held[i]'(by
      rw [cube_off_held, Array.size_set]; exact hi) =
      b.sudo_5Board_4held[i] := by
  have hset := cube_off_held b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  have hget := at_eq hset
    (by rw [cube_off_held, Array.size_set]; exact hi)
    (by rw [Array.size_set]; exact hi)
  exact hget.trans (set_ne b.sudo_5Board_4held src i hF false hne hi)

theorem settle_held_here (b : Ecbs.Board) (home : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4held[home]'(by
      rw [settle_held_eq b home hin xs n moves slides peak, Array.size_set]; exact hin.hD) =
      true := by
  have hset := settle_held_eq b home hin xs n moves slides peak
  have hget := at_eq hset
    (by rw [hset, Array.size_set]; exact hin.hD)
    (by rw [Array.size_set]; exact hin.hD)
  exact hget.trans (set_eq b.sudo_5Board_4held home hin.hD true)

theorem settle_held_ne (b : Ecbs.Board) (home : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat)
    (i : Nat) (hne : home ≠ i) (hi : i < b.sudo_5Board_4held.size) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4held[i]'(by
      rw [settle_held_eq b home hin xs n moves slides peak, Array.size_set]; exact hi) =
      b.sudo_5Board_4held[i] := by
  have hset := settle_held_eq b home hin xs n moves slides peak
  have hget := at_eq hset
    (by rw [hset, Array.size_set]; exact hi)
    (by rw [Array.size_set]; exact hi)
  exact hget.trans (set_ne b.sudo_5Board_4held home i hin.hD true hne hi)

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

theorem pointFeed_ctrl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ((ctrl + 3) + 2) := by
  simp [pointFeed, markerUpFeed]

theorem pointFeed_mark
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_6marker = Int.ofNat (1 + 1) := by
  simp [pointFeed, markerUpFeed]

theorem pointFeed_mx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max (max mx 1) 2) (1 + 2)) := by
  simp [pointFeed, markerUpFeed]

theorem pointFeed_held_eq
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4held = (upBoard a).sudo_5Board_4held := by
  simp [pointFeed, upFlag, markerUpFeed]

end

section
attribute [local irreducible] pointFeed

variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

private theorem seat_ctrl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (pointFeed a).sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  rw [seatAt]
  exact settle_ctrl_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

private theorem seat_mark
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_6marker = (pointFeed a).sudo_5Board_6marker := by
  rw [seatAt]
  exact settle_ix_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

private theorem seat_mx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (pointFeed a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  rw [seatAt]
  exact settle_mx_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seatAt_szD
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4held.size = 8 := by
  rw [seatAt, settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set,
    pointFeed_held_eq, up_board_held_size]

theorem bottomFlag_szD
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4held.size = 8 := by
  have hheld : (bottomFlag a z).sudo_5Board_4held = (bottomOff a z).sudo_5Board_4held := rfl
  rw [hheld, bottomOff, cube_off_held, Array.size_set, seatAt_szD]

theorem bottomFlag_ctrl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 5) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4ctrl := rfl
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (seatAt a).sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    rw [bottomOff, cube_off_ctrl]
  have hnat : (ctrl + 3) + 2 = ctrl + 5 := by omega
  rw [hflag, hoff, seat_ctrl, pointFeed_ctrl, hnat]

theorem bottomFlag_mark
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_6marker = Int.ofNat 2 := by
  have hflag : (bottomFlag a z).sudo_5Board_6marker = (bottomOff a z).sudo_5Board_6marker := rfl
  have hoff : (bottomOff a z).sudo_5Board_6marker = (seatAt a).sudo_5Board_6marker := by
    rw [bottomOff, cube_off_ix]
  have hnat : (1 + 1 : Nat) = 2 := by omega
  rw [hflag, hoff, seat_mark, pointFeed_mark, hnat]

theorem bottomFlag_mx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max (max mx 1) 2) 3) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := rfl
  have hoff : (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (seatAt a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
    rw [bottomOff, cube_off_mx]
  have hnat : (1 + 2 : Nat) = 3 := by omega
  rw [hflag, hoff, seat_mx, pointFeed_mx, hnat]

theorem bottomFlag_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves
        (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) z n k bench) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_5moves =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_5moves := rfl
  rw [hflag, bottomOff, cube_off_moves]

theorem seatAt_slides
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (upSl a + 2 * pegCount ((upLane n k bench y).take n)) := by
  rw [seatAt]
  exact settle_slides_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem bottomFlag_slides
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (upSl a + 2 * pegCount ((upLane n k bench y).take n)) := by
  have hflag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_6slides =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_6slides := rfl
  rw [hflag, bottomOff, cube_off_slides, seatAt_slides]

theorem feed_settle_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4held[0]'(by
        rw [settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
          (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set,
          pointFeed_held_eq, up_board_held_size]; decide) = true := by
  have hseat := settle_held_ne (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) 0 (by decide)
    (by rw [pointFeed_held_eq, up_board_held_size]; decide)
  have h0b : 0 < (upBoard a).sudo_5Board_4held.size := by rw [up_board_held_size]; decide
  have h0s : 0 < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size]; decide
  have hpt : (pointFeed a).sudo_5Board_4held[0]'(by rw [pointFeed_held_eq, up_board_held_size]; decide) =
      true := by
    have h := pointFeed_held_eq a
    exact (at_eq h _ h0b).trans ((upBoard_held0 a h0b h0s).trans (upSettled_held0 a h0s))
  exact hseat.trans hpt

theorem seatAt_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4held[0]'(by rw [seatAt_szD a]; decide) = true := by
  simpa [seatAt] using feed_settle_held0 a

theorem feed_settle_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4held[1]'(by
        rw [settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
          (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]; exact pointFeed_heldIx a) =
      true :=
  settle_held_here (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seatAt_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4held[1]'(by rw [seatAt_szD a]; decide) = true := by
  simpa [seatAt] using feed_settle_held1 a

theorem bottomFlag_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    1 < (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  have hops : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops =
      (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  rw [hops, bottomOff, cube_off_ops, Array.size_set]
  exact seatAt_ops a

section
attribute [local irreducible] seatAt

theorem bottomFlag_op
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(bottomFlag_ops a z) =
      Int.ofNat (cOps + 3) := by
  have h := off_op1 (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  have hnat : (cOps + 2) + 1 = cOps + 3 := by omega
  simpa [bottomFlag, bottomOff, hnat] using h

theorem bottomFlag_held2
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4held[2]'(by rw [bottomFlag_szD a z]; decide) = false := by
  have h := off_held_src (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  simpa [bottomFlag, bottomOff] using h

theorem bottomFlag_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4held[0]'(by rw [bottomFlag_szD a z]; decide) = true := by
  have hkeep := off_held_ne (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) 0
    (by decide) (by rw [seatAt_szD a]; decide)
  simpa [bottomFlag, bottomOff] using hkeep.trans (seatAt_held0 a)

theorem bottomFlag_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4held[1]'(by rw [bottomFlag_szD a z]; decide) = true := by
  have hkeep := off_held_ne (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) 1
    (by decide) (by rw [seatAt_szD a]; decide)
  simpa [bottomFlag, bottomOff] using hkeep.trans (seatAt_held1 a)

end

end

end EcbsLink2.Link2
