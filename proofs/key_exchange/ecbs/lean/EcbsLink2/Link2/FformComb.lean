/-
  Slot 0 on the frobenius comb. `op_mul` is slot 0 and `op_cube` is slot 1.
  Each of the three cubes bumps slot 1 (`bumpOp`) and clears its source home.
  `marker_lift` writes the marker and the control counter. The slides between
  the cubes copy the ops array, as `clear` does. Slot 0 stays the value the
  cell started with, so `comb_u2z` can take that `Nat` as `cOps`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformMarker

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem at0 {α : Type} {a c : Array α} (h : a = c)
    (ha : 0 < a.size) (hc : 0 < c.size) : a[0] = c[0] := by
  subst h
  rfl

private theorem cast0 {α : Type} (a : Array α) (h1 h2 : 0 < a.size) :
    a[0]'h1 = a[0]'h2 := by
  cases proof_irrel h1 h2
  rfl

/-- A cube writes ops slot 1 and clears the source home. Slot 0 is the cell
    the bump leaves. -/
theorem cube_off_op0 (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (h0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
        rw [cube_off_ops, Array.size_set]; exact h0) =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0 := by
  have hArr :
      (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
        (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [cube_off_ops, bumpOp_ops]
  have h0c : 0 <
      (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [cube_off_ops, Array.size_set]; exact h0
  have h0b : 0 < (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [bumpOp_ops, Array.size_set]; exact h0
  have hB := bumpOp_other b 1 cOps 0 hops h0 (by decide)
  have hBs : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0b =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0 :=
    (cast0 _ h0b (by simp [bumpOp, Array.size_set]; exact h0)).trans hB
  exact (at0 hArr h0c h0b).trans hBs

private theorem some0 (a : Array Int) (h0 : 0 < a.size) {v : Int}
    (hv : a[0]'h0 = v) : a[0]? = some v :=
  (Array.getElem?_eq_getElem h0).trans (congrArg some hv)

private theorem point_ops_copy
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp [pointFeed, markerUpFeed, upFlag]

private theorem seat_ops_copy
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops := by
  rw [seatAt]
  exact settle_ops (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

section
attribute [local irreducible] seatAt pointFeed

/-- The comb's slot 0, once the across cube is the board `DownAcross` stores.
    The up cube and the bottom cube each bump slot 1. The two slides copy the
    array. -/
theorem comb_ops0
    (b0 b : Ecbs.Board) (cMul ctrl0 : Nat)
    {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (h0 : 0 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b0.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0 = Int.ofNat cMul)
    (hEq : b = { b0 with
        sudo_5Board_6marker := -1
        sudo_5Board_4cost := { b0.sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl0 + 1) } })
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b.sudo_5Board_4held.size)
    (hHome : 0 < b.sudo_5Board_4home.size)
    (hOn : a.b1On = acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx
        hops hF hHome) :
    (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cMul) := by
  have h0b : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hEq]; exact h0
  have hbArr : b.sudo_5Board_4cost.sudo_5Costs_3ops =
      b0.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hEq]
  have hb0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0b = Int.ofNat cMul :=
    (at0 hbArr h0b h0).trans hop
  let feed := markerDownFeed b ctrl mx
  let raw := cubeOffBoard feed 0 0 x n k moves holeN bench pk peakS cOps hops hF hHome
  have hC1 := cube_off_op0 feed 0 0 x n k moves holeN bench pk peakS cOps hops hF hHome h0b
  have h0raw : 0 < raw.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show raw.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        (cubeOffBoard feed 0 0 x n k moves holeN bench pk peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops.size from rfl,
      cube_off_ops, Array.size_set]
    exact h0b
  have hRaw : raw.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0raw = Int.ofNat cMul := by
    have hIdx : raw.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0raw =
        (cubeOffBoard feed 0 0 x n k moves holeN bench pk peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
          rw [cube_off_ops, Array.size_set]; exact h0b) := rfl
    exact hIdx.trans (hC1.trans hb0)
  have hAcOps : (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
      raw.sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  have h0Ac : 0 < (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hAcOps]; exact h0raw
  have hAc : (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0Ac =
      Int.ofNat cMul :=
    (at0 hAcOps h0Ac h0raw).trans hRaw
  have hOnArr : a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops =
      (acrossBoard b x n k moves holeN bench pk peakS cOps ctrl mx hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun brd => brd.sudo_5Board_4cost.sudo_5Costs_3ops) hOn
  have h0On : 0 < a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hOnArr]; exact h0Ac
  have hAcross : a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0On = Int.ofNat cMul :=
    (at0 hOnArr h0On h0Ac).trans hAc
  have hFeedArr := upFeed_ops a
  have hSetU := settle_ops (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have h0U : 0 < (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops =
        (settleBoard (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
      hSetU, hFeedArr]
    exact h0On
  have hUpIn : (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0U = Int.ofNat cMul := by
    have hEqS : (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops =
        a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [show (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops =
          (settleBoard (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
        hSetU, hFeedArr]
    exact (at0 hEqS h0U h0On).trans hAcross
  have hC2 := cube_off_op0 (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a) h0U
  have h0Board : 0 < (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upBoard, cube_off_ops, Array.size_set]; exact h0U
  have hUp : (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0Board = Int.ofNat cMul := by
    have hEqB : (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops =
        (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
          (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4cost.sudo_5Costs_3ops := rfl
    exact (at0 hEqB h0Board
        (by rw [cube_off_ops, Array.size_set]; exact h0U)).trans (hC2.trans hUpIn)
  have hEqP := point_ops_copy a
  have h0P : 0 < (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hEqP]; exact h0Board
  have hPoint : (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0P = Int.ofNat cMul :=
    (at0 hEqP h0P h0Board).trans hUp
  have hEqSeat := seat_ops_copy a
  have h0S : 0 < (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hEqSeat]; exact h0P
  have hSeat : (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0S = Int.ofNat cMul :=
    (at0 hEqSeat h0S h0P).trans hPoint
  have hC3 := cube_off_op0 (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) h0S
  have h0B : 0 < (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops =
        (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_3ops from rfl,
      bottomOff, cube_off_ops, Array.size_set]
    exact h0S
  have hFlag : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops[0]'h0B = Int.ofNat cMul := by
    have hEqF : (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops =
        (cubeOffBoard (seatAt a) 2 2 z n k
          (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
          (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
          (raisedPeak (upPk2 a)
            (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
          (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
          (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)).sudo_5Board_4cost.sudo_5Costs_3ops := by
      rw [show (bottomFlag a z).sudo_5Board_4cost.sudo_5Costs_3ops =
          (bottomOff a z).sudo_5Board_4cost.sudo_5Costs_3ops from rfl, bottomOff]
    exact (at0 hEqF h0B
        (by rw [cube_off_ops, Array.size_set]; exact h0S)).trans (hC3.trans hSeat)
  exact some0 _ h0B hFlag

end

end EcbsLink2.Link2
