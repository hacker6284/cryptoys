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

private theorem elem_cast {α : Type} (a : Array α) (i : Nat)
    (h1 h2 : i < a.size) {v : α} (h : a[i]'h1 = v) : a[i]'h2 = v := by
  cases proof_irrel h1 h2
  exact h

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

/-- Homes layout. The lift does not write ops, the across cube is `acrossBoard`,
    and `comb_ops0` leaves slot 0 equal to the cell's incoming multiply counter. -/
theorem comb_ops0_cell
    (t : Spec.Tier) (b : Ecbs.Board)
    (baseX baseY px py xP yP zP : List Nat) (done cMul : Nat)
    (hAt : FformAt t b baseX baseY px py done)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hs2 : 2 < t.script)
    (hxL : xP.length = t.n) (hyL : yP.length = t.n) (hzL : zP.length = t.n)
    (hxT : allTritList xP) (hyT : allTritList yP) (hzT : allTritList zP)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed xP)
    (h1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed yP)
    (h2 : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed zP)
    (hd0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hd1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hd2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (moves slides c0 mark mx pk peakS hole cOps : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hc0 : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c0)
    (hmkN : b.sudo_5Board_6marker = Int.ofNat mark)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hMul : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hopMul : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hMul = Int.ofNat cMul)
    (hCtrl : FitsLen (c0 + 6)) (hOps : FitsLen (cOps + 3))
    (hRoom : FitsLen (moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n)))
    (hSl : FitsLen (slides + slideCharge t.n)) :
    ∃ (bL : Ecbs.Board)
      (a : DownAcross bL xP yP t.n t.k t.w t.h t.r t.benchlen t.combgap
            pk moves slides hole cOps (c0 + 1) mx t.script),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_point bL = .ok (bottomFlag a zP) ∧
      (bottomFlag a zP).sudo_5Board_4cost.sudo_5Costs_3ops[0]? =
        some (Int.ofNat cMul) := by
  obtain ⟨bL, a, hlift, hhome?, hheld?⟩ :=
    fform_homes_across t b baseX baseY px py xP yP zP done hAt hsh hOk sat
      hxL hyL hxT hyT hszH hszD h0 h1 h2 hd0 hd1 hd2 hoff moves slides c0 mark mx
      pk peakS hole cOps hmv hsl hc0 hmkN hmx hpk hstrict hhole hops hop1 hCtrl hOps
      hRoom hSl
  have href := marker_lift_refines b mark c0 hmkN hc0 (FitsLen.of_le hCtrl (by omega))
  have hbL : bL = { b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (c0 + 1) } } :=
    Except.ok.inj (hlift.symm.trans href)
  have hmkL : bL.sudo_5Board_9marker_on = true := by rw [hbL]; exact hAt.1
  have hoffL : bL.sudo_5Board_8bench_on = false := by rw [hbL]; exact hoff
  have hmNeg : bL.sudo_5Board_6marker < 0 := by
    have hmEq : bL.sudo_5Board_6marker = -1 := by rw [hbL]
    rw [hmEq]
    decide
  have hc : bL.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + 1) := by rw [hbL]
  have hmxL : bL.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    rw [hbL]; exact hmx
  have hte : bL.sudo_5Board_1t = embTier t := by rw [hbL]; exact hAt.2.1
  have hscript : bL.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat t.script := by
    rw [hte]; rfl
  have hopsL : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hbL]; exact hops
  have hopL : bL.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsL = (cOps : Int) := by
    have hArr : bL.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hbL]
    exact (at_eq hArr hopsL hops).trans hop1
  have h0D : 0 < bL.sudo_5Board_4held.size := a.h0D
  have h0H : 0 < bL.sudo_5Board_4home.size := a.h0H
  have hheld0 : bL.sudo_5Board_4held[0]'h0D = true := by
    have hArr : bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hbL]
    have hIdx : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (at_eq hArr h0D hIdx).trans hd0
  have hhome0 : bL.sudo_5Board_4home[0]'h0H = embed xP := by
    have hArr : bL.sudo_5Board_4home = b.sudo_5Board_4home := by rw [hbL]
    have hIdx : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (at_eq hArr h0H hIdx).trans h0
  have hstrictC : bL.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hbL]; exact hstrict.trans (ofNat_eq_natCast peakS)
  have hpeakC : bL.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hbL]; exact hpk.trans (ofNat_eq_natCast pk)
  have hn0 : 0 < t.n := hOk.n_pos
  have hn : bL.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [hte]; simp [embTier, ofNat_eq_natCast]
  have hmovesC : bL.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [hbL]; exact hmv.trans (ofNat_eq_natCast moves)
  have hbl : bL.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen := by rw [hte]; rfl
  have hcg : bL.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by rw [hte]; rfl
  have hholeL : bL.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hbL]; exact hhole
  have hw : bL.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w := by rw [hte]; rfl
  have hh : bL.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h := by rw [hte]; rfl
  have hr : bL.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r := by rw [hte]; rfl
  have hk : bL.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k := by rw [hte]; rfl
  have hspan : 3 * (t.n - 1) + t.combgap < t.benchlen := sat.cube_span
  have hsm := hsh.small
  have hnsm := hsh.n_small
  have hcapN := smallCap t.n t.benchlen
  have hnFit : FitsLen t.n := geomFit t.n t.benchlen t.n hnsm hsm.2.2.2 hcapN.1
  have hbenchFit : FitsLen t.benchlen :=
    geomFit t.n t.benchlen t.benchlen hnsm hsm.2.2.2 hcapN.2.1
  have h3 : FitsLen (3 * (t.n - 1)) :=
    geomFit t.n t.benchlen (3 * (t.n - 1)) hnsm hsm.2.2.2 hcapN.2.2
  have hMv : FitsLen (moves + cubeCharge t.n t.benchlen) := FitsLen.of_le hRoom (by omega)
  have hfm : FitsLen (moves + 2 * t.n) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hfold : FitsLen (moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    apply FitsLen.of_le hMv
    unfold cubeCharge
    omega
  have hdown := cube_down_eq bL 0 0 xP t.w t.h t.r t.n t.k moves hole t.benchlen pk peakS
    cOps t.combgap (c0 + 1) mx t.script hmkL hoffL hmNeg hc hmxL hscript
    (by have h := hsh.script_ge; omega) (FitsLen.of_le hCtrl (by omega)) hopsL hopL
    (FitsLen.of_le hOps (by omega)) h0D h0H hheld0 hhome0 (by rw [hbL, hszD]; decide)
    hstrictC hpeakC hn0 hn hxL hnFit hmovesC hbl hcg hspan h3 hfm hholeL hxT
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hw hh hr hk hsm hnsm
    hbenchFit hfold
  have hOn : a.b1On = acrossBoard bL xP t.n t.k moves hole t.benchlen pk peakS cOps
      (c0 + 1) mx hopsL h0D h0H :=
    Except.ok.inj (a.hcube.symm.trans hdown)
  have hops0 := comb_ops0 b bL cMul c0 a zP hMul hopMul hbL hopsL h0D h0H hOn
  have hs1 : 1 < t.script := by have h := hsh.script_ge; omega
  have hnb : t.n ≤ t.benchlen := by omega
  have hnbL : t.n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < t.n - t.k := by rw [hsh.gap]; exact Nat.mul_pos hsh.w0 hsh.r0
  obtain ⟨hpeg, hfitMv, hfitSl⟩ := up_settle_fit a hMv hSl
  obtain ⟨_, hMu, _⟩ := up_out_le a
  have hleF : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n) ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hleM : upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n ≤
      moves + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) := by
    unfold cubeCharge at hMu
    unfold cubeCharge
    omega
  have hfmU : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n) := FitsLen.of_le hRoom hleM
  have hfoldU : FitsLen (upMv2 a + 2 * pegCount ((upLane t.n t.k t.benchlen yP).take t.n) +
      2 * t.n + 3 * (t.benchlen - t.n)) := FitsLen.of_le hRoom hleF
  have hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed zP := by
    have hsz : 2 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
    have h := hhome?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszHOn]; decide) (Option.some.inj h)
  have hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true := by
    have hsz : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
    have h := hheld?
    rw [Array.getElem?_eq_getElem hsz] at h
    exact elem_cast _ 2 hsz (by rw [a.hszDOn]; decide) (Option.some.inj h)
  have hflag := frobenius_is_flag a zP hyT hyL hheld2 hhome2 hzL hzT hn0 hnbL hnb hgap0
    hs1 hs2 (FitsLen.of_le hCtrl (by omega)) (FitsLen.of_le hOps (by omega))
    hCtrl hOps hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfmU hfoldU
    hsh.w0 hsh.h0 hsh.rlt hsh.r0 hsh.n_eq hsh.k_le hsh.gap hsm hnsm
  exact ⟨bL, a, hlift, hflag, hops0⟩

end

end EcbsLink2.Link2
