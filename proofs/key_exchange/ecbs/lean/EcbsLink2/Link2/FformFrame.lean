/-
  The frame a nonzero F-form cell keeps. Homes 3 and 4 stay the original base
  point, the home arrays stay length 8, and the tier stays `embTier`.
  The name is `FformFrame` because `CellFrame` is the affine cell.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformCellStep
import EcbsLink2.Link2.FformHold
import EcbsLink2.Link2.FformCount

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have hxs := embed_beq xs ys
  rw [h] at hxs
  rw [embed_beq ys ys] at hxs
  exact of_decide_eq_true (by simpa using hxs)

/-- What `FformAt` asks of the tier and the base homes. -/
structure FrameAt (b : Ecbs.Board) (t : Spec.Tier) (baseX baseY : List Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  home3 : ∀ h : 3 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[3]'h = embed baseX
  held3 : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3]'h = true
  home4 : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4]'h = embed baseY
  held4 : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4]'h = true

theorem across_home_ne (b0 : Ecbs.Board) (xs : List Nat) (i : Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size)
    (hne : (0 : Nat) ≠ i) (hi : i < b0.sudo_5Board_4home.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4home[i]'(by
        rw [raw_home, Array.size_set, feed_home]; exact hi) =
      b0.sudo_5Board_4home[i]'hi := by
  have hraw := raw_home b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome
  have hfeed := feed_home b0 ctrl mx
  have hsrc : i < (markerDownFeed b0 ctrl mx).sudo_5Board_4home.size := by
    rw [hfeed]; exact hi
  have hset : i <
      ((markerDownFeed b0 ctrl mx).sudo_5Board_4home.set ⟨0, hHome⟩ #[]).size := by
    rw [Array.size_set]; exact hsrc
  have hget := at_eq hraw
      (by rw [raw_home, Array.size_set, feed_home]; exact hi) hset
  exact (hget.trans (set_ne _ 0 i hHome #[] hne hsrc)).trans (at_eq hfeed hsrc hi)

theorem across_held_ne (b0 : Ecbs.Board) (xs : List Nat) (i : Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size)
    (hne : (0 : Nat) ≠ i) (hi : i < b0.sudo_5Board_4held.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4held[i]'(by
        rw [raw_held, Array.size_set, feed_held]; exact hi) =
      b0.sudo_5Board_4held[i]'hi := by
  have hraw := raw_held b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome
  have hfeed := feed_held b0 ctrl mx
  have hsrc : i < (markerDownFeed b0 ctrl mx).sudo_5Board_4held.size := by
    rw [hfeed]; exact hi
  have hset : i <
      ((markerDownFeed b0 ctrl mx).sudo_5Board_4held.set ⟨0, hF⟩ false).size := by
    rw [Array.size_set]; exact hsrc
  have hget := at_eq hraw
      (by rw [raw_held, Array.size_set, feed_held]; exact hi) hset
  exact (hget.trans (set_ne _ 0 i hF false hne hsrc)).trans (at_eq hfeed hsrc hi)

private theorem lift_arrays (b bL : Ecbs.Board) (marker ctrl : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hfit : FitsLen (ctrl + 1))
    (hL : Ecbs.marker_lift b = .ok bL) :
    bL.sudo_5Board_4home = b.sudo_5Board_4home ∧
      bL.sudo_5Board_4held = b.sudo_5Board_4held ∧
      bL.sudo_5Board_1t = b.sudo_5Board_1t := by
  have href := marker_lift_refines b marker ctrl hm hc hfit
  have he : bL = { b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } } :=
    Except.ok.inj (hL.symm.trans href)
  simp [he]

/-- Homes 3 and 4 on `b1On` are the homes the cell started with. The lift
    rewrites the marker and the control counter. The across cube writes home 0.
    The up slide and the up cube are later: `flag_keeps_base` carries these
    values through them with `upSettled_home_ne`, `upBoard_home_ne`,
    `settle_held_ne`, and `off_held_ne`. -/
theorem b1On_base
    (b bL : Ecbs.Board) (baseX baseY x y : List Nat)
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross bL x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (ctrl0 marker0 peakS : Nat)
    (hszH : b.sudo_5Board_4home.size = 8)
    (hszD : b.sudo_5Board_4held.size = 8)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hfit : FitsLen (ctrl0 + 1))
    (hL : Ecbs.marker_lift b = .ok bL)
    (hops : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hOn : a.b1On = acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
        hops a.h0D a.h0H)
    (h3 : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed baseX)
    (h4 : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY)
    (hH3 : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (hH4 : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true) :
    a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX ∧
      a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY ∧
      a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true ∧
      a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true := by
  have harr := lift_arrays b bL marker0 ctrl0 hm hc hfit hL
  have home_from (i : Nat) (v : Array Int) (hne : (0 : Nat) ≠ i) (hi : i < 8)
      (h : b.sudo_5Board_4home[i]'(by rw [hszH]; exact hi) = v) :
      a.b1On.sudo_5Board_4home[i]'(by rw [a.hszHOn]; exact hi) = v := by
    have hib : i < b.sudo_5Board_4home.size := by rw [hszH]; exact hi
    have hiL : i < bL.sudo_5Board_4home.size := by rw [harr.1]; exact hib
    have hLv : bL.sudo_5Board_4home[i]'hiL = v := (at_eq harr.1 hiL hib).trans h
    have hAc := across_home_ne bL x i n k moves holeN bench pk peakS cOps ctrl mx
      hops a.h0D a.h0H hne hiL
    have hhome : a.b1On.sudo_5Board_4home =
        (acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
          hops a.h0D a.h0H).sudo_5Board_4home := by rw [hOn]
    have hget := at_eq hhome (by rw [a.hszHOn]; exact hi)
      (by rw [raw_home, Array.size_set, feed_home]; exact hiL)
    exact hget.trans (hAc.trans hLv)
  have held_from (i : Nat) (hne : (0 : Nat) ≠ i) (hi : i < 8)
      (h : b.sudo_5Board_4held[i]'(by rw [hszD]; exact hi) = true) :
      a.b1On.sudo_5Board_4held[i]'(by rw [a.hszDOn]; exact hi) = true := by
    have hib : i < b.sudo_5Board_4held.size := by rw [hszD]; exact hi
    have hiL : i < bL.sudo_5Board_4held.size := by rw [harr.2.1]; exact hib
    have hLv : bL.sudo_5Board_4held[i]'hiL = true := (at_eq harr.2.1 hiL hib).trans h
    have hAc := across_held_ne bL x i n k moves holeN bench pk peakS cOps ctrl mx
      hops a.h0D a.h0H hne hiL
    have hheld : a.b1On.sudo_5Board_4held =
        (acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
          hops a.h0D a.h0H).sudo_5Board_4held := by rw [hOn]
    have hget := at_eq hheld (by rw [a.hszDOn]; exact hi)
      (by rw [raw_held, Array.size_set, feed_held]; exact hiL)
    exact hget.trans (hAc.trans hLv)
  exact ⟨home_from 3 (embed baseX) (by decide) (by decide) h3,
    home_from 4 (embed baseY) (by decide) (by decide) h4,
    held_from 3 (by decide) (by decide) hH3,
    held_from 4 (by decide) (by decide) hH4⟩

/-- The across cube keeps the tier. `markerDownFeed` rewrites the marker and
    the control counter, and `cubeOffBoard` does not write the tier. -/
private theorem b1On_tier
    (b bL : Ecbs.Board) (x y : List Nat)
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross bL x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (ctrl0 marker0 peakS : Nat)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hfit : FitsLen (ctrl0 + 1))
    (hL : Ecbs.marker_lift b = .ok bL)
    (hops : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hOn : a.b1On = acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
        hops a.h0D a.h0H) :
    a.b1On.sudo_5Board_1t = b.sudo_5Board_1t := by
  have harr := lift_arrays b bL marker0 ctrl0 hm hc hfit hL
  have hcube := cube_off_tier (markerDownFeed bL ctrl mx) 0 0 x n k moves holeN bench pk
    peakS cOps hops a.h0D a.h0H
  have hwrap : (acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
      hops a.h0D a.h0H).sudo_5Board_1t =
      (cubeOffBoard (markerDownFeed bL ctrl mx) 0 0 x n k moves holeN bench pk peakS cOps
        hops a.h0D a.h0H).sudo_5Board_1t := by
    unfold acrossBoard
    rfl
  have hfeed : (markerDownFeed bL ctrl mx).sudo_5Board_1t = bL.sudo_5Board_1t := rfl
  exact (congrArg (fun brd => brd.sudo_5Board_1t) hOn).trans
    (hwrap.trans (hcube.trans (hfeed.trans harr.2.2)))

/-- Putting the marker flag back does not change the tier. -/
private theorem flag_on_tier (b : Ecbs.Board) :
    ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_1t = b.sudo_5Board_1t := rfl

/-- Stepping the marker does not change the tier. -/
private theorem up_feed_tier (b : Ecbs.Board) (m ctrl mx : Nat) :
    (markerUpFeed b m ctrl mx).sudo_5Board_1t = b.sudo_5Board_1t := rfl

/-- The comb's tier is the tier `b1On` had. Each feed copies it, each settle
    keeps it (`settle_tier_eq`), and each cube keeps it (`cube_off_tier`). -/
theorem bottomFlag_tier
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_1t = a.b1On.sudo_5Board_1t := by
  have hflag : (bottomFlag a z).sudo_5Board_1t = (bottomOff a z).sudo_5Board_1t := by
    unfold bottomFlag
    exact flag_on_tier (bottomOff a z)
  have hoff : (bottomOff a z).sudo_5Board_1t = (seatAt a).sudo_5Board_1t := by
    unfold bottomOff
    exact cube_off_tier (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)
  have hseat : (seatAt a).sudo_5Board_1t = (pointFeed a).sudo_5Board_1t := by
    unfold seatAt
    exact settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hpoint : (pointFeed a).sudo_5Board_1t = (upFlag a).sudo_5Board_1t := by
    unfold pointFeed
    exact up_feed_tier (upFlag a) 1 (ctrl + 3) (max (max mx 1) 2)
  have hupFlag : (upFlag a).sudo_5Board_1t = (upBoard a).sudo_5Board_1t := by
    unfold upFlag
    exact flag_on_tier (upBoard a)
  have hup : (upBoard a).sudo_5Board_1t = (upSettled a).sudo_5Board_1t := by
    unfold upBoard
    exact cube_off_tier (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hset : (upSettled a).sudo_5Board_1t = (upFeed a).sudo_5Board_1t := by
    unfold upSettled
    exact settle_tier_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  exact hflag.trans (hoff.trans (hseat.trans (hpoint.trans (hupFlag.trans
    (hup.trans (hset.trans (upFeed_tier a)))))))

/-- The bottom cube keeps homes 3 and 4. `bottomFlag_later` is the off step
    plus the settle chain; `bottomFlag_held3` and `bottomFlag_held4` are the flags. -/
theorem flag_keeps_base
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z baseX baseY : List Nat)
    (h3 : a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed baseX)
    (h4 : a.b1On.sudo_5Board_4home[4]'(by rw [a.hszHOn]; decide) = embed baseY)
    (hH3 : a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true)
    (hH4 : a.b1On.sudo_5Board_4held[4]'(by rw [a.hszDOn]; decide) = true) :
    (bottomFlag a z).sudo_5Board_4home[3]'(by rw [bottomFlag_sz a z]; decide) = embed baseX ∧
    (bottomFlag a z).sudo_5Board_4home[4]'(by rw [bottomFlag_sz a z]; decide) = embed baseY ∧
    (bottomFlag a z).sudo_5Board_4held[3]'(by rw [bottomFlag_szD a z]; decide) = true ∧
    (bottomFlag a z).sudo_5Board_4held[4]'(by rw [bottomFlag_szD a z]; decide) = true ∧
    (bottomFlag a z).sudo_5Board_4home.size = 8 ∧
    (bottomFlag a z).sudo_5Board_4held.size = 8 := by
  refine ⟨?_, ?_, bottomFlag_held3 a z hH3, bottomFlag_held4 a z hH4,
      bottomFlag_sz a z, bottomFlag_szD a z⟩
  · rw [bottomFlag_later a z 3 (by decide) (by decide) (by decide) (by decide), h3]
  · rw [bottomFlag_later a z 4 (by decide) (by decide) (by decide) (by decide), h4]

/-- `FrameAt` on the board the cell entered is `FrameAt` on the comb.
    `b1On_base` is the lift and the across cube. `flag_keeps_base` is the up
    slide, the up cube, and the bottom cube. The tier is `embTier` at each step. -/
theorem comb_frame
    (t : Spec.Tier) (b bL bZ : Ecbs.Board) (baseX baseY x y z : List Nat)
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross bL x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (ctrl0 marker0 peakS : Nat)
    (fr : FrameAt b t baseX baseY)
    (hm : b.sudo_5Board_6marker = Int.ofNat marker0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hfit : FitsLen (ctrl0 + 1))
    (hL : Ecbs.marker_lift b = .ok bL)
    (hops : 1 < bL.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hOn : a.b1On = acrossBoard bL x n k moves holeN bench pk peakS cOps ctrl mx
        hops a.h0D a.h0H)
    (hZ : bZ = bottomFlag a z) :
    FrameAt bZ t baseX baseY := by
  have hbase := b1On_base b bL baseX baseY x y a ctrl0 marker0 peakS fr.szH fr.szD
    hm hc hfit hL hops hOn
    (fr.home3 (by rw [fr.szH]; decide)) (fr.home4 (by rw [fr.szH]; decide))
    (fr.held3 (by rw [fr.szD]; decide)) (fr.held4 (by rw [fr.szD]; decide))
  have hflag := flag_keeps_base a z baseX baseY hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2
  have htier := (bottomFlag_tier a z).trans
    ((b1On_tier b bL x y a ctrl0 marker0 peakS hm hc hfit hL hops hOn).trans fr.tier)
  have hhome := congrArg (fun brd => brd.sudo_5Board_4home) hZ
  have hheld := congrArg (fun brd => brd.sudo_5Board_4held) hZ
  exact {
    tier := (congrArg (fun brd => brd.sudo_5Board_1t) hZ).trans htier
    szH := (congrArg Array.size hhome).trans hflag.2.2.2.2.1
    szD := (congrArg Array.size hheld).trans hflag.2.2.2.2.2
    home3 := fun h =>
      (at_eq hhome h (by rw [bottomFlag_sz a z]; decide)).trans hflag.1
    held3 := fun h =>
      (at_eq hheld h (by rw [bottomFlag_szD a z]; decide)).trans hflag.2.2.1
    home4 := fun h =>
      (at_eq hhome h (by rw [bottomFlag_sz a z]; decide)).trans hflag.2.1
    held4 := fun h =>
      (at_eq hheld h (by rw [bottomFlag_szD a z]; decide)).trans hflag.2.2.2.1
  }

/-- The cell's tail still holds those homes, and the tier is `embTier`.
    The base homes come from the incoming `FrameAt`, through `b1On_base`.
    `hLink3` and `hLink4` name the same lists as `x2` and `y2`. -/
theorem cell_frame (t : Spec.Tier) (b : Ecbs.Board) (lane : List Nat)
    (n k bench : Nat) (v z x2 y2 x3 yUp : List Nat)
    (tier : Ecbs.Tier) (szHome szHeld : Nat) (baseX baseY : List Nat)
    (c : CellAt b lane n k bench v z x2 y2 x3 yUp tier szHome szHeld)
    {bIn b0 : Ecbs.Board} {x y : List Nat}
    {w h r cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b0 x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (ctrl0 marker0 peakS : Nat)
    (fr : FrameAt bIn t baseX baseY)
    (hm : bIn.sudo_5Board_6marker = Int.ofNat marker0)
    (hc : bIn.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl0)
    (hfit : FitsLen (ctrl0 + 1))
    (hL : Ecbs.marker_lift bIn = .ok b0)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hOn : a.b1On = acrossBoard b0 x n k moves holeN bench pk peakS cOps ctrl mx
        hops a.h0D a.h0H)
    (hLink3 : (bottomFlag a z).sudo_5Board_4home[3]'(by rw [bottomFlag_sz a z]; decide) = embed x2)
    (hLink4 : (bottomFlag a z).sudo_5Board_4home[4]'(by rw [bottomFlag_sz a z]; decide) = embed y2)
    (hTier : tier = embTier t) (hszH : szHome = 8) (hszD : szHeld = 8) :
    FrameAt b t baseX baseY := by
  have hbase := b1On_base bIn b0 baseX baseY x y a ctrl0 marker0 peakS fr.szH fr.szD
    hm hc hfit hL hops hOn
    (fr.home3 (by rw [fr.szH]; decide)) (fr.home4 (by rw [fr.szH]; decide))
    (fr.held3 (by rw [fr.szD]; decide)) (fr.held4 (by rw [fr.szD]; decide))
  have hflag := flag_keeps_base a z baseX baseY hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2
  have hx : x2 = baseX := embed_inj (hLink3.symm.trans hflag.1)
  have hy : y2 = baseY := embed_inj (hLink4.symm.trans hflag.2.1)
  exact {
    tier := c.tierEq.trans hTier
    szH := c.szH.trans hszH
    szD := c.szD.trans hszD
    home3 := fun h => (c.home3 h).trans (congrArg embed hx)
    held3 := c.held3
    home4 := fun h => (c.home4 h).trans (congrArg embed hy)
    held4 := c.held4
  }

end EcbsLink2.Link2
