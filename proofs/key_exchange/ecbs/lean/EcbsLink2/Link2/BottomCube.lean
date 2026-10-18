/-
  The bottom comb after the cubed up has been slid home.
  `pointFeed` is not unfolded. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomOff

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def seatAt
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem pointFeed_w
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [upFlag, upBoard, cube_off_tier, up_w]
  exact h

theorem pointFeed_h
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [upFlag, upBoard, cube_off_tier, up_h]
  exact h

theorem pointFeed_r
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [upFlag, upBoard, cube_off_tier, up_r]
  exact h

theorem pointFeed_k
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [upFlag, upBoard, cube_off_tier, up_k]
  exact h

theorem pointFeed_bl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [upFlag, upBoard, cube_off_tier, up_bl]
  exact h

theorem pointFeed_cg
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
  have h : (upFlag a).sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    rw [upFlag, upBoard, cube_off_tier, up_cg]
  exact h

theorem pointFeed_strict
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7) : Int) := by
  have h : (upFlag a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7) : Int) := by
    have hc := cube_off_strict (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
    rw [show (upFlag a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        (upBoard a).sudo_5Board_4cost.sudo_5Costs_11peak_strict from rfl, upBoard, hc]
    rfl
  exact h

theorem pointFeed_hole
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole a.hole1 (topIdx (combStrip n bench y))) := by
  have h : (upFlag a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole a.hole1 (topIdx (combStrip n bench y))) := by
    rw [upFlag, upBoard]
    exact cube_off_hole (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  exact h

theorem pointFeed_home2ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (pointFeed a).sudo_5Board_4home.size := by
  have h : 2 < (upFlag a).sudo_5Board_4home.size := by
    rw [upFlag, up_board_home_size a]; decide
  exact h

theorem pointFeed_held2ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (pointFeed a).sudo_5Board_4held.size := by
  have h : 2 < (upFlag a).sudo_5Board_4held.size := by
    rw [upFlag, up_board_held_size a]; decide
  exact h

theorem pointFeed_z
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z) :
    (pointFeed a).sudo_5Board_4home[2]'(pointFeed_home2ix a) = embed z :=
  bottom_home a z hhome2

theorem pointFeed_zHeld
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true) :
    (pointFeed a).sudo_5Board_4held[2]'(pointFeed_held2ix a) = true :=
  bottom_held a hheld2

theorem seatAt_off
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_9marker_on = false := by
  rw [seatAt, settle_marker_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_off a

theorem seatAt_bench
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_8bench_on = false := by
  rw [seatAt]
  exact settle_bench_off (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seatAt_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) := by
  rw [seatAt]
  exact settle_moves_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seatAt_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_n a

theorem seatAt_w
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_w a

theorem seatAt_h
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_h a

theorem seatAt_r
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_r a

theorem seatAt_k
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_k a

theorem seatAt_bl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_bl a

theorem seatAt_cg
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
  rw [seatAt, settle_tier_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_cg a

theorem seatAt_strict
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7) : Int) := by
  rw [seatAt, settle_strict_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_strict a

theorem seatAt_hole
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole a.hole1 (topIdx (combStrip n bench y))) := by
  rw [seatAt, settle_hole_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_hole a

theorem seatAt_held7
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    7 ≤ (seatAt a).sudo_5Board_4held.size := by
  rw [seatAt, settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]
  exact pointFeed_held7 a

theorem seatAt_home2ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (seatAt a).sudo_5Board_4home.size := by
  rw [seatAt, settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]
  exact pointFeed_home2ix a

theorem seatAt_held2ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (seatAt a).sudo_5Board_4held.size := by
  rw [seatAt, settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]
  exact pointFeed_held2ix a

section
attribute [local irreducible] pointFeed

theorem seatAt_z?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z) :
    (seatAt a).sudo_5Board_4home[2]? = some (embed z) := by
  have hop : (pointFeed a).sudo_5Board_4home[2]? = some (embed z) := by
    rw [Array.getElem?_eq_getElem (pointFeed_home2ix a)]
    exact congrArg some (pointFeed_z a z hhome2)
  rw [seatAt, settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
  exact hop

theorem seatAt_zHeld?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true) :
    (seatAt a).sudo_5Board_4held[2]? = some true := by
  have hop : (pointFeed a).sudo_5Board_4held[2]? = some true := by
    rw [Array.getElem?_eq_getElem (pointFeed_held2ix a)]
    exact congrArg some (pointFeed_zHeld a hheld2)
  rw [seatAt, settle_held_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 2)]
  exact hop

theorem seatAt_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [seatAt]
  exact seat_opsIx a

theorem seatAt_op
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(seatAt_ops a) =
      (((cOps + 2 : Nat) : Int)) := by
  have h : (seatAt a).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some (((cOps + 2 : Nat) : Int)) := by
    rw [seatAt]
    exact seat_op1 a
  rw [Array.getElem?_eq_getElem (seatAt_ops a)] at h
  exact Option.some.inj h

theorem seatAt_z
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z) :
    (seatAt a).sudo_5Board_4home[2]'(seatAt_home2ix a) = embed z := by
  have h := seatAt_z? a z hhome2
  rw [Array.getElem?_eq_getElem (seatAt_home2ix a)] at h
  exact Option.some.inj h

theorem seatAt_zHeld
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true) :
    (seatAt a).sudo_5Board_4held[2]'(seatAt_held2ix a) = true := by
  have h := seatAt_zHeld? a hheld2
  rw [Array.getElem?_eq_getElem (seatAt_held2ix a)] at h
  exact Option.some.inj h

end

theorem seatAt_peak
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7) : Int) := by
  rw [seatAt, settle_peak_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) (pointFeed_pk a), raisedPeak]
  rfl

section
attribute [local irreducible] pointFeed

/-- The bottom comb. Marker off, bench off, source home 2 holds `z`. -/
theorem seatAt_cube
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true)
    (hz : z.length = n) (hzt : allTritList z) (hn0 : 0 < n)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hfitC3 : FitsLen (cOps + 3))
    (hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n))
    (hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n +
        3 * (bench - n)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    Ecbs.cube (seatAt a) ((2 : Nat) : Int) ((2 : Nat) : Int) =
      .ok (cubeOffBoard (seatAt a) 2 2 z n k
        (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
        (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)) := by
  exact cube_off_eq (seatAt a) 2 2 z w h r n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) cg
    (seatAt_off a) (seatAt_bench a) (seatAt_ops a) (seatAt_op a)
    (by rw [show (cOps + 2) + 1 = cOps + 3 by omega]; exact hfitC3)
    (seatAt_bl a) (seatAt_cg a) hspan
    (seatAt_held2ix a) (seatAt_home2ix a) (seatAt_zHeld a hheld2) (seatAt_z a z hhome2)
    (seatAt_held7 a) hn0 (seatAt_n a) hz hnFit (seatAt_moves a) (seatAt_peak a)
    (seatAt_strict a) hzt h3 hfm
    ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩
    (seatAt_w a) (seatAt_h a) (seatAt_r a) (seatAt_k a) (seatAt_hole a)
    hsm hnsm hbenchFit hfold

end

theorem seatAt_lane
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (cubeOffBoard (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)).sudo_5Board_5bench =
      embed (laneFold n (n - k) (combStrip n bench z)) :=
  cube_off_bench (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)

theorem seatAt_on
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (cubeOffBoard (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)).sudo_5Board_8bench_on =
      true :=
  cube_off_on (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)

theorem seatAt_to
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (cubeOffBoard (seatAt a) 2 2 z n k
      (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
      (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
      (raisedPeak (upPk2 a)
        (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
      (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)).sudo_5Board_8bench_to =
      (2 : Int) :=
  cube_off_to (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)

theorem seatAt_take (z : List Nat) (n k bench : Nat) :
    (laneFold n (n - k) (combStrip n bench z)).take n = fieldCube n k bench z :=
  cube_off_prefix n k bench z

theorem feed_home_irrel
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    pointFeed_homeIx a = upFlagH a := proof_irrel _ _

theorem feed_held_irrel
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    pointFeed_heldIx a = upFlag1 a := proof_irrel _ _

end EcbsLink2.Link2
