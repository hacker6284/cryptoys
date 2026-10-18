/-
  Homes the bottom comb does not write. Across stays the cubed across.
  Up is what the slide wrote. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomGlue

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem pointFeed_home0ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    0 < (pointFeed a).sudo_5Board_4home.size := by
  have h : 0 < (upBoard a).sudo_5Board_4home.size := by
    rw [up_board_home_size a]; decide
  exact h

theorem pointFeed_x
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4home[0]'(pointFeed_home0ix a) =
      embed (fieldCube n k bench x) := up_home0 a

section
attribute [local irreducible] pointFeed

theorem seatAt_x?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4home[0]? = some (embed (fieldCube n k bench x)) := by
  have hop : (pointFeed a).sudo_5Board_4home[0]? =
      some (embed (fieldCube n k bench x)) := by
    rw [Array.getElem?_eq_getElem (pointFeed_home0ix a)]
    exact congrArg some (pointFeed_x a)
  rw [seatAt, settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [Array.getElem?_set_ne _ _ _ (by decide : (1 : Nat) ≠ 0)]
  exact hop

theorem seatAt_y?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4home[1]? =
      some (embed ((upLane n k bench y).take n)) := by
  rw [seatAt, settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [Array.getElem?_set_eq]

theorem seatAt_yCube?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4home[1]? = some (embed (fieldCube n k bench y)) := by
  have h := seatAt_y? a
  rwa [upLane_take] at h

end

/-- The bottom comb writes home 2. Home 0 stays the cubed across. -/
theorem flag_cube_home0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    ({ cubeOffBoard (seatAt a) 2 2 z n k
        (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
        (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) with
        sudo_5Board_9marker_on := true }).sudo_5Board_4home[0]? =
      some (embed (fieldCube n k bench x)) := by
  rw [cube_off_home]
  rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 0)]
  exact seatAt_x? a

/-- The bottom comb writes home 2. Home 1 stays the cubed up. -/
theorem flag_cube_home1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    ({ cubeOffBoard (seatAt a) 2 2 z n k
        (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
        (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
        (raisedPeak (upPk2 a)
          (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
        (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
        (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) with
        sudo_5Board_9marker_on := true }).sudo_5Board_4home[1]? =
      some (embed (fieldCube n k bench y)) := by
  rw [cube_off_home]
  rw [Array.getElem?_set_ne _ _ _ (by decide : (2 : Nat) ≠ 1)]
  exact seatAt_yCube? a

/-- The bottom of `frobenius_point`, including the cubed across and up.
    Home 0 is `fieldCube` of across, home 1 is `fieldCube` of up, and the
    bench above hole `n` is empty. -/
theorem frobenius_bottom_homes
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hyt : allTritList y) (hy : y.length = n)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z)
    (hz : z.length = n) (hzt : allTritList z)
    (hn0 : 0 < n) (hnbL : n ≤ a.laneX.length) (hnb : n ≤ bench) (hgap0 : 0 < n - k)
    (hs1 : 1 < script) (hs2 : 2 < script)
    (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hfitCtrl : FitsLen (ctrl + 5)) (hfitC3 : FitsLen (cOps + 3))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitMv : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitSl : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n))
    (hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n +
        3 * (bench - n)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    ∃ bZ,
      Ecbs.frobenius_point b = .ok bZ ∧
      bZ.sudo_5Board_9marker_on = true ∧
      bZ.sudo_5Board_8bench_on = true ∧
      bZ.sudo_5Board_8bench_to = (2 : Int) ∧
      bZ.sudo_5Board_5bench =
        embed (laneFold n (n - k) (combStrip n bench z)) ∧
      (laneFold n (n - k) (combStrip n bench z)).take n = fieldCube n k bench z ∧
      bZ.sudo_5Board_4home[0]? = some (embed (fieldCube n k bench x)) ∧
      bZ.sudo_5Board_4home[1]? = some (embed (fieldCube n k bench y)) ∧
      ∀ i, n ≤ i → ∀ hi : i < (laneFold n (n - k) (combStrip n bench z)).length,
        (laneFold n (n - k) (combStrip n bench z))[i] = 0 := by
  have hseat := pointFeed_seat a hn0 hnb hgap0 hnFit hfitC3 hpeg hfitMv hfitSl hbenchFit
  have hcube := seatAt_cube a z hhome2 hheld2 hz hzt hn0 hspan h3 hnFit hbenchFit hfitC3
    hfm hfold hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  rw [frobenius_point_bottom a z hyt hy hheld2 hhome2 hz hzt hn0 hnbL hnb hgap0
    hs1 hs2 hfitU hfitC hfitCtrl hfitC3 hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfm hfold
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
  rw [← pointFeed]
  rw [hseat, ← seatAt_cast a, hcube, ok_bind, pure_eq_ok]
  refine ⟨_, rfl, rfl, ?_, ?_, seatAt_lane a z, seatAt_take z n k bench, ?_, ?_, ?_⟩
  · exact seatAt_on a z
  · exact seatAt_to a z
  · exact flag_cube_home0 a z
  · exact flag_cube_home1 a z
  · intro i hi hii
    have hlen : (laneFold n (n - k) (combStrip n bench z)).length = bench := by
      rw [laneFold_length n (n - k) (combStrip n bench z)
          (by rw [combStrip_length]; exact hnb), combStrip_length]
    have hbi : i < bench := by rw [← hlen]; exact hii
    have hc0 := cube_off_high z n k bench hn0 hgap0 i hi hbi
    exact (coeff_eq_get (laneFold n (n - k) (combStrip n bench z)) i hii).symm.trans
      (by simpa using hc0)

end EcbsLink2.Link2
