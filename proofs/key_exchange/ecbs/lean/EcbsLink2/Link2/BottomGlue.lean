/-
  `frobenius_point` ends at the bottom comb. The slid board's proof indices
  are identified without unfolding `pointFeed`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem settle_cast (b : Ecbs.Board) (home : Nat)
    (hH₁ hH₂ : home < b.sudo_5Board_4home.size)
    (hD₁ hD₂ : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (eH : hH₁ = hH₂) (eD : hD₁ = hD₂) :
    settleBoard b home hH₁ hD₁ xs n moves slides peak =
      settleBoard b home hH₂ hD₂ xs n moves slides peak := by
  cases eH
  cases eD
  rfl

theorem seatAt_cast
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    seatAt a =
      settleBoard (pointFeed a) 1 (upFlagH a) (upFlag1 a)
        (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) := by
  rw [seatAt]

/-- The bottom of `frobenius_point`. Home 2 was `z`; the bench prefix is
    `fieldCube` of that bottom, and the marker stays on. -/
theorem frobenius_bottom_field
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
      (laneFold n (n - k) (combStrip n bench z)).take n = fieldCube n k bench z := by
  have hseat := pointFeed_seat a hn0 hnb hgap0 hnFit hfitC3 hpeg hfitMv hfitSl hbenchFit
  have hcube := seatAt_cube a z hhome2 hheld2 hz hzt hn0 hspan h3 hnFit hbenchFit hfitC3
    hfm hfold hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  rw [frobenius_point_bottom a z hyt hy hheld2 hhome2 hz hzt hn0 hnbL hnb hgap0
    hs1 hs2 hfitU hfitC hfitCtrl hfitC3 hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfm hfold
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
  rw [← pointFeed]
  rw [hseat, ← seatAt_cast a, hcube, ok_bind, pure_eq_ok]
  refine ⟨_, rfl, rfl, ?_, ?_, seatAt_lane a z, seatAt_take z n k bench⟩
  · exact seatAt_on a z
  · exact seatAt_to a z

end EcbsLink2.Link2
