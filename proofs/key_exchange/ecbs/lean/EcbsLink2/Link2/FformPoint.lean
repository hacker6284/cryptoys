/-
  The first two cubes of `frobenius_point`. Across and up are cubed, and the
  bench still holds the cubed up. The bottom cube is the next cell.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusRead

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `frobenius_point` is the across cube, the up cube, then the bottom cube. -/
theorem frobenius_point_cubes (b : Ecbs.Board) :
    Ecbs.frobenius_point b =
      (Ecbs.cube b Ecbs.across Ecbs.across >>= fun b1 =>
        Ecbs.cube b1 Ecbs.up Ecbs.up >>= fun b2 =>
          Ecbs.cube b2 Ecbs.bottom Ecbs.bottom >>= fun b3 =>
            pure b3) := by
  unfold Ecbs.frobenius_point
  conv => lhs; zeta

/-- The across cube and the up cube. The board they leave is `upFlag`:
    the bench is on, aimed at up, and holds the cubed up. -/
theorem point_across_up
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hs1 : 1 < script) (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hnb : n ≤ a.laneX.length)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    (Ecbs.cube b Ecbs.across Ecbs.across >>= fun b1 =>
        Ecbs.cube b1 Ecbs.up Ecbs.up) =
      .ok (upFlag a) := by
  rw [show Ecbs.across = (0 : Int) from rfl, show Ecbs.up = (1 : Int) from rfl]
  have hcube0 : Ecbs.cube b (0 : Int) (0 : Int) = .ok a.b1On := a.hcube
  have hup :=
    (across_up_field a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit hnb
      hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm).1
  rw [hcube0, ok_bind]
  simpa [upFlag] using hup

end EcbsLink2.Link2
