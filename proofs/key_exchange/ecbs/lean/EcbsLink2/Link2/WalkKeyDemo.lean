/-
  `walk_key` on a demo tier. The walk is `walk_chord`, and a true flag is
  `point_of` of across and up.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.WalkScope
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- Demo's key walk is the chord walk. A true flag reads the point in across and up. -/
theorem walk_key_demo_chord (cells : Array Int) (x y : Array Int)
    (b0 b1 b2 : Ecbs.Board)
    (hN : new_board demo_tier = .ok b0)
    (h1 : put b0 base_across x = .ok b1)
    (h2 : put b1 base_up y = .ok b2)
    (hdemo : b2.sudo_5Board_1t.sudo_4Tier_4demo = true) :
    walk_key demo_tier cells { sudo_5Point_1x := x, sudo_5Point_1y := y } =
      (do
          let r ← (do
            let r ← walk_chord b2 cells
            let live := r.1.1
            let ok := r.1.2
            let b := r.2
            let flag ← (if live then pure ok else pure false)
            pure (flag, b))
          match r with
          | (flag, b) =>
            if !flag then
              pure (none : Option Point)
            else
              do
                let p ← point_of b across up
                pure (some p)) := by
  unfold walk_key
  conv => lhs; zeta
  rw [hN, ok_bind, h1, ok_bind, h2, ok_bind]
  rw [walk_and_finish_demo b2 cells hdemo]

end EcbsLink2.Link2
