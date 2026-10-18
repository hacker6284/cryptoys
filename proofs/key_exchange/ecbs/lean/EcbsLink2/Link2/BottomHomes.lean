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

end EcbsLink2.Link2
