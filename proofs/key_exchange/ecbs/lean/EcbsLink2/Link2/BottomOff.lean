/-
  After the cubed up is slid home, the bottom cube is the bench-off comb.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomField
import EcbsLink2.Link2.MulSettle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def seatBoard
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  settleBoard (pointFeed a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y)
    n (upMv2 a) (upSl a) (upPk2 a)

theorem seat_off
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatBoard a).sudo_5Board_9marker_on = false := by
  rw [seatBoard, settle_marker_eq (pointFeed a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_off a

theorem seat_bench_off
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatBoard a).sudo_5Board_8bench_on = false := by
  rw [seatBoard]
  exact settle_bench_off (pointFeed a) 1 ⟨upFlagH a, upFlag1 a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seat_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatBoard a).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) := by
  rw [seatBoard]
  exact settle_moves_eq (pointFeed a) 1 ⟨upFlagH a, upFlag1 a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)

theorem seat_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatBoard a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  rw [seatBoard, settle_tier_eq (pointFeed a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_n a

theorem seat_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (seatBoard a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [seatBoard, settle_ops (pointFeed a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_ops a

/-- `settle` does not change the cube counter. The board stays a variable so the
    array equality is not unfolded. -/
theorem settle_ops_get1 (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) (v : Int)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = v) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops[1]'
        (by rw [settle_ops b home ⟨hH, hD⟩ xs n moves slides peak]; exact hops) = v := by
  exact (get_eq_of_array (settle_ops b home ⟨hH, hD⟩ xs n moves slides peak) 1
      (by rw [settle_ops b home ⟨hH, hD⟩ xs n moves slides peak]; exact hops)).trans hop

end EcbsLink2.Link2
