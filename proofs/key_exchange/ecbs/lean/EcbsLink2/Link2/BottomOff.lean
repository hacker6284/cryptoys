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

/-- The same fact through `getElem?`, so the two bound proofs are not unified. -/
theorem settle_ops_get1?
    (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) (v : Int)
    (hop : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some v) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some v := by
  rw [settle_ops b home ⟨hH, hD⟩ xs n moves slides peak]
  exact hop

/-- Size proofs sealed on `pointFeed`, so a later use does not unfold it to
    match `upFlag`. -/
theorem pointFeed_homeIx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (pointFeed a).sudo_5Board_4home.size := upFlagH a

theorem pointFeed_heldIx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (pointFeed a).sudo_5Board_4held.size := upFlag1 a

theorem pointFeed_op1?
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some (((cOps + 2 : Nat) : Int)) := by
  rw [Array.getElem?_eq_getElem (pointFeed_ops a)]
  exact congrArg some (pointFeed_op1 a)

section
attribute [local irreducible] pointFeed

/-- The cube counter after the slide. `pointFeed` is irreducible, the goal is
    the `settleBoard` expression `seatBoard` unfolds to, and the read is
    `getElem?`. -/
theorem seat_op1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some (((cOps + 2 : Nat) : Int)) := by
  exact settle_ops_get1? (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) _ (pointFeed_op1? a)

theorem seat_opsIx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [settle_ops (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  exact pointFeed_ops a

theorem seat_op1_get
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (settleBoard (pointFeed a) 1 (pointFeed_homeIx a) (pointFeed_heldIx a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)).sudo_5Board_4cost.sudo_5Costs_3ops[1]'
        (seat_opsIx a) =
      (((cOps + 2 : Nat) : Int)) := by
  have h := seat_op1 a
  rw [Array.getElem?_eq_getElem (seat_opsIx a)] at h
  exact Option.some.inj h

end

end EcbsLink2.Link2
