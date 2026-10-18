/-
  The board `frobenius_point` cubes after the up cube. The bench is aimed at
  the up home. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformPoint

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The bottom cube's entry: marker stepped, bench still the cubed up. -/
def pointFeed
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  markerUpFeed (upFlag a) 1 (ctrl + 3) (max (max mx 1) 2)

theorem pointFeed_off
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_9marker_on = false := rfl

theorem pointFeed_on
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_8bench_on = true := up_board_on a

theorem pointFeed_to
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_8bench_to = ((1 : Nat) : Int) := up_board_to a

theorem pointFeed_bench
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_5bench = embed (upLane n k bench y) := (up_field a).1

theorem pointFeed_mv
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (upMv2 a) := up_board_mv a

theorem pointFeed_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := up_board_n a

theorem pointFeed_sl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (upSl a) := up_board_sl a

theorem pointFeed_pk
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat (upPk2 a) := up_board_pk a

theorem pointFeed_held7
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    7 ≤ (pointFeed a).sudo_5Board_4held.size := by
  have h : 7 ≤ (upFlag a).sudo_5Board_4held.size := by
    rw [upFlag, up_board_held_size a]; decide
  exact h

theorem pointFeed_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4held[1]'(upFlag1 a) = false := up_board_empty a

private theorem flag_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [upFlag, upBoard, cube_off_ops, Array.size_set]
  exact up_ops_lt a

theorem pointFeed_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops.size := flag_ops a

private theorem cell_eq_of {α : Type} {a b : Array α} (h : a = b) {i : Nat}
    {ha : i < a.size} {hb : i < b.size} {v : α}
    (hv : b[i]'hb = v) : a[i]'ha = v := by
  subst h
  have : (⟨i, ha⟩ : Fin a.size) = ⟨i, hb⟩ := Fin.ext rfl
  simpa [this] using hv

private theorem flag_op1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(flag_ops a) =
      ((cOps + 2 : Nat) : Int) := by
  have hset := cube_off_ops (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hboard : (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
        (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [upBoard]
  have harr : (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, up_ops_lt a⟩
        (Int.ofNat ((cOps + 1) + 1)) :=
    (show (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops =
        (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops from rfl).trans (hboard.trans hset)
  have hsz : 1 < ((upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, up_ops_lt a⟩
      (Int.ofNat ((cOps + 1) + 1))).size := by
    rw [Array.size_set]; exact up_ops_lt a
  have hget := Array.getElem_set_eq (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops
    ⟨1, up_ops_lt a⟩ (Int.ofNat ((cOps + 1) + 1)) rfl hsz
  exact (cell_eq_of harr hget).trans (congrArg Int.ofNat (by omega))

theorem pointFeed_op1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(pointFeed_ops a) =
      ((cOps + 2 : Nat) : Int) := flag_op1 a

/-- Sliding the cubed up into home 1, then cubing, is the bottom cube.
    The bench is aimed at up, not at the bottom. -/
theorem pointFeed_seat
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hn0 : 0 < n) (hnb : n ≤ bench) (hgap0 : 0 < n - k)
    (hnFit : FitsLen n) (hfitC3 : FitsLen (cOps + 3))
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitMv : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitSl : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)))
    (hbenchFit : FitsLen bench) :
    Ecbs.cube (pointFeed a) ((2 : Nat) : Int) ((2 : Nat) : Int) =
      Ecbs.cube
        (settleBoard (pointFeed a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y)
          n (upMv2 a) (upSl a) (upPk2 a))
        ((2 : Nat) : Int) ((2 : Nat) : Int) := by
  have hlen := upLane_len n k bench y hnb
  have hzero := upLane_zero n k bench y hn0 hgap0 hlen
  have hnle : n ≤ (upLane n k bench y).length := by rw [hlen]; exact hnb
  have hpos : 0 < (upLane n k bench y).length := by rw [hlen]; omega
  have hfitL : FitsLen (upLane n k bench y).length := by rw [hlen]; exact hbenchFit
  exact cube_settle_other (pointFeed a) 2 2 1 (upLane n k bench y) n (upMv2 a) (upSl a)
    (upPk2 a) (cOps + 2) (pointFeed_off a) (pointFeed_on a) (pointFeed_to a)
    (upFlagH a) (upFlag1 a) (pointFeed_held7 a) (pointFeed_held1 a) (pointFeed_bench a)
    (pointFeed_n a) hpos hnle hzero hnFit hfitL (pointFeed_mv a) (pointFeed_sl a)
    (pointFeed_pk a) hpeg hfitMv hfitSl (pointFeed_ops a) (pointFeed_op1 a)
    (by rw [show (cOps + 2) + 1 = cOps + 3 by omega]; exact hfitC3)

end EcbsLink2.Link2
