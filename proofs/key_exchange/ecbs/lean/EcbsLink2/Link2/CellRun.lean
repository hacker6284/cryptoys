/-
  The `RunFrame` on the board `cell_to_frame` returns. Held flags other than
  across and up are the flags of the lifted board. Ops slots other than 1 are
  the incoming slots; slot 1 grew by two. Strict and hole are the values the
  up cube writes, because that cube does write them.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CellFrame

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Held flags other than across and up. The two settles write 0 and 1, and
    the two cubes clear those same homes. -/
theorem affine_held {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hjF : j < (cellOut cell.a).sudo_5Board_4held.size)
    (hjU : j < (upFlag cell.a).sudo_5Board_4held.size)
    (hjB : j < (upBoard cell.a).sudo_5Board_4held.size)
    (hjS : j < (upSettled cell.a).sudo_5Board_4held.size)
    (hjE : j < (upFeed cell.a).sudo_5Board_4held.size)
    (hj1n : j < cell.a.b1On.sudo_5Board_4held.size)
    (hjL : j < cell.bL.sudo_5Board_4held.size)
    (hBL : cell.bL.sudo_5Board_4held = b.sudo_5Board_4held)
    (hj0b : j < b.sudo_5Board_4held.size) :
    (cellOut cell.a).sudo_5Board_4held[j] = b.sudo_5Board_4held[j] := by
  have h1 := (at_eq (cellOut_heldSet cell.a) hjF (by rw [Array.size_set]; exact hjU)).trans
    (set_ne (upFlag cell.a).sudo_5Board_4held 1 j (upFlag1 cell.a) true (by omega) hjU)
  have hflag : (upFlag cell.a).sudo_5Board_4held[j] = (upBoard cell.a).sudo_5Board_4held[j] := rfl
  have hcube := cube_off_held (upSettled cell.a) 1 1 accY t.n t.k (upMv cell.a) cell.a.hole1
    t.benchlen (upPk cell.a) cell.a.peakS1 (cell.cubeOps + 1) (up_ops_lt cell.a) (up1D cell.a)
    (up1H cell.a)
  have h2 := (at_eq (by rw [upBoard]; exact hcube) hjB (by rw [Array.size_set]; exact hjS)).trans
    (set_ne (upSettled cell.a).sudo_5Board_4held 1 j (up1D cell.a) false (by omega) hjS)
  have hset := settle_held_eq (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n
    cell.a.mv1 slides cell.a.pk1
  have h3 := (at_eq hset hjS (by rw [Array.size_set]; exact hjE)).trans
    (set_ne (upFeed cell.a).sudo_5Board_4held 0 j (upD cell.a) true (by omega) hjE)
  have hfeed := at_eq (upFeed_held cell.a) hjE hj1n
  have hraw := raw_held cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
    (ctrl + 1) mx cell.hops cell.h0D cell.h0H
  have hheldOn : cell.a.b1On.sudo_5Board_4held =
      (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
        (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4held :=
    congrArg (fun b => b.sudo_5Board_4held) cell.onEq
  have hszA : j < (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
      (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4held.size := by
    rw [hraw, Array.size_set, feed_held]
    exact hjL
  have hOn := at_eq hheldOn hj1n hszA
  have hfeedSz : j < (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4held.size := by
    rw [feed_held]; exact hjL
  have h4 := (hOn.trans (at_eq hraw hszA (by rw [Array.size_set]; exact hfeedSz))).trans
    (set_ne (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4held 0 j cell.h0D false
      (by omega) hfeedSz)
  have hdown := at_eq (feed_held cell.bL (ctrl + 1) mx) (by rw [feed_held]; exact hjL) hjL
  have hbase := at_eq hBL hjL hj0b
  exact h1.trans (hflag.trans (h2.trans (h3.trans (hfeed.trans (h4.trans (hdown.trans hbase))))))

/-- Ops slots other than 1. Both cubes write slot 1; the settles do not write ops. -/
theorem affine_ops {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj1 : j ≠ 1)
    (hjF : j < (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hjU : j < (upFlag cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hjS : j < (upSettled cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hjE : j < (upFeed cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hj1n : j < cell.a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hjL : j < cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hBL : cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hj0b : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_3ops[j] =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have h1 := at_eq (cellOut_opsSet cell.a) hjF hjU
  have hflag : (upFlag cell.a).sudo_5Board_4cost.sudo_5Costs_3ops[j] =
      (upBoard cell.a).sudo_5Board_4cost.sudo_5Costs_3ops[j] := rfl
  have hboard := upBoard_ops cell.a
  have h2 := (at_eq hboard hjU (by rw [Array.size_set]; exact hjS)).trans
    (set_ne (upSettled cell.a).sudo_5Board_4cost.sudo_5Costs_3ops 1 j (up_ops_lt cell.a)
      (Int.ofNat ((cell.cubeOps + 1) + 1)) (by omega) hjS)
  have hset := settle_ops (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n
    cell.a.mv1 slides cell.a.pk1
  have h3 := at_eq hset hjS hjE
  have hfeed := at_eq (upFeed_ops cell.a) hjE hj1n
  have hraw := raw_ops cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
    (ctrl + 1) mx cell.hops cell.h0D cell.h0H
  have hopsOn : cell.a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops =
      (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
        (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4cost.sudo_5Costs_3ops :=
    congrArg (fun b => b.sudo_5Board_4cost.sudo_5Costs_3ops) cell.onEq
  have hszA : j < (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
      (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hraw, Array.size_set, feed_ops]
    exact hjL
  have hOn := at_eq hopsOn hj1n hszA
  have hfeedSz : j < (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [feed_ops]; exact hjL
  have h4 := (hOn.trans (at_eq hraw hszA (by rw [Array.size_set]; exact hfeedSz))).trans
    (set_ne (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4cost.sudo_5Costs_3ops 1 j
      cell.hops (Int.ofNat (cell.cubeOps + 1)) (by omega) hfeedSz)
  have hdown := at_eq (feed_ops cell.bL (ctrl + 1) mx) (by rw [feed_ops]; exact hjL) hjL
  have hbase := at_eq hBL hjL hj0b
  exact h1.trans (hflag.trans (h2.trans (h3.trans (hfeed.trans (h4.trans (hdown.trans hbase))))))

/-- Strict after the up cube. The across cube stored its strict in `peakS1`;
    the up cube raises that by the held-count it sees, and the closing settle
    does not write strict. -/
theorem cell_strict {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak cell.a.peakS1
        (countHeld (upSettled cell.a).sudo_5Board_4held 7)) := by
  rw [cellOut]
  rw [settle_strict_eq (upFlag cell.a) 1 ⟨upFlagH cell.a, upFlag1 cell.a⟩
    (upLane t.n t.k t.benchlen accY) t.n (upMv2 cell.a) (upSl cell.a) (upPk2 cell.a)]
  rw [upFlag, upBoard, cube_off_strict]

/-- Hole after the up cube. The closing settle does not write the hole counter. -/
theorem cell_hole {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole cell.a.hole1
        (topIdx (combStrip t.n t.benchlen accY))) := by
  rw [cellOut]
  rw [settle_hole_eq (upFlag cell.a) 1 ⟨upFlagH cell.a, upFlag1 cell.a⟩
    (upLane t.n t.k t.benchlen accY) t.n (upMv2 cell.a) (upSl cell.a) (upPk2 cell.a)]
  rw [upFlag, upBoard, cube_off_hole]

/-- The ladder is not written by the lift, the cubes, or the settles. -/
theorem ladder_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_6ladder = b.sudo_5Board_6ladder) :
    (cellOut cell.a).sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  refine affine_card cell (fun b => b.sudo_5Board_6ladder) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_6ladder) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl
  · intro _ _ _
    rfl
  · intro _ _ _ _
    rfl
  · intro _
    rfl

theorem held_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj : j < 8) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hBL : cell.bL.sudo_5Board_4held = b.sudo_5Board_4held) (hsz : b.sudo_5Board_4held.size = 8) :
    (cellOut cell.a).sudo_5Board_4held[j]'(lt_of_size (cellOut_szD cell.a) hj) =
      b.sudo_5Board_4held[j]'(lt_of_size hsz hj) := by
  exact affine_held cell j hj0 hj1
    (lt_of_size (cellOut_szD cell.a) hj)
    (by rw [upFlag, up_board_held_size cell.a]; exact hj)
    (by rw [up_board_held_size cell.a]; exact hj)
    (by rw [up_held_size cell.a]; exact hj)
    (by rw [upFeed_held cell.a, cell.a.hszDOn]; exact hj)
    (by rw [cell.a.hszDOn]; exact hj)
    (by rw [hBL, hsz]; exact hj)
    hBL
    (lt_of_size hsz hj)

theorem home_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj : j < 8) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hBL : cell.bL.sudo_5Board_4home = b.sudo_5Board_4home) (hsz : b.sudo_5Board_4home.size = 8) :
    (cellOut cell.a).sudo_5Board_4home[j]'(lt_of_size (cellOut_szH cell.a) hj) =
      b.sudo_5Board_4home[j]'(lt_of_size hsz hj) := by
  exact affine_home cell j hj0 hj1
    (lt_of_size (cellOut_szH cell.a) hj)
    (by rw [upFlag, up_board_home_size cell.a]; exact hj)
    (by rw [up_board_home_size cell.a]; exact hj)
    (by rw [up_home_size cell.a]; exact hj)
    (by rw [upFeed_home cell.a, cell.a.hszHOn]; exact hj)
    (by rw [cell.a.hszHOn]; exact hj)
    (by rw [hBL, hsz]; exact hj)
    hBL
    (lt_of_size hsz hj)

theorem tier_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_1t = b.sudo_5Board_1t) :
    (cellOut cell.a).sudo_5Board_1t = b.sudo_5Board_1t := by
  refine affine_card cell (fun b => b.sudo_5Board_1t) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_1t) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem high_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  refine affine_card cell (fun b => b.sudo_5Board_4cost.sudo_5Costs_15control_highest) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk
      (fun b => b.sudo_5Board_4cost.sudo_5Costs_15control_highest) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem row_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_3row = b.sudo_5Board_3row) :
    (cellOut cell.a).sudo_5Board_3row = b.sudo_5Board_3row := by
  refine affine_card cell (fun b => b.sudo_5Board_3row) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_3row) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem tally_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len) :
    (cellOut cell.a).sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  refine affine_card cell (fun b => b.sudo_5Board_9tally_len) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_9tally_len) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem t0_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_6tally0 = b.sudo_5Board_6tally0) :
    (cellOut cell.a).sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
  refine affine_card cell (fun b => b.sudo_5Board_6tally0) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_6tally0) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem tmax_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b.sudo_5Board_4cost.sudo_5Costs_9tally_max := by
  refine affine_card cell (fun b => b.sudo_5Board_4cost.sudo_5Costs_9tally_max) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk
      (fun b => b.sudo_5Board_4cost.sudo_5Costs_9tally_max) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem l0_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0) :
    (cellOut cell.a).sudo_5Board_7ladder0 = b.sudo_5Board_7ladder0 := by
  refine affine_card cell (fun b => b.sudo_5Board_7ladder0) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_7ladder0) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem nr_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_6nrungs = b.sudo_5Board_6nrungs) :
    (cellOut cell.a).sudo_5Board_6nrungs = b.sudo_5Board_6nrungs := by
  refine affine_card cell (fun b => b.sudo_5Board_6nrungs) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_6nrungs) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem park_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_9park_hole = b.sudo_5Board_9park_hole) :
    (cellOut cell.a).sudo_5Board_9park_hole = b.sudo_5Board_9park_hole := by
  refine affine_card cell (fun b => b.sudo_5Board_9park_hole) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_9park_hole) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem from_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_11parked_from = b.sudo_5Board_11parked_from) :
    (cellOut cell.a).sudo_5Board_11parked_from = b.sudo_5Board_11parked_from := by
  refine affine_card cell (fun b => b.sudo_5Board_11parked_from) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_11parked_from) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem ridx_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hL : cell.bL.sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx) :
    (cellOut cell.a).sudo_5Board_8rung_idx = b.sudo_5Board_8rung_idx := by
  refine affine_card cell (fun b => b.sudo_5Board_8rung_idx) ?_ ?_ ?_ ?_ ?_ hL
  · intro b0 home hin xs n mv sl pk
    exact settle_same b0 home hin xs n mv sl pk (fun b => b.sudo_5Board_8rung_idx) rfl rfl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl

theorem out_ops_size {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (hBL : cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  have hset := cellOut_opsSet cell.a
  have hboard := upBoard_ops cell.a
  have hsettle := settle_ops (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n
    cell.a.mv1 slides cell.a.pk1
  have hfeed := upFeed_ops cell.a
  have hraw := raw_ops cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
    (ctrl + 1) mx cell.hops cell.h0D cell.h0H
  have hOn := congrArg (fun b => b.sudo_5Board_4cost.sudo_5Costs_3ops) cell.onEq
  have hsz1 := congrArg Array.size hset
  have hsz2 : (upFlag cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      (upBoard cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := rfl
  have hsz3 : (upBoard cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      (upSettled cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    (congrArg Array.size hboard).trans (Array.size_set _ _ _)
  have hsz4 : (upSettled cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      (upFeed cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upSettled]; exact congrArg Array.size hsettle
  have hsz5 := congrArg Array.size hfeed
  have hsz6 := congrArg Array.size hOn
  have hsz7 : (acrossBoard cell.bL accX t.n t.k moves hole t.benchlen peak peakS cell.cubeOps
      (ctrl + 1) mx cell.hops cell.h0D cell.h0H).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      (markerDownFeed cell.bL (ctrl + 1) mx).sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    (congrArg Array.size hraw).trans (Array.size_set _ _ _)
  have hsz8 := congrArg Array.size (feed_ops cell.bL (ctrl + 1) mx)
  exact hsz1.trans (hsz2.trans (hsz3.trans (hsz4.trans (hsz5.trans (hsz6.trans
    (hsz7.trans (hsz8.trans (congrArg Array.size hBL))))))))

theorem ops_kept {b : Ecbs.Board} {t : Spec.Tier} {accX accY : List Nat}
    {peak moves slides hole peakS ctrl mx opsCap : Nat}
    (cell : AffineCell b t accX accY peak moves slides hole peakS ctrl mx opsCap)
    (j : Nat) (hj1 : j ≠ 1) (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hBL : cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops) :
    (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'(by
        rw [out_ops_size cell hBL]; exact hj) =
      b.sudo_5Board_4cost.sudo_5Costs_3ops[j] := by
  have hsz := out_ops_size cell hBL
  have hjF : j < (cellOut cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hsz]; exact hj
  have hjU : j < (upFlag cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [← cellOut_opsSet cell.a]; exact hjF
  have hjB : j < (upBoard cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show (upFlag cell.a).sudo_5Board_4cost.sudo_5Costs_3ops =
        (upBoard cell.a).sudo_5Board_4cost.sudo_5Costs_3ops from rfl] at hjU
    exact hjU
  have hjS : j < (upSettled cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upBoard_ops cell.a, Array.size_set] at hjB
    exact hjB
  have hjE : j < (upFeed cell.a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upSettled] at hjS
    rw [settle_ops (upFeed cell.a) 0 ⟨upH cell.a, upD cell.a⟩ cell.a.laneX t.n
      cell.a.mv1 slides cell.a.pk1] at hjS
    exact hjS
  have hj1n : j < cell.a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [← upFeed_ops cell.a]; exact hjE
  have hjL : j < cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hBL]; exact hj
  exact affine_ops cell j hj1 hjF hjU hjS hjE hj1n hjL hBL hj

/-- The output board is a `RunFrame` for the cubed accumulator. Held flags other
    than 0 and 1 are the incoming flags. Ops slots 2 and 3 are the incoming
    slots. Strict and hole are the values the up cube writes. -/
theorem cell_run_frame (b : Ecbs.Board) (t : Spec.Tier)
    (baseX accX baseY accY : List Nat) (fr : RunFrame b t baseX accX)
    (hOk : BoardOk t) (sat : TierSat t) (hsh : TierShape t)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hY : fr.y4 = baseY) (hA : fr.y1 = accY)
    (hf4 : fr.flag4 = true) (hf1 : fr.flag1 = true)
    (hyA : accY.length = t.n) (htriY : allTritList accY)
    (hMove : FitsLen (fr.moves + cubeCharge t.n t.benchlen + 3 * t.n))
    (hSlide : FitsLen (fr.slides + slideCharge t.n))
    (hCtrl : FitsLen (fr.ctrl + 5))
    (hOps : FitsLen (fr.opsCap + 2)) :
    ∃ bL bF, ∃ fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX),
      Ecbs.marker_lift b = .ok bL ∧
      Ecbs.frobenius_affine bL = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      fr'.y1 = fieldCube t.n t.k t.benchlen accY ∧
      fr'.y4 = baseY ∧
      fr'.flag1 = true ∧
      fr'.flag4 = true ∧
      fr'.ctrl = fr.ctrl + 4 ∧
      fr'.mark = 1 ∧
      fr'.cOps = fr.cOps ∧
      fr'.chordOps = fr.chordOps ∧
      fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen ∧
      fr'.slides ≤ fr.slides + slideCharge t.n := by
  obtain ⟨cell⟩ := cell_affine b t baseX accX accY fr hOk sat hsh hmk hA hf1 hyA htriY
    hMove hSlide hCtrl hOps
  have href := marker_lift_refines b fr.mark fr.ctrl fr.hmark fr.hctrl
    (FitsLen.of_le hCtrl (by omega))
  have hBLeq : cell.bL = { b with
      sudo_5Board_6marker := -1
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_4ctrl := Int.ofNat (fr.ctrl + 1) } } :=
    Except.ok.inj (cell.liftEq.symm.trans href)
  have hHeldL : cell.bL.sudo_5Board_4held = b.sudo_5Board_4held := by rw [hBLeq]
  have hHomeL : cell.bL.sudo_5Board_4home = b.sudo_5Board_4home := by rw [hBLeq]
  have hOpsL : cell.bL.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [hBLeq]
  let bF := cellOut cell.a
  have hszH := cellOut_szH cell.a
  have hszD := cellOut_szD cell.a
  have hnb : t.n ≤ t.benchlen := by have h := sat.cube_span; omega
  have hlenA : (fieldCube t.n t.k t.benchlen accX).length = t.n :=
    fieldCube_length t.n t.k t.benchlen accX hnb
  have htriA : allTritList (fieldCube t.n t.k t.benchlen accX) :=
    fieldCube_trits t.n t.k t.benchlen accX fr.triA (by have h := sat.cube_span; omega) hsh.k_le
  have h0 : 0 < bF.sudo_5Board_4home.size := lt_of_size hszH (by decide)
  have h1 : 1 < bF.sudo_5Board_4home.size := lt_of_size hszH (by decide)
  have hd0 : 0 < bF.sudo_5Board_4held.size := lt_of_size hszD (by decide)
  have hd1 : 1 < bF.sudo_5Board_4held.size := lt_of_size hszD (by decide)
  have hheld (j : Nat) (hj : j < 8) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
      bF.sudo_5Board_4held[j]'(lt_of_size hszD hj) =
        b.sudo_5Board_4held[j]'(lt_of_size fr.szD hj) :=
    held_kept cell j hj hj0 hj1 hHeldL fr.szD
  have hhome (j : Nat) (hj : j < 8) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
      bF.sudo_5Board_4home[j]'(lt_of_size hszH hj) =
        b.sudo_5Board_4home[j]'(lt_of_size fr.szH hj) :=
    home_kept cell j hj hj0 hj1 hHomeL fr.szH
  have hctrl : bF.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (fr.ctrl + 4) := by
    have h := cellOut_ctrl cell.a
    have hsum : ((fr.ctrl + 1) + 1) + 2 = fr.ctrl + 4 := by omega
    simpa [hsum] using h
  obtain ⟨_, hMle, hSle⟩ := up_out_le cell.a
  have hmvN := cellOut_moves cell.a
  have hslN := cellOut_slides cell.a
  let mvN := upMv2 cell.a + 2 * pegCount ((upLane t.n t.k t.benchlen accY).take t.n)
  let slN := upSl cell.a + 2 * pegCount ((upLane t.n t.k t.benchlen accY).take t.n)
  let pkN := if upPk2 cell.a < countHeld
      ((upFlag cell.a).sudo_5Board_4held.set ⟨1, upFlag1 cell.a⟩ true) 7
    then countHeld ((upFlag cell.a).sudo_5Board_4held.set ⟨1, upFlag1 cell.a⟩ true) 7
    else upPk2 cell.a
  let stN := raisedPeak cell.a.peakS1 (countHeld (upSettled cell.a).sudo_5Board_4held 7)
  let hoN := raisedHole cell.a.hole1 (topIdx (combStrip t.n t.benchlen accY))
  have hszOps := out_ops_size cell hOpsL
  have hsz2 : 2 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszOps]; exact fr.ops2
  have hsz3 : 3 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszOps]; exact fr.ops3
  let fr' : RunFrame bF t baseX (fieldCube t.n t.k t.benchlen accX) := {
    szH := hszH
    szD := hszD
    bench := cellOut_bench cell.a
    held5 := by
      exact (hheld 5 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.held5)
    held6 := by
      exact (hheld 6 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.held6)
    held2 := by
      exact (hheld 2 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.held2)
    held0 := cellOut_held0 cell.a hd0
    home0 := cellOut_home0 cell.a h0
    held3 := by
      exact (hheld 3 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.held3)
    home3 := by
      exact (hhome 3 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.home3)
    y1 := fieldCube t.n t.k t.benchlen accY
    y4 := baseY
    flag1 := true
    flag4 := true
    home1 := cellOut_home1 cell.a h1
    held1 := cellOut_held1 cell.a hd1
    home4 := by
      have h := (hhome 4 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.home4)
      simpa [hY] using h
    held4 := by
      have h := (hheld 4 (by decide) (by decide) (by decide)).trans (idx_irrel.trans fr.held4)
      simpa [hf4] using h
    mark := 1
    mx := max (max fr.mx 1) 2
    hmark := cellOut_mark cell.a
    hmx := cellOut_mx cell.a
    lenX := fr.lenX
    lenA := hlenA
    triX := fr.triX
    triA := htriA
    tier := by rw [tier_kept cell (by rw [hBLeq])]; exact fr.tier
    moves := mvN
    slides := slN
    peak := pkN
    ctrl := fr.ctrl + 4
    high := fr.high
    cOps := fr.cOps
    chordOps := fr.chordOps
    opsCap := fr.opsCap + 2
    peakS := stN
    hole := hoN
    hmoves := hmvN
    hslides := hslN
    hpeak := cellOut_peak cell.a
    hctrl := hctrl
    hhigh := by rw [high_kept cell (by rw [hBLeq])]; exact fr.hhigh
    tmax := fr.tmax
    htally := by rw [tally_kept cell (by rw [hBLeq])]; exact fr.htally
    ht0 := by rw [t0_kept cell (by rw [hBLeq])]; exact fr.ht0
    hrow := by rw [row_kept cell (by rw [hBLeq])]; exact fr.hrow
    htmax := by rw [tmax_kept cell (by rw [hBLeq])]; exact fr.htmax
    hStart := fr.hStart
    hlad := by rw [ladder_kept cell (by rw [hBLeq])]; exact fr.hlad
    hl0 := by rw [l0_kept cell (by rw [hBLeq])]; exact fr.hl0
    hnr := by rw [nr_kept cell (by rw [hBLeq])]; exact fr.hnr
    hpark := by rw [park_kept cell (by rw [hBLeq])]; exact fr.hpark
    hfrom := by rw [from_kept cell (by rw [hBLeq])]; exact fr.hfrom
    hridx := by rw [ridx_kept cell (by rw [hBLeq])]; exact fr.hridx
    hstrict := cell_strict cell
    hhole := cell_hole cell
    ops2 := hsz2
    ops3 := hsz3
    hop2 := by
      have h := ops_kept cell 2 (by decide) fr.ops2 hOpsL
      exact idx_irrel.trans (h.trans fr.hop2)
    hop3 := by
      have h := ops_kept cell 3 (by decide) fr.ops3 hOpsL
      exact idx_irrel.trans (h.trans fr.hop3)
    fitInv := fr.fitInv
    fitChord := fr.fitChord
    fitCtrl := hCtrl
    fitRoom := by
      apply FitsLen.of_le hMove
      have hle : mvN ≤ fr.moves + cubeCharge t.n t.benchlen := by
        simpa [mvN, cubeCharge] using hMle
      omega
    opsRoom := by
      intro i hi
      have hi0 : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hszOps]; exact hi
      by_cases hone : i = 1
      · subst hone
        refine ⟨cell.cubeOps + 2, ?_, ?_⟩
        · exact idx_irrel.trans (cellOut_ops1 cell.a (by rw [hszOps]; exact hi0))
        · simp only [if_neg (by decide : (1 : Nat) ≠ 2), if_neg (by decide : (1 : Nat) ≠ 3)]
          exact Nat.add_le_add_right cell.capLe 2
      · have h := ops_kept cell i hone hi0 hOpsL
        obtain ⟨c, hc, hle⟩ := fr.opsRoom i hi0
        refine ⟨c, ?_, Nat.le_trans hle (Nat.le_add_right _ 2)⟩
        exact (idx_irrel.trans h).trans hc
  }
  have hmove : fr'.moves ≤ fr.moves + cubeCharge t.n t.benchlen := by
    simpa [fr', mvN, cubeCharge] using hMle
  have hslide : fr'.slides ≤ fr.slides + slideCharge t.n := by
    simpa [fr', slN, slideCharge] using hSle
  exact ⟨cell.bL, bF, fr', cell.liftEq, cell.frobEq, cellOut_on cell.a,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmove, hslide⟩

end EcbsLink2.Link2
