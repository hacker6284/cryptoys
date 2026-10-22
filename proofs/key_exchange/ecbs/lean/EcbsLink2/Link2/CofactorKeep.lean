/-
  What the cofactor cube leaves for the next chord cell.
  `down_across` and the up-field close stay in their own declarations.
  This file reads a `DownAcross` record: the bottom is home 2, and the chord
  counter is ops slot 3. Slot 1 is the cube counter.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusRead

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem idx_eq_local {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem get_irrel {α : Type} (a : Array α) (i : Nat) (h1 h2 : i < a.size) {v : α}
    (h : a[i]'h1 = v) : a[i]'h2 = v := by
  have hp : h1 = h2 := Subsingleton.elim h1 h2
  cases hp
  exact h

private theorem set_idx_ne {α : Type} (a : Array α) (i j : Nat) (hi : i < a.size)
    (v val : α) (hne : i ≠ j) (hj : j < a.size) (h : a[j]'hj = val) :
    (a.set ⟨i, hi⟩ v)[j]'(by rw [Array.size_set]; exact hj) = val := by
  have hget := Array.getElem_set_ne a ⟨i, hi⟩ v (by rw [Array.size_set]; exact hj) hne
  exact hget.trans (get_irrel a j hj _ h)

private theorem charge_assoc (moves n bench : Nat) :
    moves + 8 * n + 6 * (bench - n) = moves + (8 * n + 6 * (bench - n)) := by
  omega

private theorem add_two (spent moves n bench : Nat)
    (h : spent ≤ moves + (8 * n + 6 * (bench - n))) :
    spent + 2 * n ≤ moves + 10 * n + 6 * (bench - n) := by
  omega

private theorem span_le (n bench cg : Nat) (h : 3 * (n - 1) + cg < bench) : n ≤ bench := by
  omega

private theorem script_pos (script : Nat) (h : 2 ≤ script) : 0 < script ∧ 1 < script := by
  omega

private theorem shape_n_pos (n w h r : Nat)
    (heq : n = w * h - 1) (hw : 0 < w) (hr : 0 < r) (hlt : r < h) : 0 < n := by
  have hh : 2 ≤ h := by omega
  have hw1 : 1 ≤ w := by omega
  have hprod : 2 ≤ w * h := Nat.mul_le_mul hw1 hh
  omega

private theorem mv_rooms (moves n bench : Nat)
    (h : FitsLen (moves + 8 * n + 6 * (bench - n))) :
    FitsLen n ∧ FitsLen (3 * (n - 1)) ∧ FitsLen (moves + 2 * n) ∧
      FitsLen bench ∧ FitsLen (moves + 2 * n + 3 * (bench - n)) := by
  refine ⟨FitsLen.of_le h (by omega), FitsLen.of_le h (by omega),
    FitsLen.of_le h (by omega), FitsLen.of_le h (by omega),
    FitsLen.of_le h (by omega)⟩

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

/-- The board `frobenius_affine` returns: across cubed, up cubed, bench off. -/
def frobeniusOut
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  settleBoard (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem out_held_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_4held.size = 8 := by
  rw [frobeniusOut, settle_held_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]
  rw [upFlag]
  exact up_board_held_size a

theorem out_home_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_4home.size = 8 := by
  rw [frobeniusOut, settle_home_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set]
  rw [upFlag]
  exact up_board_home_size a

theorem cube_ops_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [frobeniusOut, settle_ops (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [upFlag, upBoard, cube_off_ops, Array.size_set]
  rw [upSettled, settle_ops (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1, upFeed_ops]

/-- `frobenius_affine` is the settle of the up cube. -/
theorem frob_board
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hs1 : 1 < script) (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hspan : 3 * (n - 1) + cg < bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hMv : FitsLen (moves + 8 * n + 6 * (bench - n)))
    (hSl : FitsLen (slides + 4 * n)) :
    Ecbs.frobenius_affine b = .ok (frobeniusOut a) := by
  have hrooms := mv_rooms moves n bench hMv
  have hnb := span_le n bench cg hspan
  have hlenL : n ≤ a.laneX.length := by rw [a.hlenX]; exact hnb
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hMvC : FitsLen (moves + cubeCharge n bench) := by
    rw [cubeCharge, ← charge_assoc]; exact hMv
  have hSlC : FitsLen (slides + slideCharge n) := by rw [slideCharge]; exact hSl
  have hfit := up_settle_fit a hMvC hSlC
  have hfield := across_up_field a hyt hy hn0 hs1 hfitU hfitC hspan hrooms.2.1 hrooms.1
      hrooms.2.2.2.1 hlenL hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  have hset := up_close a hn0 hgap0 hnb hrooms.1 hfit.1 hfit.2.1 hfit.2.2
  unfold Ecbs.frobenius_affine
  rw [show Ecbs.across = (0 : Int) from rfl, show Ecbs.up = (1 : Int) from rfl]
  have hcube0 : Ecbs.cube b (0 : Int) (0 : Int) = .ok a.b1On := a.hcube
  have hup : Ecbs.cube a.b1On (1 : Int) (1 : Int) =
      .ok { upBoard a with sudo_5Board_9marker_on := true } := hfield.1
  rw [hcube0, ok_bind]
  conv =>
    lhs
    dsimp
  rw [hup, ok_bind]
  show (Ecbs.settle (upFlag a) >>= fun r => pure r) = Except.ok (frobeniusOut a)
  rw [show frobeniusOut a = settleBoard (upFlag a) 1 (upFlagH a) (upFlag1 a)
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) from rfl,
    hset, ok_bind, pure_eq_ok]

/-- Homes other than the two cube sources, and ops slots other than slot 1,
    survive both cubes and both settles. -/
theorem held_keep
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (j : Nat) (hj : j < 8) (hz : j ≠ 0) (ho : j ≠ 1) {v : Bool}
    (h : a.b1On.sudo_5Board_4held[j]'(by rw [a.hszDOn]; exact hj) = v) :
    (frobeniusOut a).sudo_5Board_4held[j]'(by rw [out_held_size a]; exact hj) = v := by
  have hjF : j < (upFeed a).sudo_5Board_4held.size := by
    rw [upFeed_held a, a.hszDOn]; exact hj
  have hF : (upFeed a).sudo_5Board_4held[j]'hjF = v :=
    (idx_eq_local (upFeed_held a) j hjF).trans
      (get_irrel _ j (by rw [a.hszDOn]; exact hj) ((upFeed_held a) ▸ hjF) h)
  have heqS := settle_held_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hsetS := set_idx_ne (upFeed a).sudo_5Board_4held 0 j (upD a) true v hz.symm hjF hF
  have hjS : j < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size a]; exact hj
  have hS : (upSettled a).sudo_5Board_4held[j]'hjS = v :=
    (idx_eq_local heqS j hjS).trans
      (get_irrel _ j (by rw [Array.size_set]; exact hjF) (heqS ▸ hjS) hsetS)
  have hcube := cube_off_held (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hsetC := set_idx_ne (upSettled a).sudo_5Board_4held 1 j (up1D a) false v ho.symm hjS hS
  have hUB : (upBoard a).sudo_5Board_4held =
      (upSettled a).sudo_5Board_4held.set ⟨1, up1D a⟩ false := by
    rw [upBoard, hcube]
  have hjU : j < (upBoard a).sudo_5Board_4held.size := by rw [hUB, Array.size_set]; exact hjS
  have hU : (upBoard a).sudo_5Board_4held[j]'hjU = v :=
    (idx_eq_local hUB j hjU).trans
      (get_irrel _ j (by rw [Array.size_set]; exact hjS) (hUB ▸ hjU) hsetC)
  have hflag : (upFlag a).sudo_5Board_4held = (upBoard a).sudo_5Board_4held := rfl
  have hjG : j < (upFlag a).sudo_5Board_4held.size := by rw [hflag]; exact hjU
  have hG : (upFlag a).sudo_5Board_4held[j]'hjG = v :=
    (idx_eq_local hflag j hjG).trans (get_irrel _ j hjU (hflag ▸ hjG) hU)
  have heqF := settle_held_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hsetF := set_idx_ne (upFlag a).sudo_5Board_4held 1 j (upFlag1 a) true v ho.symm hjG hG
  have hjO : j < (frobeniusOut a).sudo_5Board_4held.size := by rw [out_held_size a]; exact hj
  have hOut : (frobeniusOut a).sudo_5Board_4held =
      (upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true := by
    rw [frobeniusOut]; exact heqF
  exact (idx_eq_local hOut j hjO).trans
    (get_irrel _ j (by rw [Array.size_set]; exact hjG) (hOut ▸ hjO) hsetF)

theorem home_keep
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (j : Nat) (hj : j < 8) (hz : j ≠ 0) (ho : j ≠ 1) {v : Array Int}
    (h : a.b1On.sudo_5Board_4home[j]'(by rw [a.hszHOn]; exact hj) = v) :
    (frobeniusOut a).sudo_5Board_4home[j]'(by rw [out_home_size a]; exact hj) = v := by
  have hjF : j < (upFeed a).sudo_5Board_4home.size := by
    rw [upFeed_home a, a.hszHOn]; exact hj
  have hF : (upFeed a).sudo_5Board_4home[j]'hjF = v :=
    (idx_eq_local (upFeed_home a) j hjF).trans
      (get_irrel _ j (by rw [a.hszHOn]; exact hj) ((upFeed_home a) ▸ hjF) h)
  have heqS := settle_home_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hsetS := set_idx_ne (upFeed a).sudo_5Board_4home 0 j (upH a)
      (embed (a.laneX.take n)) v hz.symm hjF hF
  have hjS : j < (upSettled a).sudo_5Board_4home.size := by rw [up_home_size a]; exact hj
  have hS : (upSettled a).sudo_5Board_4home[j]'hjS = v :=
    (idx_eq_local heqS j hjS).trans
      (get_irrel _ j (by rw [Array.size_set]; exact hjF) (heqS ▸ hjS) hsetS)
  have hcube := cube_off_home (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hsetC := set_idx_ne (upSettled a).sudo_5Board_4home 1 j (up1H a) #[] v ho.symm hjS hS
  have hUB : (upBoard a).sudo_5Board_4home =
      (upSettled a).sudo_5Board_4home.set ⟨1, up1H a⟩ #[] := by
    rw [upBoard, hcube]
  have hjU : j < (upBoard a).sudo_5Board_4home.size := by rw [hUB, Array.size_set]; exact hjS
  have hU : (upBoard a).sudo_5Board_4home[j]'hjU = v :=
    (idx_eq_local hUB j hjU).trans
      (get_irrel _ j (by rw [Array.size_set]; exact hjS) (hUB ▸ hjU) hsetC)
  have hflag : (upFlag a).sudo_5Board_4home = (upBoard a).sudo_5Board_4home := rfl
  have hjG : j < (upFlag a).sudo_5Board_4home.size := by rw [hflag]; exact hjU
  have hG : (upFlag a).sudo_5Board_4home[j]'hjG = v :=
    (idx_eq_local hflag j hjG).trans (get_irrel _ j hjU (hflag ▸ hjG) hU)
  have heqF := settle_home_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hsetF := set_idx_ne (upFlag a).sudo_5Board_4home 1 j (upFlagH a)
      (embed ((upLane n k bench y).take n)) v ho.symm hjG hG
  have hjO : j < (frobeniusOut a).sudo_5Board_4home.size := by rw [out_home_size a]; exact hj
  have hOut : (frobeniusOut a).sudo_5Board_4home =
      (upFlag a).sudo_5Board_4home.set ⟨1, upFlagH a⟩
        (embed ((upLane n k bench y).take n)) := by
    rw [frobeniusOut]; exact heqF
  exact (idx_eq_local hOut j hjO).trans
    (get_irrel _ j (by rw [Array.size_set]; exact hjG) (hOut ▸ hjO) hsetF)

theorem ops_keep
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (j : Nat) (hj : j < a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size) (ho : j ≠ 1) {v : Int}
    (h : a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj = v) :
    (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'(by rw [cube_ops_size a]; exact hj) = v := by
  have hjF : j < (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upFeed_ops a]; exact hj
  have hF : (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjF = v :=
    (idx_eq_local (upFeed_ops a) j hjF).trans
      (get_irrel _ j hj ((upFeed_ops a) ▸ hjF) h)
  have heqS := settle_ops (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hjS : j < (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upSettled, heqS]; exact hjF
  have hS : (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjS = v :=
    (idx_eq_local heqS j hjS).trans (get_irrel _ j hjF (heqS ▸ hjS) hF)
  have hcube := cube_off_ops (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hsetC := set_idx_ne (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops 1 j (up_ops_lt a)
      (Int.ofNat ((cOps + 1) + 1)) v ho.symm hjS hS
  have hUB : (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, up_ops_lt a⟩
        (Int.ofNat ((cOps + 1) + 1)) := by
    rw [upBoard, hcube]
  have hjU : j < (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hUB, Array.size_set]; exact hjS
  have hU : (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjU = v :=
    (idx_eq_local hUB j hjU).trans
      (get_irrel _ j (by rw [Array.size_set]; exact hjS) (hUB ▸ hjU) hsetC)
  have hflag : (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops := rfl
  have hjG : j < (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hflag]; exact hjU
  have hG : (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops[j]'hjG = v :=
    (idx_eq_local hflag j hjG).trans (get_irrel _ j hjU (hflag ▸ hjG) hU)
  have heqF := settle_ops (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hjO : j < (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [cube_ops_size a]; exact hj
  have hOut : (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [frobeniusOut]; exact heqF
  exact (idx_eq_local hOut j hjO).trans (get_irrel _ j hjG (hOut ▸ hjO) hG)

theorem out_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_4held[0]'(by rw [out_held_size a]; decide) = true := by
  have heqS := settle_held_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hjS : 0 < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size a]; decide
  have hszSet : 0 < ((upFeed a).sudo_5Board_4held.set ⟨0, upD a⟩ true).size := by
    rw [Array.size_set]; exact upD a
  have hset := Array.getElem_set_eq (upFeed a).sudo_5Board_4held ⟨0, upD a⟩ true rfl hszSet
  have hS : (upSettled a).sudo_5Board_4held[0]'hjS = true :=
    (idx_eq_local heqS 0 hjS).trans (get_irrel _ 0 hszSet (heqS ▸ hjS) hset)
  have hcube := cube_off_held (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hsetC := set_idx_ne (upSettled a).sudo_5Board_4held 1 0 (up1D a) false true (by decide) hjS hS
  have hUB : (upBoard a).sudo_5Board_4held =
      (upSettled a).sudo_5Board_4held.set ⟨1, up1D a⟩ false := by rw [upBoard, hcube]
  have hjU : 0 < (upBoard a).sudo_5Board_4held.size := by rw [hUB, Array.size_set]; exact hjS
  have hU : (upBoard a).sudo_5Board_4held[0]'hjU = true :=
    (idx_eq_local hUB 0 hjU).trans
      (get_irrel _ 0 (by rw [Array.size_set]; exact hjS) (hUB ▸ hjU) hsetC)
  have hflag : (upFlag a).sudo_5Board_4held = (upBoard a).sudo_5Board_4held := rfl
  have hjG : 0 < (upFlag a).sudo_5Board_4held.size := by rw [hflag]; exact hjU
  have hG : (upFlag a).sudo_5Board_4held[0]'hjG = true :=
    (idx_eq_local hflag 0 hjG).trans (get_irrel _ 0 hjU (hflag ▸ hjG) hU)
  have heqF := settle_held_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hsetF := set_idx_ne (upFlag a).sudo_5Board_4held 1 0 (upFlag1 a) true true (by decide) hjG hG
  have hjO : 0 < (frobeniusOut a).sudo_5Board_4held.size := by rw [out_held_size a]; decide
  have hOut : (frobeniusOut a).sudo_5Board_4held =
      (upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true := by
    rw [frobeniusOut]; exact heqF
  exact (idx_eq_local hOut 0 hjO).trans
    (get_irrel _ 0 (by rw [Array.size_set]; exact hjG) (hOut ▸ hjO) hsetF)

theorem out_home0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_4home[0]'(by rw [out_home_size a]; decide) =
      embed (fieldCube n k bench x) := by
  have hU0 := up_home0 a
  have hflag : (upFlag a).sudo_5Board_4home = (upBoard a).sudo_5Board_4home := rfl
  have hjG : 0 < (upFlag a).sudo_5Board_4home.size := by
    rw [hflag, up_board_home_size a]; decide
  have hG : (upFlag a).sudo_5Board_4home[0]'hjG = embed (fieldCube n k bench x) :=
    (idx_eq_local hflag 0 hjG).trans
      (get_irrel _ 0 (by rw [up_board_home_size a]; decide) (hflag ▸ hjG) hU0)
  have heqF := settle_home_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hsetF := set_idx_ne (upFlag a).sudo_5Board_4home 1 0 (upFlagH a)
      (embed ((upLane n k bench y).take n)) (embed (fieldCube n k bench x)) (by decide) hjG hG
  have hjO : 0 < (frobeniusOut a).sudo_5Board_4home.size := by rw [out_home_size a]; decide
  have hOut : (frobeniusOut a).sudo_5Board_4home =
      (upFlag a).sudo_5Board_4home.set ⟨1, upFlagH a⟩
        (embed ((upLane n k bench y).take n)) := by
    rw [frobeniusOut]; exact heqF
  exact (idx_eq_local hOut 0 hjO).trans
    (get_irrel _ 0 (by rw [Array.size_set]; exact hjG) (hOut ▸ hjO) hsetF)

theorem out_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hChord : FitsLen (moves + 10 * n + 6 * (bench - n))) :
    ∃ mvF,
      (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF ∧
      mvF = upMv2 a + 2 * pegCount ((upLane n k bench y).take n) ∧
      FitsLen (mvF + 2 * n) := by
  have hmv := settle_moves_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  let mvF := upMv2 a + 2 * pegCount ((upLane n k bench y).take n)
  refine ⟨mvF, ?_, rfl, ?_⟩
  · rw [frobeniusOut]; exact hmv
  · have hle := (up_out_le a).2.1
    rw [cubeCharge] at hle
    exact FitsLen.of_le hChord (add_two _ moves n bench hle)

theorem out_peak
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    ∃ pkF, (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkF := by
  have hpk : (upFlag a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat (upPk2 a) := by
    rw [upFlag]; exact up_board_pk a
  have h := settle_peak_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a) hpk
  let pkF := if upPk2 a < countHeld
      ((upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true) 7
    then countHeld ((upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true) 7
    else upPk2 a
  refine ⟨pkF, ?_⟩
  rw [frobeniusOut]
  simpa [pkF] using h

theorem out_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (frobeniusOut a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  rw [frobeniusOut, settle_tier_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)]
  rw [upFlag]
  exact up_board_n a

/-- The across cube writes home 0 and ops slot 1. The bottom, base across, and
    ops slot 3 are what that cube read. -/
theorem b1_skip
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (peakS c3 : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = n) (hxt : allTritList x)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hge : 2 ≤ script) (hfitD : FitsLen (ctrl + 1))
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hn0 : 0 < n) (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hspan : 3 * (n - 1) + cg < bench)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hMv : FitsLen (moves + 8 * n + 6 * (bench - n)))
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'hops3 = (c3 : Int)) :
    a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = false ∧
      a.b1On.sudo_5Board_4held[3]'(by rw [a.hszDOn]; decide) = true ∧
      a.b1On.sudo_5Board_4home[3]'(by rw [a.hszHOn]; decide) = embed x ∧
      3 < a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ h3 : 3 < a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops[3] = (c3 : Int)) := by
  have hsp := script_pos script hge
  have hrooms := mv_rooms moves n bench hMv
  have hfit1 : FitsLen (cOps + 1) := FitsLen.of_le hfitC (Nat.le_succ (cOps + 1))
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have hmov : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [hmoves, ofNat_eq_natCast]
  have hpkC : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hpeak, ofNat_eq_natCast]
  have hst : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hstrict, ofNat_eq_natCast]
  let feed := markerDownFeed b ctrl mx
  let cubeB := cubeOffBoard feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  let known := { cubeB with sudo_5Board_9marker_on := true }
  have hcube := cube_down_eq b 0 0 x w h r n k moves holeN bench pk peakS cOps cg ctrl mx script
      hmk hoff hm hc hmx hscript hsp.1 hfitD hops hop1 hfit1 h0D h0H hheld0 hhome0 h7
      hst hpkC hn0 hn hx hrooms.1 hmov hbl hcg hspan hrooms.2.1 hrooms.2.2.1
      hhole hxt hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm
      hrooms.2.2.2.1 hrooms.2.2.2.2
  have hcube' : Ecbs.cube b ((0 : Nat) : Int) ((0 : Nat) : Int) = .ok known := by
    simpa [feed, cubeB, known] using hcube
  have heq : a.b1On = known := by
    have h := a.hcube.symm.trans hcube'
    injection h
  have hheldK : known.sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨0, h0D⟩ false := by
    simp [known, cubeB, feed, cube_off_held, markerDownFeed]
  have hhomeK : known.sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨0, h0H⟩ #[] := by
    simp [known, cubeB, feed, cube_off_home, markerDownFeed]
  have hopsK : known.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := by
    simp [known, cubeB, feed, cube_off_ops, markerDownFeed]
  have h2b : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3b : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have hset2 := set_idx_ne b.sudo_5Board_4held 0 2 h0D false false (by decide) h2b h2
  have hset3 := set_idx_ne b.sudo_5Board_4held 0 3 h0D false true (by decide) h3b h3t
  have hsetH := set_idx_ne b.sudo_5Board_4home 0 3 h0H (#[] : Array Int) (embed x) (by decide) h3H h3a
  have hsetO := set_idx_ne b.sudo_5Board_4cost.sudo_5Costs_3ops 1 3 hops
      (Int.ofNat (cOps + 1)) (c3 : Int) (by decide) hops3 hop3
  have h2a : 2 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
  have h3aD : 3 < a.b1On.sudo_5Board_4held.size := by rw [a.hszDOn]; decide
  have h3aH : 3 < a.b1On.sudo_5Board_4home.size := by rw [a.hszHOn]; decide
  have hheldA : a.b1On.sudo_5Board_4held = known.sudo_5Board_4held := by rw [heq]
  have hhomeA : a.b1On.sudo_5Board_4home = known.sudo_5Board_4home := by rw [heq]
  have hopsA : a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops =
      known.sudo_5Board_4cost.sudo_5Costs_3ops := by rw [heq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (idx_eq_local (hheldA.trans hheldK) 2 h2a).trans
      (get_irrel _ 2 (by rw [Array.size_set]; exact h2b)
        ((hheldA.trans hheldK) ▸ h2a) hset2)
  · exact (idx_eq_local (hheldA.trans hheldK) 3 h3aD).trans
      (get_irrel _ 3 (by rw [Array.size_set]; exact h3b)
        ((hheldA.trans hheldK) ▸ h3aD) hset3)
  · exact (idx_eq_local (hhomeA.trans hhomeK) 3 h3aH).trans
      (get_irrel _ 3 (by rw [Array.size_set]; exact h3H)
        ((hhomeA.trans hhomeK) ▸ h3aH) hsetH)
  · rw [heq, hopsK, Array.size_set]; exact hops3
  · intro h3
    exact (idx_eq_local (hopsA.trans hopsK) 3 h3).trans
      (get_irrel _ 3 (by rw [Array.size_set]; exact hops3)
        ((hopsA.trans hopsK) ▸ h3) hsetO)

end

/-- The cubed cofactor root. The bottom stays empty, ops slot 3 is untouched,
    and the move count still has room for one chord add. -/
theorem cube_keep_of
    (b : Ecbs.Board) (x y : List Nat)
    (n k w h r bench cg pk moves slides holeN cOps ctrl mx script peakS c3 : Nat)
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hops3 : 3 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = n) (hy : y.length = n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hmark : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hwT : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhT : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrT : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcgT : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hge : 2 ≤ script) (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hspan : 3 * (n - 1) + cg < bench)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hMv : FitsLen (moves + 8 * n + 6 * (bench - n)))
    (hSl : FitsLen (slides + 4 * n))
    (hChord : FitsLen (moves + 10 * n + 6 * (bench - n)))
    (h2 : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (hop3 : b.sudo_5Board_4cost.sudo_5Costs_3ops[3]'hops3 = (c3 : Int)) :
    ∃ (mvF pkF : Nat),
      Ecbs.frobenius_affine b = .ok (frobeniusOut a) ∧
      (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF ∧
      mvF = upMv2 a + 2 * pegCount ((upLane n k bench y).take n) ∧
      FitsLen (mvF + 2 * n) ∧
      (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkF ∧
      (frobeniusOut a).sudo_5Board_4held.size = 8 ∧
      (frobeniusOut a).sudo_5Board_4home.size = 8 ∧
      (∀ h2 : 2 < (frobeniusOut a).sudo_5Board_4held.size,
        (frobeniusOut a).sudo_5Board_4held[2] = false) ∧
      (∀ h0 : 0 < (frobeniusOut a).sudo_5Board_4held.size,
        (frobeniusOut a).sudo_5Board_4held[0] = true) ∧
      (∀ h0 : 0 < (frobeniusOut a).sudo_5Board_4home.size,
        (frobeniusOut a).sudo_5Board_4home[0] = embed (fieldCube n k bench x)) ∧
      (∀ h3 : 3 < (frobeniusOut a).sudo_5Board_4held.size,
        (frobeniusOut a).sudo_5Board_4held[3] = true) ∧
      (∀ h3 : 3 < (frobeniusOut a).sudo_5Board_4home.size,
        (frobeniusOut a).sudo_5Board_4home[3] = embed x) ∧
      3 < (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ h3 : 3 < (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size,
        (frobeniusOut a).sudo_5Board_4cost.sudo_5Costs_3ops[3] = (c3 : Int)) ∧
      (frobeniusOut a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  have hn0 := shape_n_pos n w h r hnE hw0 hrP hrR
  obtain ⟨h2b, h3b, h3h, hopsB, hopB⟩ :=
    b1_skip a peakS c3 hszH hszD hops hops3 hx hxt hmk hoff
      (by rw [hmark]; decide) hc hmx hscript hge hfitD hop1 hfitC hheld0 hhome0
      hmoves hpeak hstrict hhole hn hk hwT hhT hrT hbl hcgT
      hw0 hh0 hrR hrP hn0 hnE hkLe hgap hspan hsm hnsm hMv h2 h3t h3a hop3
  have hrun := frob_board a hyt hy hn0 (script_pos script hge).2 hfitU hfitC hspan
      hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm hMv hSl
  obtain ⟨mvF, hmv, hdef, hfit⟩ := out_moves a hChord
  obtain ⟨pkF, hpk⟩ := out_peak a
  refine ⟨mvF, pkF, hrun, hmv, hdef, hfit, hpk, out_held_size a, out_home_size a,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, out_n a⟩
  · intro h
    have h2i := get_irrel a.b1On.sudo_5Board_4held 2 (by rw [a.hszDOn]; decide)
        (by rw [a.hszDOn]; exact (by decide : (2 : Nat) < 8)) h2b
    have hbot := held_keep a 2 (by decide) (by decide) (by decide) h2i
    exact get_irrel _ 2 (by rw [out_held_size a]; exact (by decide : (2 : Nat) < 8)) h hbot
  · intro h
    exact get_irrel _ 0 (by rw [out_held_size a]; decide) h (out_held0 a)
  · intro h
    exact get_irrel _ 0 (by rw [out_home_size a]; decide) h (out_home0 a)
  · intro h
    have h3i := get_irrel a.b1On.sudo_5Board_4held 3 (by rw [a.hszDOn]; decide)
        (by rw [a.hszDOn]; exact (by decide : (3 : Nat) < 8)) h3b
    have hkeep := held_keep a 3 (by decide) (by decide) (by decide) h3i
    exact get_irrel _ 3 (by rw [out_held_size a]; exact (by decide : (3 : Nat) < 8)) h hkeep
  · intro h
    have h3i := get_irrel a.b1On.sudo_5Board_4home 3 (by rw [a.hszHOn]; decide)
        (by rw [a.hszHOn]; exact (by decide : (3 : Nat) < 8)) h3h
    have hkeep := home_keep a 3 (by decide) (by decide) (by decide) h3i
    exact get_irrel _ 3 (by rw [out_home_size a]; exact (by decide : (3 : Nat) < 8)) h hkeep
  · rw [cube_ops_size a]; exact hopsB
  · intro h
    have hop := ops_keep a 3 hopsB (by decide) (hopB hopsB)
    exact get_irrel _ 3 (by rw [cube_ops_size a]; exact hopsB) h hop

end EcbsLink2.Link2
