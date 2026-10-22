/-
  One live cell hands the next cell a `RunFrame`. `marker_lift` picks the
  script marker up, `frobenius_affine` cubes homes 0 and 1, and the control
  row, the ladder, the base point, and ops slots 2 and 3 stay. The new
  accumulator is that cube. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusRead
import EcbsLink2.Link2.CopyLay
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.WalkCharge

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- A Frobenius plus the three homes the next invert copies still fits in the
    move charge of one live cell. -/
theorem frob_move_le_walk (t : Spec.Tier) :
    cubeCharge t.n t.benchlen + 3 * t.n ≤ walkCharge t := by
  unfold cubeCharge walkCharge cellMoveCharge tailMoveCap
  omega

theorem frob_slide_le_cell (t : Spec.Tier) :
    slideCharge t.n ≤ cellSlideCharge t := by
  unfold slideCharge cellSlideCharge tailSlideCap
  omega

theorem frob_ctrl_le_cell (t : Spec.Tier) :
    5 ≤ cellCtrlCharge t := by
  unfold cellCtrlCharge
  omega

theorem frob_ops_le_cell (t : Spec.Tier) :
    2 ≤ cellOpsCharge t := by
  unfold cellOpsCharge
  omega

theorem geomFit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m := by
  have hbig : 4 * (1000000 * 1000001) + 40 * 1000001 ≤ 9223372036854775807 := by
    decide
  have hp : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hn (by omega)
  have h2 : 2 * (n * (n + 1)) ≤ 2 * (1000000 * 1000001) := Nat.mul_le_mul_left 2 hp
  have h12 : 12 * bench ≤ 12 * 1000001 := Nat.mul_le_mul_left 12 hb
  have h24 : 24 * n ≤ 24 * 1000000 := Nat.mul_le_mul_left 24 hn
  have hsum : 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ≤
      4 * (1000000 * 1000001) + 40 * 1000001 := by omega
  unfold FitsLen i64MaxNat
  omega

theorem smallCap (n bench : Nat) :
    n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    bench ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    3 * (n - 1) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

theorem at_eq {α : Type} {a b : Array α} (h : a = b) {i : Nat}
    (ha : i < a.size) (hb : i < b.size) : a[i] = b[i] := by
  subst h
  rfl

theorem set_ne {α : Type} (a : Array α) (i j : Nat) (hi : i < a.size)
    (v : α) (hne : i ≠ j) (hj : j < a.size) :
    (a.set ⟨i, hi⟩ v)[j]'(by rw [Array.size_set]; exact hj) = a[j] :=
  Array.getElem_set_ne a ⟨i, hi⟩ v (by rw [Array.size_set]; exact hj) hne

theorem set_eq {α : Type} (a : Array α) (i : Nat) (hi : i < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[i]'(by rw [Array.size_set]; exact hi) = v := by
  simp [Array.getElem_set]

/-- Bumping slot 1 by two keeps every slot a natural under `cap + 2`. Slot 1
    becomes `cubeOps + 2`. Slots 2 and 3 keep the `+ 1` headroom. -/
theorem opsRoom_bump (ops ops' : Array Int) (cap cubeOps : Nat)
    (hsz : ops'.size = ops.size)
    (h1 : ∀ (h : 1 < ops'.size), ops'[1]'h = Int.ofNat (cubeOps + 2))
    (hrest : ∀ i (hi : i < ops.size), i ≠ 1 →
      ops'[i]'(by rw [hsz]; exact hi) = ops[i]'hi)
    (hroom : ∀ i (hi : i < ops.size),
      ∃ c, ops[i]'hi = Int.ofNat c ∧
        (if i = 2 then c + 1 else if i = 3 then c + 1 else c) ≤ cap)
    (hcap : cubeOps ≤ cap) :
    ∀ i (hi : i < ops'.size),
      ∃ c, ops'[i]'hi = Int.ofNat c ∧
        (if i = 2 then c + 1 else if i = 3 then c + 1 else c) ≤ cap + 2 := by
  intro i hi
  by_cases hone : i = 1
  · subst hone
    refine ⟨cubeOps + 2, h1 hi, ?_⟩
    simp only [if_neg (by decide : (1 : Nat) ≠ 2), if_neg (by decide : (1 : Nat) ≠ 3)]
    omega
  · have hi0 : i < ops.size := by rw [← hsz]; exact hi
    obtain ⟨c, hc, hle⟩ := hroom i hi0
    refine ⟨c, (hrest i hi0 hone).trans hc, Nat.le_trans hle (Nat.le_add_right cap 2)⟩

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

/-- The board `frobenius_affine` returns once the across cube is `DownAcross`. -/
def cellOut
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  settleBoard (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

attribute [irreducible] cellOut

theorem cell_frob
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hs1 : 1 < script) (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hnbL : n ≤ a.laneX.length) (hnb : n ≤ bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hMv : FitsLen (moves + cubeCharge n bench))
    (hSl : FitsLen (slides + slideCharge n)) :
    Ecbs.frobenius_affine b = .ok (cellOut a) := by
  have hfit := up_settle_fit a hMv hSl
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hfield := across_up_field a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit hnbL
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  have hset := up_close a hn0 hgap0 hnb hnFit hfit.1 hfit.2.1 hfit.2.2
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
  show (Ecbs.settle (upFlag a) >>= fun r => pure r) = Except.ok (cellOut a)
  rw [hset, ok_bind, pure_eq_ok, cellOut]

theorem cellOut_szH
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4home.size = 8 := by
  have h := settle_home_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)
  rw [cellOut, h, Array.size_set, upFlag, up_board_home_size]

theorem cellOut_szD
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4held.size = 8 := by
  have h := settle_held_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)
  rw [cellOut, h, Array.size_set, upFlag, up_board_held_size]

theorem cellOut_h0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    0 < (cellOut a).sudo_5Board_4home.size := by
  rw [cellOut_szH a]; decide

theorem cellOut_h1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (cellOut a).sudo_5Board_4home.size := by
  rw [cellOut_szH a]; decide

theorem cellOut_d0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    0 < (cellOut a).sudo_5Board_4held.size := by
  rw [cellOut_szD a]; decide

theorem cellOut_d1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (cellOut a).sudo_5Board_4held.size := by
  rw [cellOut_szD a]; decide

theorem cellOut_bench
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_8bench_on = false := by
  rw [cellOut]
  exact settle_bench_off (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem cellOut_on
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_9marker_on = true := by
  rw [cellOut]
  rw [settle_marker_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a), upFlag]

theorem cellOut_homeSet
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4home =
      (upFlag a).sudo_5Board_4home.set ⟨1, upFlagH a⟩
        (embed ((upLane n k bench y).take n)) := by
  rw [cellOut]
  exact settle_home_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem cellOut_heldSet
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4held =
      (upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true := by
  rw [cellOut]
  exact settle_held_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem cellOut_home0_flag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (cellOut a).sudo_5Board_4home.size)
    (h0f : 0 < (upFlag a).sudo_5Board_4home.size) :
    (cellOut a).sudo_5Board_4home[0] = (upFlag a).sudo_5Board_4home[0] := by
  exact (at_eq (cellOut_homeSet a) h0 (by rw [Array.size_set]; exact h0f)).trans
    (set_ne (upFlag a).sudo_5Board_4home 1 0 (upFlagH a)
      (embed ((upLane n k bench y).take n)) (by decide) h0f)

theorem cellOut_home0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (cellOut a).sudo_5Board_4home.size) :
    (cellOut a).sudo_5Board_4home[0] = embed (fieldCube n k bench x) := by
  have h0f : 0 < (upFlag a).sudo_5Board_4home.size := by
    rw [upFlag, up_board_home_size a]; decide
  have hflag : (upFlag a).sudo_5Board_4home[0] = (upBoard a).sudo_5Board_4home[0] := rfl
  exact (cellOut_home0_flag a h0 h0f).trans (hflag.trans (up_home0 a))

theorem cellOut_home1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h1 : 1 < (cellOut a).sudo_5Board_4home.size) :
    (cellOut a).sudo_5Board_4home[1] = embed (fieldCube n k bench y) := by
  have h1f : 1 < (upFlag a).sudo_5Board_4home.size := by
    rw [upFlag, up_board_home_size a]; decide
  have hget := set_eq (upFlag a).sudo_5Board_4home 1 (upFlagH a)
    (embed ((upLane n k bench y).take n))
  exact ((at_eq (cellOut_homeSet a) h1 (by rw [Array.size_set]; exact h1f)).trans hget).trans
    (congrArg embed (upLane_take n k bench y))

theorem cellOut_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h1 : 1 < (cellOut a).sudo_5Board_4held.size) :
    (cellOut a).sudo_5Board_4held[1] = true := by
  have h1f : 1 < (upFlag a).sudo_5Board_4held.size := by
    rw [upFlag, up_board_held_size a]; decide
  exact (at_eq (cellOut_heldSet a) h1 (by rw [Array.size_set]; exact h1f)).trans
    (set_eq (upFlag a).sudo_5Board_4held 1 (upFlag1 a) true)

theorem cellOut_held0_flag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (cellOut a).sudo_5Board_4held.size)
    (h0f : 0 < (upFlag a).sudo_5Board_4held.size) :
    (cellOut a).sudo_5Board_4held[0] = (upFlag a).sudo_5Board_4held[0] := by
  exact (at_eq (cellOut_heldSet a) h0 (by rw [Array.size_set]; exact h0f)).trans
    (set_ne (upFlag a).sudo_5Board_4held 1 0 (upFlag1 a) true (by decide) h0f)

theorem upBoard_heldEq
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4held =
      (upSettled a).sudo_5Board_4held.set ⟨1, up1D a⟩ false := by
  rw [upBoard]
  exact cube_off_held (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem upBoard_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (upBoard a).sudo_5Board_4held.size)
    (h0s : 0 < (upSettled a).sudo_5Board_4held.size) :
    (upBoard a).sudo_5Board_4held[0] = (upSettled a).sudo_5Board_4held[0] := by
  exact (at_eq (upBoard_heldEq a) h0 (by rw [Array.size_set]; exact h0s)).trans
    (set_ne (upSettled a).sudo_5Board_4held 1 0 (up1D a) false (by decide) h0s)

theorem upSettled_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (upSettled a).sudo_5Board_4held.size) :
    (upSettled a).sudo_5Board_4held[0] = true := by
  have hset := settle_held_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  exact (at_eq hset h0 (by rw [Array.size_set]; exact upD a)).trans
    (set_eq (upFeed a).sudo_5Board_4held 0 (upD a) true)

theorem cellOut_held0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h0 : 0 < (cellOut a).sudo_5Board_4held.size) :
    (cellOut a).sudo_5Board_4held[0] = true := by
  have h0f : 0 < (upFlag a).sudo_5Board_4held.size := by
    rw [upFlag, up_board_held_size a]; decide
  have h0b : 0 < (upBoard a).sudo_5Board_4held.size := by rw [up_board_held_size a]; decide
  have h0s : 0 < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size a]; decide
  have hflag : (upFlag a).sudo_5Board_4held[0] = (upBoard a).sudo_5Board_4held[0] := rfl
  exact (cellOut_held0_flag a h0 h0f).trans
    (hflag.trans ((upBoard_held0 a h0b h0s).trans (upSettled_held0 a h0s)))

theorem cellOut_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) := by
  rw [cellOut]
  exact settle_moves_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem cellOut_slides
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (upSl a + 2 * pegCount ((upLane n k bench y).take n)) := by
  rw [cellOut]
  exact settle_slides_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem cellOut_ctrl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ((ctrl + 1) + 2) := by
  have hfeed : (upFeed a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat ((ctrl + 1) + 2) := by
    simp [upFeed, markerUpFeed]
  have hset : (upSettled a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (upFeed a).sudo_5Board_4cost.sudo_5Costs_4ctrl :=
    settle_ctrl_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hcube : (upBoard a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (upSettled a).sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    rw [upBoard, cube_off_ctrl]
  have hflag : (upFlag a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_4ctrl := rfl
  have hout : (cellOut a).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      (upFlag a).sudo_5Board_4cost.sudo_5Costs_4ctrl := by
    rw [cellOut]
    exact settle_ctrl_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
  exact hout.trans (hflag.trans (hcube.trans (hset.trans hfeed)))

theorem cellOut_mark
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_6marker = Int.ofNat 1 := by
  have hfeed : (upFeed a).sudo_5Board_6marker = Int.ofNat 1 := by
    simp [upFeed, markerUpFeed]
  have hset : (upSettled a).sudo_5Board_6marker = (upFeed a).sudo_5Board_6marker :=
    settle_ix_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hcube : (upBoard a).sudo_5Board_6marker = (upSettled a).sudo_5Board_6marker := by
    rw [upBoard, cube_off_ix]
  have hflag : (upFlag a).sudo_5Board_6marker = (upBoard a).sudo_5Board_6marker := rfl
  have hout : (cellOut a).sudo_5Board_6marker = (upFlag a).sudo_5Board_6marker := by
    rw [cellOut]
    exact settle_ix_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
  exact hout.trans (hflag.trans (hcube.trans (hset.trans hfeed)))

theorem cellOut_mx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max mx 1) 2) := by
  have hfeed : (upFeed a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max mx 1) 2) := by
    simp [upFeed, markerUpFeed]
  have hset : (upSettled a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (upFeed a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max :=
    settle_mx_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hcube : (upBoard a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (upSettled a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
    rw [upBoard, cube_off_mx]
  have hflag : (upFlag a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := rfl
  have hout : (cellOut a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      (upFlag a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
    rw [cellOut]
    exact settle_mx_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
  exact hout.trans (hflag.trans (hcube.trans (hset.trans hfeed)))

theorem cellOut_peak
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (if upPk2 a < countHeld
          ((upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true) 7
        then countHeld ((upFlag a).sudo_5Board_4held.set ⟨1, upFlag1 a⟩ true) 7
        else upPk2 a) := by
  rw [cellOut]
  exact settle_peak_eq (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a) (by rw [upFlag]; exact up_board_pk a)

theorem cellOut_opsLt
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (cellOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  have hset := settle_ops (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)
  rw [cellOut, hset, upFlag, upBoard, cube_off_ops, Array.size_set]
  exact up_ops_lt a

theorem cellOut_opsSet
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops := by
  rw [cellOut]
  exact settle_ops (upFlag a) 1 ⟨upFlagH a, upFlag1 a⟩ (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)

theorem upBoard_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops =
      (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, up_ops_lt a⟩
        (Int.ofNat ((cOps + 1) + 1)) := by
  rw [upBoard]
  exact cube_off_ops (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem cellOut_ops1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (h1 : 1 < (cellOut a).sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (cellOut a).sudo_5Board_4cost.sudo_5Costs_3ops[1] = Int.ofNat (cOps + 2) := by
  have hszU : 1 < (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upFlag, upBoard_ops a, Array.size_set]; exact up_ops_lt a
  have hAt := at_eq (cellOut_opsSet a) h1 hszU
  have hflag : (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'hszU =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by
        rw [upBoard_ops a, Array.size_set]; exact up_ops_lt a) := rfl
  have hAtB := at_eq (upBoard_ops a)
    (by rw [upBoard_ops a, Array.size_set]; exact up_ops_lt a)
    (by rw [Array.size_set]; exact up_ops_lt a)
  have hget := set_eq (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops 1 (up_ops_lt a)
    (Int.ofNat ((cOps + 1) + 1))
  exact hAt.trans (hflag.trans (hAtB.trans (hget.trans (congrArg Int.ofNat (by omega)))))

/-- The across cube `cube_down_eq` names, so fields it does not write are the
    input board's. -/
def acrossBoard (b0 : Ecbs.Board) (xs : List Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size) : Ecbs.Board :=
  { cubeOffBoard (markerDownFeed b0 ctrl mx) 0 0 xs n k moves hole bench peak peakS cOps
      hops hF hHome with
    sudo_5Board_9marker_on := true }

theorem raw_home
    (b0 : Ecbs.Board) (xs : List Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4home =
      (markerDownFeed b0 ctrl mx).sudo_5Board_4home.set ⟨0, hHome⟩ #[] := by
  rw [acrossBoard, cube_off_home]

theorem raw_held
    (b0 : Ecbs.Board) (xs : List Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4held =
      (markerDownFeed b0 ctrl mx).sudo_5Board_4held.set ⟨0, hF⟩ false := by
  rw [acrossBoard, cube_off_held]

theorem raw_ops
    (b0 : Ecbs.Board) (xs : List Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size)
    (hHome : 0 < b0.sudo_5Board_4home.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
      (markerDownFeed b0 ctrl mx).sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩
        (Int.ofNat (cOps + 1)) := by
  rw [acrossBoard, cube_off_ops]

theorem feed_home (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_4home = b0.sudo_5Board_4home := rfl

theorem feed_held (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_4held = b0.sudo_5Board_4held := rfl

theorem feed_ops (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_4cost.sudo_5Costs_3ops =
      b0.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

theorem feed_ladder (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_6ladder = b0.sudo_5Board_6ladder := rfl

theorem feed_l0 (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_7ladder0 = b0.sudo_5Board_7ladder0 := rfl

theorem feed_nr (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_6nrungs = b0.sudo_5Board_6nrungs := rfl

theorem feed_park (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_9park_hole = b0.sudo_5Board_9park_hole := rfl

theorem feed_from (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_11parked_from = b0.sudo_5Board_11parked_from := rfl

theorem feed_ridx (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_8rung_idx = b0.sudo_5Board_8rung_idx := rfl

theorem feed_row (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_3row = b0.sudo_5Board_3row := rfl

theorem feed_t0 (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_6tally0 = b0.sudo_5Board_6tally0 := rfl

theorem feed_tlen (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_9tally_len = b0.sudo_5Board_9tally_len := rfl

theorem feed_tmax (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_4cost.sudo_5Costs_9tally_max =
      b0.sudo_5Board_4cost.sudo_5Costs_9tally_max := rfl

theorem feed_high (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_4cost.sudo_5Costs_15control_highest =
      b0.sudo_5Board_4cost.sudo_5Costs_15control_highest := rfl

theorem feed_tier (b0 : Ecbs.Board) (ctrl mx : Nat) :
    (markerDownFeed b0 ctrl mx).sudo_5Board_1t = b0.sudo_5Board_1t := rfl

theorem cube_ladder (b0 : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b0.sudo_5Board_4held.size) (hHome : src < b0.sudo_5Board_4home.size) :
    (cubeOffBoard b0 dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6ladder =
      b0.sudo_5Board_6ladder := rfl

theorem on_ladder (b0 : Ecbs.Board) (xs : List Nat)
    (n k moves hole bench peak peakS cOps ctrl mx : Nat)
    (hops : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : 0 < b0.sudo_5Board_4held.size) (hHome : 0 < b0.sudo_5Board_4home.size) :
    (acrossBoard b0 xs n k moves hole bench peak peakS cOps ctrl mx hops hF hHome).sudo_5Board_6ladder =
      b0.sudo_5Board_6ladder := by
  rw [acrossBoard, cube_ladder, feed_ladder]

theorem settle_same (b0 : Ecbs.Board) (home : Nat) (hin : HomeIn b0 home)
    (xs : List Nat) (n moves slides peak : Nat)
    {α : Type} (proj : Ecbs.Board → α)
    (hp : proj { b0 with
        sudo_5Board_4home := b0.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b0.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b0.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n))
          sudo_5Costs_4peak :=
            Int.ofNat (countHeld (b0.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7) } } = proj b0)
    (hk : proj { b0 with
        sudo_5Board_4home := b0.sudo_5Board_4home.set ⟨home, hin.hH⟩ (embed (xs.take n))
        sudo_5Board_4held := b0.sudo_5Board_4held.set ⟨home, hin.hD⟩ true
        sudo_5Board_8bench_on := false
        sudo_5Board_4cost := { b0.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount (xs.take n))
          sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount (xs.take n)) } } = proj b0) :
    proj (settleBoard b0 home hin.hH hin.hD xs n moves slides peak) = proj b0 := by
  by_cases hpk : peak < countHeld (b0.sudo_5Board_4held.set ⟨home, hin.hD⟩ true) 7
  · rw [settle_peak b0 home hin xs n moves slides peak hpk]; exact hp
  · rw [settle_keep b0 home hin xs n moves slides peak hpk]; exact hk

end

end EcbsLink2.Link2
