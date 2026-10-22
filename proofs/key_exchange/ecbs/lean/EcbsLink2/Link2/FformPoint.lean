/-
  `frobenius_point`: across, then up, then the bottom.
  The bottom cube settles the cubed up and folds the bottom the across cube left.
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

private def flag2D
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (upFlag a).sudo_5Board_4held.size := by
  rw [upFlag, up_board_held_size a]; decide

private def flag2H
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    2 < (upFlag a).sudo_5Board_4home.size := by
  rw [upFlag, up_board_home_size a]; decide

/-- The marker, control, and script fields the bottom cube reads off `upFlag`. -/
private theorem flag_marker
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_6marker = Int.ofNat 1 := by
  rw [upFlag, upBoard, cube_off_ix, upSettled,
    settle_ix_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1,
    upFeed, markerUpFeed]

private theorem flag_ctrl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 3) := by
  rw [upFlag, upBoard, cube_off_ctrl, upSettled,
    settle_ctrl_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1,
    upFeed, markerUpFeed]

private theorem flag_mx
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max (max mx 1) 2) := by
  rw [upFlag, upBoard, cube_off_mx, upSettled,
    settle_mx_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1,
    upFeed, markerUpFeed]

private theorem flag_script
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
  rw [upFlag, upBoard, cube_off_tier, upSettled,
    settle_tier_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1, upFeed_tier a]
  exact a.hsOn

private theorem flag_w
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
  rw [upFlag, upBoard, cube_off_tier, up_w]

private theorem flag_h
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
  rw [upFlag, upBoard, cube_off_tier, up_h]

private theorem flag_r
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
  rw [upFlag, upBoard, cube_off_tier, up_r]

private theorem flag_k
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
  rw [upFlag, upBoard, cube_off_tier, up_k]

private theorem flag_bl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
  rw [upFlag, upBoard, cube_off_tier, up_bl]

private theorem flag_cg
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
  rw [upFlag, upBoard, cube_off_tier, up_cg]

private theorem flag_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upFlag a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [upFlag, upBoard, cube_off_ops, Array.size_set]
  exact up_ops_lt a

private theorem cell_eq_of_local {α : Type} {a b : Array α} (h : a = b) {i : Nat}
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
  exact (cell_eq_of_local harr hget).trans (congrArg Int.ofNat (by omega))

private theorem flag_strict
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7) : Int) := by
  have h := cube_off_strict (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  rw [show (upFlag a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (upBoard a).sudo_5Board_4cost.sudo_5Costs_11peak_strict from rfl, upBoard, h]
  rfl

private theorem flag_hole
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole a.hole1 (topIdx (combStrip n bench y))) := by
  rw [upFlag, upBoard]
  exact cube_off_hole (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

private theorem idx_eq_local {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- The up cube writes home 1 and settles home 0. Held 2 stays the across cube's. -/
theorem bottom_held
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hheld : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true) :
    (upFlag a).sudo_5Board_4held[2]'(flag2D a) = true := by
  have hcube := cube_off_held (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hszC : 2 < (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4held.size := by
    rw [hcube, Array.size_set, up_held_size]; decide
  have hget := idx_eq_local hcube 2 hszC
  have hne : (1 : Nat) ≠ 2 := by decide
  simp only [Array.getElem_set, hne] at hget
  have hszS : 2 < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size]; decide
  have hsettle := settle_held_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hgetS := idx_eq_local hsettle 2 hszS
  have hne0 : (0 : Nat) ≠ 2 := by decide
  simp only [Array.getElem_set, hne0] at hgetS
  have hszF : 2 < (upFeed a).sudo_5Board_4held.size := by
    rw [upFeed_held]; rw [a.hszDOn]; decide
  have hgetF := idx_eq_local (upFeed_held a) 2 hszF
  have hflag : (upFlag a).sudo_5Board_4held = (upBoard a).sudo_5Board_4held := rfl
  have hboard : (upBoard a).sudo_5Board_4held =
      (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
        (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4held := by
    rw [upBoard]
  have hgetFlag := idx_eq_local hflag 2 (flag2D a)
  have hgetBoard := idx_eq_local hboard 2 (by rw [up_board_held_size]; decide)
  exact hgetFlag.symm.trans (hgetBoard.trans (hget.trans (hgetS.trans (hgetF.trans hheld))))

/-- Home 2 stays the bottom the across cube left. -/
theorem bottom_home
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hhome : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z) :
    (upFlag a).sudo_5Board_4home[2]'(flag2H a) = embed z := by
  have hcube := cube_off_home (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hszC : 2 < (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4home.size := by
    rw [hcube, Array.size_set, up_home_size]; decide
  have hget := idx_eq_local hcube 2 hszC
  have hne : (1 : Nat) ≠ 2 := by decide
  simp only [Array.getElem_set, hne] at hget
  have hszS : 2 < (upSettled a).sudo_5Board_4home.size := by rw [up_home_size]; decide
  have hsettle := settle_home_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hgetS := idx_eq_local hsettle 2 hszS
  have hne0 : (0 : Nat) ≠ 2 := by decide
  simp only [Array.getElem_set, hne0] at hgetS
  have hszF : 2 < (upFeed a).sudo_5Board_4home.size := by
    rw [upFeed_home]; rw [a.hszHOn]; decide
  have hgetF := idx_eq_local (upFeed_home a) 2 hszF
  have hflag : (upFlag a).sudo_5Board_4home = (upBoard a).sudo_5Board_4home := rfl
  have hboard : (upBoard a).sudo_5Board_4home =
      (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
        (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4home := by
    rw [upBoard]
  have hgetFlag := idx_eq_local hflag 2 (flag2H a)
  have hgetBoard := idx_eq_local hboard 2 (by rw [up_board_home_size]; decide)
  exact hgetFlag.symm.trans (hgetBoard.trans (hget.trans (hgetS.trans (hgetF.trans hhome))))

/-- The bottom cube. The bench still holds the cubed up and is aimed at up.
    Cubing the bottom settles that up home, then folds the bottom onto the bench.
    That bottom is the one the across cube left. -/
theorem point_bottom
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z)
    (hz : z.length = n) (hzt : allTritList z)
    (hn0 : 0 < n) (hnb : n ≤ bench) (hgap0 : 0 < n - k)
    (hs2 : 2 < script) (hfitCtrl : FitsLen (ctrl + 5)) (hfitC3 : FitsLen (cOps + 3))
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
    Ecbs.cube (upFlag a) ((2 : Nat) : Int) ((2 : Nat) : Int) =
      (do
        let r ← Ecbs.cube
          (markerUpFeed (upFlag a) 1 (ctrl + 3) (max (max mx 1) 2))
          ((2 : Nat) : Int) ((2 : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  have hheldF := bottom_held a hheld2
  have hhomeF := bottom_home a z hhome2
  let lane := upLane n k bench y
  have hlen := upLane_len n k bench y hnb
  have hzero := upLane_zero n k bench y hn0 hgap0 hlen
  have hnle : n ≤ lane.length := by rw [hlen]; exact hnb
  have hfitL : FitsLen lane.length := by rw [hlen]; exact hbenchFit
  have hmk : (upFlag a).sudo_5Board_9marker_on = true := rfl
  have hon : (upFlag a).sudo_5Board_8bench_on = true := by rw [upFlag]; exact up_board_on a
  have hto : (upFlag a).sudo_5Board_8bench_to = ((1 : Nat) : Int) := by
    rw [upFlag]; exact up_board_to a
  have hempty : (upFlag a).sudo_5Board_4held[1]'(upFlag1 a) = false := up_board_empty a
  have hbench : (upFlag a).sudo_5Board_5bench = embed lane := by
    rw [upFlag]; exact (up_field a).1
  have hmv : (upFlag a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (upMv2 a) := by
    rw [upFlag]; exact up_board_mv a
  have hsl : (upFlag a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (upSl a) := by
    rw [upFlag]; exact up_board_sl a
  have hpk : (upFlag a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat (upPk2 a) := by
    rw [upFlag]; exact up_board_pk a
  have hn : (upFlag a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [upFlag]; exact up_board_n a
  have h7 : 7 ≤ (upFlag a).sudo_5Board_4held.size := by
    rw [upFlag, up_board_held_size]; decide
  let peakS2 := raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7)
  let hole2 := raisedHole a.hole1 (topIdx (combStrip n bench y))
  exact cube_bench_up (upFlag a) 2 2 1 z lane w h r n k (upMv2 a) (upSl a) hole2 bench
    (upPk2 a) peakS2 (cOps + 2) cg 1 (ctrl + 3) (max (max mx 1) 2) script
    hmk hon (flag_marker a) (flag_ctrl a) (flag_mx a) (flag_script a)
    hs2 (fits_small (by decide))
    ((show ctrl + 5 = (ctrl + 3) + 2 by omega) ▸ hfitCtrl) (fits_small (by decide))
    (flag_ops a) (flag_op1 a)
    ((show cOps + 3 = (cOps + 2) + 1 by omega) ▸ hfitC3)
    (by decide) (flag2D a) (flag2H a) hheldF hhomeF
    (upFlag1 a) (upFlagH a) h7 hto hempty hbench (flag_strict a) hpk
    hn0 hn hz (by rw [hlen]; omega) hnle hzero hnFit hfitL hmv hsl hpeg hfitMv hfitSl
    (flag_bl a) (flag_cg a) hspan h3 hfm (flag_hole a) hzt
    hw0 hh0 hrR hrP hnE hkLe hgap (flag_w a) (flag_h a) (flag_r a) (flag_k a)
    hsm hnsm hbenchFit hfold

/-- `frobenius_point` is the across cube, the up cube, then the bottom cube. -/
theorem frobenius_point_bottom
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
    Ecbs.frobenius_point b =
      (do
        let r ← Ecbs.cube
          (markerUpFeed (upFlag a) 1 (ctrl + 3) (max (max mx 1) 2))
          Ecbs.bottom Ecbs.bottom
        pure { r with sudo_5Board_9marker_on := true }) := by
  rw [frobenius_point_cubes, ← bind_assoc]
  have htwo := point_across_up a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit hnbL
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  rw [htwo, ok_bind]
  have hbot := point_bottom a z hheld2 hhome2 hz hzt hn0 hnb hgap0 hs2 hfitCtrl hfitC3
    hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfm hfold
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hbot, except_bind_pure]

end EcbsLink2.Link2
