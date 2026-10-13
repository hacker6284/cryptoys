/-
  The up cube of `frobenius_affine`, after `across_up_cube`.
  The bench is still on, so the cube is the marker-off cube of the slid board.
  That cube's bench prefix is `fieldCube` of the up home.
  Each board step is its own lemma. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FrobeniusOn

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

/-- The marker-off board the up cube runs on: seated one step past the across cube. -/
def upFeed
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  markerUpFeed a.b1On 0 (ctrl + 1) (max mx 1)

theorem upFeed_flag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_9marker_on = false := by
  simp [upFeed, markerUpFeed]

theorem upFeed_on
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_8bench_on = true := by
  rw [show (upFeed a).sudo_5Board_8bench_on = a.b1On.sudo_5Board_8bench_on from by
    simp [upFeed, markerUpFeed]]
  exact a.honOn

theorem upFeed_to
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_8bench_to = ((0 : Nat) : Int) := by
  rw [show (upFeed a).sudo_5Board_8bench_to = a.b1On.sudo_5Board_8bench_to from by
    simp [upFeed, markerUpFeed]]
  exact a.htoOn

theorem upFeed_bench
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_5bench = embed a.laneX := by
  rw [show (upFeed a).sudo_5Board_5bench = a.b1On.sudo_5Board_5bench from by
    simp [upFeed, markerUpFeed]]
  exact a.hbenchOn

theorem upFeed_held
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4held = a.b1On.sudo_5Board_4held := by
  simp [upFeed, markerUpFeed]

theorem upFeed_home
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4home = a.b1On.sudo_5Board_4home := by
  simp [upFeed, markerUpFeed]

theorem upFeed_tier
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_1t = a.b1On.sudo_5Board_1t := by
  simp [upFeed, markerUpFeed]

theorem upFeed_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_5moves =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_5moves := by
  simp [upFeed, markerUpFeed]

theorem upFeed_slides
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_6slides =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_6slides := by
  simp [upFeed, markerUpFeed]

theorem upFeed_peak
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_4peak =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_4peak := by
  simp [upFeed, markerUpFeed]

theorem upFeed_strict
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  simp [upFeed, markerUpFeed]

theorem upFeed_hole
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  simp [upFeed, markerUpFeed]

theorem upFeed_ops
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops =
      a.b1On.sudo_5Board_4cost.sudo_5Costs_3ops := by
  simp [upFeed, markerUpFeed]

/-- The list the up cube folds. Its length-`n` prefix is the field cube. -/
def upLane (n k bench : Nat) (y : List Nat) : List Nat :=
  laneFold n (n - k) (combStrip n bench y)

theorem upLane_len (n k bench : Nat) (y : List Nat) (hnb : n ≤ bench) :
    (upLane n k bench y).length = bench := by
  rw [upLane, laneFold_length n (n - k) (combStrip n bench y)
      (by rw [combStrip_length]; exact hnb), combStrip_length]

theorem upLane_take (n k bench : Nat) (y : List Nat) :
    (upLane n k bench y).take n = fieldCube n k bench y := by
  simpa [upLane] using cube_off_prefix n k bench y

theorem upLane_zero (n k bench : Nat) (y : List Nat) (hn0 : 0 < n) (hgap0 : 0 < n - k)
    (hlen : (upLane n k bench y).length = bench) :
    ∀ i, n ≤ i → ∀ hi : i < (upLane n k bench y).length, (upLane n k bench y)[i] = 0 := by
  intro i hi hii
  have hbi : i < bench := by rw [← hlen]; exact hii
  have hc := cube_off_high y n k bench hn0 hgap0 i hi hbi
  exact (coeff_eq_get (upLane n k bench y) i hii).symm.trans (by simpa [upLane] using hc)

def upH (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    0 < (upFeed a).sudo_5Board_4home.size := by
  rw [upFeed_home a]; exact a.h0HOn

def upD (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    0 < (upFeed a).sudo_5Board_4held.size := by
  rw [upFeed_held a]; exact a.h0DOn

/-- The board after the up cube slides the across product into home 0. -/
def upSettled (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  settleBoard (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1

/-- The up cube slides the across product home, then cubes the bench-off board. -/
theorem up_slide
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hnb : n ≤ a.laneX.length) (hnFit : FitsLen n) (hfitC : FitsLen (cOps + 2)) :
    Ecbs.cube (upFeed a) ((1 : Nat) : Int) ((1 : Nat) : Int) =
      Ecbs.cube (upSettled a) ((1 : Nat) : Int) ((1 : Nat) : Int) := by
  have h7 : 7 ≤ (upFeed a).sudo_5Board_4held.size := by rw [upFeed_held a]; exact a.h7On
  have hempty : (upFeed a).sudo_5Board_4held[0] = false := by
    have hget := idx_eq (upFeed_held a) 0 (upD a)
    exact hget.trans a.hemptyOn
  have hn : (upFeed a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [upFeed_tier a]; exact a.hnOn
  have hmoves : (upFeed a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat a.mv1 := by
    rw [upFeed_moves a]; exact a.hmv1N
  have hslides : (upFeed a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [upFeed_slides a]; exact a.hslOn
  have hpeak : (upFeed a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat a.pk1 := by
    rw [upFeed_peak a]; exact a.hpkOn
  have hops : 1 < (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [upFeed_ops a]; exact a.hopsOn
  have hop1 : (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((cOps + 1 : Nat) : Int) := by
    have hget := idx_eq (upFeed_ops a) 1 hops
    exact hget.trans a.hopOn
  have hpeg : FitsLen (2 * pegCount (a.laneX.take n)) := by
    rw [← a.hpegDef]; exact a.hpegFit
  have hfitM : FitsLen (a.mv1 + 2 * pegCount (a.laneX.take n)) := by
    rw [← a.hpegDef]; exact a.hfitMvX
  have hfitS : FitsLen (slides + 2 * pegCount (a.laneX.take n)) := by
    rw [← a.hpegDef]; exact a.hfitSlX
  have hfops : FitsLen ((cOps + 1) + 1) := by
    have : (cOps + 1) + 1 = cOps + 2 := by omega
    rw [this]; exact hfitC
  exact cube_settle_other (upFeed a) 1 1 0 a.laneX n a.mv1 slides a.pk1 (cOps + 1)
    (upFeed_flag a) (upFeed_on a) (upFeed_to a) (upH a) (upD a) h7 hempty (upFeed_bench a) hn
    a.hposX hnb a.hzeroX hnFit a.hfitLX hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops

def upMv (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Nat :=
  a.mv1 + 2 * a.pegX

theorem up_moves
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_5moves = (upMv a : Int) := by
  rw [upSettled, settle_moves_eq, ← a.hpegDef, ofNat_eq_natCast]
  rfl

def upPk (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Nat :=
  if a.pk1 < countHeld ((upFeed a).sudo_5Board_4held.set ⟨0, upD a⟩ true) 7
    then countHeld ((upFeed a).sudo_5Board_4held.set ⟨0, upD a⟩ true) 7
    else a.pk1

theorem up_peak
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_4peak = (upPk a : Int) := by
  rw [upSettled, settle_peak_eq _ _ _ _ _ _ _ _ _
      (by rw [upFeed_peak a]; exact a.hpkOn), ofNat_eq_natCast]
  rfl

theorem up_off_flag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_9marker_on = false ∧
      (upSettled a).sudo_5Board_8bench_on = false := by
  refine ⟨?_, ?_⟩
  · rw [upSettled, settle_marker_eq]; exact upFeed_flag a
  · rw [upSettled]; exact settle_bench_off _ _ _ _ _ _ _ _ _

theorem up_strict
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_11peak_strict = (a.peakS1 : Int) := by
  rw [upSettled, settle_strict_eq, upFeed_strict]; exact a.hstrictOn

theorem up_hole
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat a.hole1 := by
  rw [upSettled, settle_hole_eq, upFeed_hole]; exact a.hholeOn

theorem up_held_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4held.size = 8 := by
  rw [upSettled, settle_held_eq, Array.size_set, upFeed_held]; exact a.hszDOn

theorem up_home_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4home.size = 8 := by
  rw [upSettled, settle_home_eq, Array.size_set, upFeed_home]; exact a.hszHOn

theorem up_held1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4held[1]'(by rw [up_held_size a]; decide) = true := by
  have hsz : 1 < (upSettled a).sudo_5Board_4held.size := by rw [up_held_size a]; decide
  have heq := settle_held_eq (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1
  have hget := idx_eq heq 1 hsz
  have hne : (0 : Nat) ≠ 1 := by decide
  simp only [Array.getElem_set, hne] at hget
  have hsrc : (upFeed a).sudo_5Board_4held[1]'(by rw [upFeed_held a]; exact a.h1DOn) = true := by
    have h2 := idx_eq (upFeed_held a) 1 (by rw [upFeed_held a]; exact a.h1DOn)
    exact h2.trans a.hheld1On
  exact hget.trans hsrc

theorem up_home1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4home[1]'(by rw [up_home_size a]; decide) = embed y := by
  have hsz : 1 < (upSettled a).sudo_5Board_4home.size := by rw [up_home_size a]; decide
  have heq := settle_home_eq (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1
  have hget := idx_eq heq 1 hsz
  have hne : (0 : Nat) ≠ 1 := by decide
  simp only [Array.getElem_set, hne] at hget
  have hsrc : (upFeed a).sudo_5Board_4home[1]'(by rw [upFeed_home a]; exact a.h1HOn) = embed y := by
    have h2 := idx_eq (upFeed_home a) 1 (by rw [upFeed_home a]; exact a.h1HOn)
    exact h2.trans a.hhome1On
  exact hget.trans hsrc

theorem up_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hnOn

theorem up_w
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hwOn

theorem up_h
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hhOn

theorem up_r
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hrOn

theorem up_k
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hkOn

theorem up_bl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hblOn

theorem up_cg
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
  rw [upSettled, settle_tier_eq, upFeed_tier]; exact a.hcgOn

theorem up_ops_lt
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  rw [upSettled, settle_ops, upFeed_ops]; exact a.hopsOn

theorem up_ops1
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(up_ops_lt a) =
      ((cOps + 1 : Nat) : Int) := by
  have heq := settle_ops (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1
  have hget := idx_eq heq 1 (up_ops_lt a)
  have hsrc : (upFeed a).sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by
      rw [upFeed_ops a]; exact a.hopsOn) = ((cOps + 1 : Nat) : Int) := by
    have h2 := idx_eq (upFeed_ops a) 1 (by rw [upFeed_ops a]; exact a.hopsOn)
    exact h2.trans a.hopOn
  exact hget.trans hsrc

def up1D (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upSettled a).sudo_5Board_4held.size := by
  rw [up_held_size a]; decide

def up1H (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upSettled a).sudo_5Board_4home.size := by
  rw [up_home_size a]; decide

/-- The bench-off up cube. Its bench prefix is read by `up_field`. -/
def upBoard (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

/-- The up home, after the across product has been slid off the bench, cubes to
    `upBoard`. That is `cube_off_eq` on the settled board. -/
theorem frob_up_off
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hfitC : FitsLen (cOps + 2))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    Ecbs.cube (upSettled a) ((1 : Nat) : Int) ((1 : Nat) : Int) = .ok (upBoard a) := by
  have h7 : 7 ≤ (upSettled a).sudo_5Board_4held.size := by rw [up_held_size a]; decide
  have hfm : FitsLen (upMv a + 2 * n) := by rw [upMv]; exact a.hfm2
  have hfold : FitsLen (upMv a + 2 * n + 3 * (bench - n)) := by rw [upMv]; exact a.hfold2
  exact cube_off_eq (upSettled a) 1 1 y w h r n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) cg (up_off_flag a).1 (up_off_flag a).2 (up_ops_lt a) (up_ops1 a) hfitC
    (up_bl a) (up_cg a) hspan (up1D a) (up1H a) (up_held1 a) (up_home1 a) h7
    hn0 (up_n a) hy hnFit (up_moves a) (up_peak a) (up_strict a) hyt h3 hfm
    hw0 hh0 hrR hrP hnE hkLe hgap (up_w a) (up_h a) (up_r a) (up_k a) (up_hole a)
    hsm hnsm hbenchFit hfold

/-- The bench `up_off` leaves has `fieldCube` of the up input as its length-`n` prefix. -/
theorem up_field
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_5bench = embed (upLane n k bench y) ∧
      (upLane n k bench y).take n = fieldCube n k bench y := by
  refine ⟨?_, upLane_take n k bench y⟩
  rw [upBoard, upLane]
  exact cube_off_bench (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

/-- The emitted up cube, marker seated and bench still on, returns that board
    with the flag put back. The bench prefix is the field cube of the up home. -/
theorem across_up_field
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
    Ecbs.cube a.b1On ((1 : Nat) : Int) ((1 : Nat) : Int) =
        .ok { upBoard a with sudo_5Board_9marker_on := true } ∧
      (upBoard a).sudo_5Board_5bench = embed (upLane n k bench y) ∧
      (upLane n k bench y).take n = fieldCube n k bench y := by
  have hpre := up_field a
  refine ⟨?_, hpre.1, hpre.2⟩
  rw [across_up_cube b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script a
      hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit
      hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm]
  rw [show markerUpFeed a.b1On 0 (ctrl + 1) (max mx 1) = upFeed a from rfl]
  rw [up_slide a hnb hnFit hfitC,
      frob_up_off a hyt hy hn0 hspan h3 hnFit hbenchFit hfitC
        hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm]
  simp only [ok_bind, pure_eq_ok]

def upFlag (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Ecbs.Board :=
  { upBoard a with sudo_5Board_9marker_on := true }

def upMv2 (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Nat :=
  cubeMoves (upMv a) y n k bench

def upSl (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Nat :=
  slides + 2 * a.pegX

def upPk2 (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    Nat :=
  raisedPeak (upPk a)
    (countHeld ((upSettled a).sudo_5Board_4held.set ⟨1, up1D a⟩ false) 7)

theorem up_board_on
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_8bench_on = true := by
  rw [upBoard]
  exact cube_off_on (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem up_board_to
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_8bench_to = ((1 : Nat) : Int) := by
  rw [upBoard]
  exact cube_off_to (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem up_board_mv
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (upMv2 a) := by
  rw [upBoard, upMv2]
  exact cube_off_moves (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem up_sl_settled
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upSettled a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (upSl a) := by
  rw [upSettled, upSl, settle_slides_eq, ← a.hpegDef]

theorem up_board_sl
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (upSl a) := by
  rw [upBoard, cube_off_slides, up_sl_settled]

theorem up_board_pk
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat (upPk2 a) := by
  rw [upBoard, upPk2]
  exact cube_off_peak (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)

theorem up_board_n
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  rw [upBoard, cube_off_tier, up_n]

theorem up_board_held_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4held.size = 8 := by
  rw [upBoard, cube_off_held, Array.size_set, up_held_size]

theorem up_board_home_size
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4home.size = 8 := by
  rw [upBoard, cube_off_home, Array.size_set, up_home_size]

def upFlag1 (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upFlag a).sudo_5Board_4held.size := by
  rw [upFlag, up_board_held_size]; decide

def upFlagH (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    1 < (upFlag a).sudo_5Board_4home.size := by
  rw [upFlag, up_board_home_size]; decide

theorem up_board_empty
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upFlag a).sudo_5Board_4held[1]'(upFlag1 a) = false := by
  have hheld := cube_off_held (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hszC : 1 < (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4held.size := by
    rw [hheld, Array.size_set]; exact up1D a
  have hget := idx_eq hheld 1 hszC
  simp only [Array.getElem_set] at hget
  have hflag : (upFlag a).sudo_5Board_4held = (upBoard a).sudo_5Board_4held := rfl
  have hboard : (upBoard a).sudo_5Board_4held =
      (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
        (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4held := by
    rw [upBoard]
  have hgetF := idx_eq hflag 1 (upFlag1 a)
  have hgetB := idx_eq hboard 1 (by rw [up_board_held_size]; decide)
  exact hgetF.symm.trans (hgetB.trans hget)

/-- Closing settle of the up cube. The up home becomes the field cube; the bench goes off. -/
theorem up_close
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hnb : n ≤ bench) (hnFit : FitsLen n)
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitM : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitS : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n))) :
    Ecbs.settle (upFlag a) =
      .ok (settleBoard (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
            (upMv2 a) (upSl a) (upPk2 a)) := by
  have hlen := upLane_len n k bench y hnb
  have hzero := upLane_zero n k bench y hn0 hgap0 hlen
  have hpos : 0 < (upLane n k bench y).length := by rw [hlen]; omega
  have hnle : n ≤ (upLane n k bench y).length := by rw [hlen]; exact hnb
  have hbench : (upFlag a).sudo_5Board_5bench = embed (upLane n k bench y) := by
    rw [upFlag]; exact (up_field a).1
  have hon : (upFlag a).sudo_5Board_8bench_on = true := by rw [upFlag]; exact up_board_on a
  have hto : (upFlag a).sudo_5Board_8bench_to = ((1 : Nat) : Int) := by
    rw [upFlag]; exact up_board_to a
  have hmv : (upFlag a).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (upMv2 a) := by
    rw [upFlag]; exact up_board_mv a
  have hsl : (upFlag a).sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (upSl a) := by
    rw [upFlag]; exact up_board_sl a
  have hpk : (upFlag a).sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat (upPk2 a) := by
    rw [upFlag]; exact up_board_pk a
  have hn : (upFlag a).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [upFlag]; exact up_board_n a
  have h7 : 7 ≤ (upFlag a).sudo_5Board_4held.size := by rw [upFlag, up_board_held_size]; decide
  have hfitL : FitsLen (upLane n k bench y).length := by
    rw [hlen, ← a.hlenX]; exact a.hfitLX
  exact settle_refines (upFlag a) 1 (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
    (upFlagH a) (upFlag1 a) h7 hon hto (up_board_empty a) hbench hn hpos hnle hzero
    hnFit hfitL hmv hsl hpk hpeg hfitM hfitS

theorem up_home0
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (upBoard a).sudo_5Board_4home[0]'(by rw [up_board_home_size a]; decide) =
      embed (fieldCube n k bench x) := by
  have hcube := cube_off_home (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
    (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have h0S : 0 < (upSettled a).sudo_5Board_4home.size := by rw [up_home_size a]; decide
  have hsz : 0 < (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
      (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4home.size := by
    rw [hcube, Array.size_set]; exact h0S
  have hget := idx_eq hcube 0 hsz
  have hne : (1 : Nat) ≠ 0 := by decide
  simp only [Array.getElem_set, hne, if_false] at hget
  have hset := settle_home_eq (upFeed a) 0 (upH a) (upD a) a.laneX n a.mv1 slides a.pk1
  have hget0 := idx_eq hset 0 (by rw [hset, Array.size_set]; exact upH a)
  simp only [Array.getElem_set, if_true] at hget0
  have htake : embed (List.take n a.laneX) = embed (fieldCube n k bench x) :=
    congrArg embed a.htakeX
  have hget0' := hget0.trans htake
  have hboard : (upBoard a).sudo_5Board_4home =
      (cubeOffBoard (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a) a.peakS1
        (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)).sudo_5Board_4home := by rw [upBoard]
  have hgetB := idx_eq hboard 0 (by rw [up_board_home_size a]; decide)
  exact hgetB.trans (hget.trans hget0')

/-- `frobenius_affine` with the marker lifted. Across is cubed, up is cubed with that
    bench still on, and the closing settle writes the up field cube home. The marker
    flag stays on. -/
theorem frobenius_affine_marker
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
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitM : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitS : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n))) :
    ∃ bF,
      Ecbs.frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube n k bench x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube n k bench y)) := by
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hfield := across_up_field a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit hnbL
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  have hset := up_close a hn0 hgap0 hnb hnFit hpeg hfitM hfitS
  let bF := settleBoard (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
    (upMv2 a) (upSl a) (upPk2 a)
  refine ⟨bF, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ecbs.frobenius_affine
    rw [show Ecbs.across = (0 : Int) from rfl, show Ecbs.up = (1 : Int) from rfl]
    have hcube0 : Ecbs.cube b (0 : Int) (0 : Int) = .ok a.b1On := a.hcube
    have hup : Ecbs.cube a.b1On (1 : Int) (1 : Int) =
        .ok { upBoard a with sudo_5Board_9marker_on := true } := hfield.1
    rw [hcube0, ok_bind]
    conv =>
      lhs
      dsimp
    rw [hup, ok_bind]
    show (Ecbs.settle (upFlag a) >>= fun r => pure r) = Except.ok bF
    rw [hset, ok_bind, pure_eq_ok]
  · rw [settle_marker_eq]; rfl
  · exact settle_bench_off (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
  · intro h0
    have hsetH := settle_home_eq (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
    have hget := idx_eq hsetH 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne, if_false] at hget
    have hflag : (upFlag a).sudo_5Board_4home = (upBoard a).sudo_5Board_4home := rfl
    have h0U : 0 < (upBoard a).sudo_5Board_4home.size := by rw [up_board_home_size a]; decide
    have hgetU := idx_eq hflag 0 (by rw [hflag]; exact h0U)
    exact hget.trans (hgetU.trans (up_home0 a))
  · intro h1
    have hsetH := settle_home_eq (upFlag a) 1 (upFlagH a) (upFlag1 a) (upLane n k bench y) n
      (upMv2 a) (upSl a) (upPk2 a)
    have hget := idx_eq hsetH 1 h1
    simp only [Array.getElem_set, if_true] at hget
    rw [upLane_take] at hget
    exact hget

/-- One marker-on Frobenius: two cubes, two settles. The move charge is at most
    eight pegs per home hole and six per folded bench hole. -/
def cubeCharge (n bench : Nat) : Nat :=
  8 * n + 6 * (bench - n)

/-- The slide charge of that Frobenius: two pegs on the way in, two on the way out,
    and a length-`n` home has at most `n` pegs. -/
def slideCharge (n : Nat) : Nat :=
  4 * n

private theorem lenFit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
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

private theorem budgetRoom (moves n bench : Nat)
    (hm : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n) :
    moves + cubeCharge n bench ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  dsimp [cubeCharge]
  omega

private theorem slideRoom (n slides : Nat) (hsl : slides ≤ 2 * n) :
    slides + slideCharge n ≤ 6 * n := by
  dsimp [slideCharge]
  omega

private theorem six_n_room (n bench : Nat) :
    6 * n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

/-- Pegs in the up field cube, and the counters the closing settle checks.
    A length-`n` home has at most `n` pegs, so each check is `FitsLen.of_le`
    of the cell's move and slide room. -/
theorem up_out_le
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    pegCount ((upLane n k bench y).take n) ≤ n ∧
      upMv2 a + 2 * pegCount ((upLane n k bench y).take n) ≤
        moves + cubeCharge n bench ∧
      upSl a + 2 * pegCount ((upLane n k bench y).take n) ≤
        slides + slideCharge n := by
  have hpt : pegCount ((upLane n k bench y).take n) ≤ n := by
    refine Nat.le_trans (pegCount_le _) ?_
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have hpx : a.pegX ≤ n := a.hpegX
  have hmv1 := a.hmv1le
  have hmv : upMv a = a.mv1 + 2 * a.pegX := rfl
  have hupLe : upMv a ≤ moves + 4 * n + 3 * (bench - n) := by
    rw [hmv]
    omega
  have hcube := cubeMoves_le (upMv a) y n k bench
  have hup : upMv2 a = cubeMoves (upMv a) y n k bench := rfl
  have hcube2 : upMv2 a ≤ moves + 6 * n + 6 * (bench - n) := by
    rw [hup]
    omega
  refine ⟨hpt, ?_, ?_⟩
  · have hfin : upMv2 a + 2 * pegCount ((upLane n k bench y).take n) ≤
        moves + 8 * n + 6 * (bench - n) := by
      omega
    rw [cubeCharge, ← Nat.add_assoc]
    exact hfin
  · have hsl : upSl a = slides + 2 * a.pegX := rfl
    have hfin : upSl a + 2 * pegCount ((upLane n k bench y).take n) ≤ slides + 4 * n := by
      rw [hsl]
      omega
    simpa [slideCharge] using hfin

theorem up_settle_fit
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hMv : FitsLen (moves + cubeCharge n bench))
    (hSl : FitsLen (slides + slideCharge n)) :
    FitsLen (2 * pegCount ((upLane n k bench y).take n)) ∧
      FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) ∧
      FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)) := by
  obtain ⟨hpt, hM, hS⟩ := up_out_le a
  refine ⟨?_, FitsLen.of_le hMv hM, FitsLen.of_le hSl hS⟩
  · exact FitsLen.of_le hMv (by
      have h2 : 2 * pegCount ((upLane n k bench y).take n) ≤ 2 * n :=
        Nat.mul_le_mul_left 2 hpt
      dsimp [cubeCharge] at *
      omega)

/-- The same three checks, from the rung budget `down_across` already requires.
    Homes of length `n` supply the peg bound. -/
theorem up_settle_fit_budget
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hnsm : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hmv : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n)
    (hsl : slides ≤ 2 * n) :
    FitsLen (2 * pegCount ((upLane n k bench y).take n)) ∧
      FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) ∧
      FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)) := by
  have hMv := lenFit n bench _ hnsm hb (budgetRoom moves n bench hmv)
  have hSl := lenFit n bench _ hnsm hb
    (Nat.le_trans (slideRoom n slides hsl) (six_n_room n bench))
  exact up_settle_fit a hMv hSl

/-- `frobenius_affine_marker` with the settle checks proved from the home length. -/
theorem frobenius_affine_len
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
    (hmv : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n)
    (hsl : slides ≤ 2 * n) :
    ∃ bF,
      Ecbs.frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = true ∧
      bF.sudo_5Board_8bench_on = false ∧
      (∀ h0 : 0 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[0] = embed (fieldCube n k bench x)) ∧
      (∀ h1 : 1 < bF.sudo_5Board_4home.size,
        bF.sudo_5Board_4home[1] = embed (fieldCube n k bench y)) := by
  have hfit := up_settle_fit_budget a hnsm hsm.2.2.2 hmv hsl
  exact frobenius_affine_marker a hyt hy hn0 hs1 hfitU hfitC hspan h3 hnFit hbenchFit
    hnbL hnb hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm hfit.1 hfit.2.1 hfit.2.2

end

end EcbsLink2.Link2
