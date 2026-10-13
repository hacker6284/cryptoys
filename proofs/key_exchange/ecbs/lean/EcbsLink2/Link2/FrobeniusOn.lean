/-
  `frobenius_affine` with the script marker lifted and the bench off.
  The first cube seats the marker. The second cube starts with that bench
  still on, so it is `cube_bench_up`, then the closing `settle`.
  The homes are the two field cubes. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerBench

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem array_at_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem frobFit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
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

private theorem offMarker (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6marker =
      b.sudo_5Board_6marker := rfl

private theorem offMax (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := rfl

private theorem two_cube_budget (moves n bench : Nat)
    (hm : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n) :
    moves + 8 * n + 6 * (bench - n) ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    6 * n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    bench ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    3 * (n - 1) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

/-- The across cube, marker lifted. The board it leaves has the bench on and the
    marker seated at 0, which is what the up cube reads. -/
structure DownAcross (b : Ecbs.Board) (x y : List Nat)
    (n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat) where
  b1 : Ecbs.Board
  b1On : Ecbs.Board
  feed : Ecbs.Board
  laneX : List Nat
  mv1 : Nat
  pk1 : Nat
  peakS1 : Nat
  hole1 : Nat
  pegX : Nat
  hcube : Ecbs.cube b ((0 : Nat) : Int) ((0 : Nat) : Int) = .ok b1On
  htakeX : laneX.take n = fieldCube n k bench x
  hlenX : laneX.length = bench
  hzeroX : ∀ i, n ≤ i → ∀ hi : i < laneX.length, laneX[i] = 0
  hposX : 0 < laneX.length
  hpegX : pegX ≤ n
  hpegDef : pegX = pegCount (laneX.take n)
  hmv1le : mv1 ≤ moves + 2 * n + 3 * (bench - n)
  hszD1 : b1.sudo_5Board_4held.size = 8
  hszH1 : b1.sudo_5Board_4home.size = 8
  htier1 : b1.sudo_5Board_1t = feed.sudo_5Board_1t
  h0D : 0 < b.sudo_5Board_4held.size
  h0H : 0 < b.sudo_5Board_4home.size
  hmkOn : b1On.sudo_5Board_9marker_on = true
  honOn : b1On.sudo_5Board_8bench_on = true
  hmOn : b1On.sudo_5Board_6marker = Int.ofNat 0
  hcOn : b1On.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1)
  hxOn : b1On.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1)
  hsOn : b1On.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script
  hopsOn : 1 < b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hopOn : b1On.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsOn = ((cOps + 1 : Nat) : Int)
  h0DOn : 0 < b1On.sudo_5Board_4held.size
  h0HOn : 0 < b1On.sudo_5Board_4home.size
  h1DOn : 1 < b1On.sudo_5Board_4held.size
  h1HOn : 1 < b1On.sudo_5Board_4home.size
  hszDOn : b1On.sudo_5Board_4held.size = 8
  hszHOn : b1On.sudo_5Board_4home.size = 8
  hmv1N : b1On.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv1
  hslOn : b1On.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  hpkOn : b1On.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk1
  hbenchOn : b1On.sudo_5Board_5bench = embed laneX
  htoOn : b1On.sudo_5Board_8bench_to = ((0 : Nat) : Int)
  hemptyOn : b1On.sudo_5Board_4held[0]'h0DOn = false
  hheld1On : b1On.sudo_5Board_4held[1]'h1DOn = true
  hhome1On : b1On.sudo_5Board_4home[1]'h1HOn = embed y
  hstrictOn : b1On.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS1 : Int)
  hholeOn : b1On.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1
  hnOn : b1On.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  hblOn : b1On.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench
  hcgOn : b1On.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg
  hwOn : b1On.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hhOn : b1On.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  hrOn : b1On.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  hkOn : b1On.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k
  h7On : 7 ≤ b1On.sudo_5Board_4held.size
  hfitLX : FitsLen laneX.length
  hpegFit : FitsLen (2 * pegX)
  hfitMvX : FitsLen (mv1 + 2 * pegX)
  hfitSlX : FitsLen (slides + 2 * pegX)
  hfm2 : FitsLen (mv1 + 2 * pegX + 2 * n)
  hfold2 : FitsLen (mv1 + 2 * pegX + 2 * n + 3 * (bench - n))

/-- Marker lifted (`marker < 0`), bench off. Across cube. -/
noncomputable def down_across (b : Ecbs.Board) (x y : List Nat)
    (w h r n k moves slides pk peakS holeN cOps ctrl mx script : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = n) (hy : y.length = n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hs1 : 1 < script) (hfitD : FitsLen (ctrl + 1))
    (hfitU : FitsLen ((ctrl + 1) + 2))
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hn0 : 0 < n) (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hspan : 3 * (n - 1) + cg < bench)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hmv : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n)
    (hsl : slides ≤ 2 * n) :
    DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script := by
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hbnd : bench ≤ 1000001 := hsm.2.2.2
  have hbud := two_cube_budget moves n bench hmv
  have fit (m : Nat) (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m :=
    frobFit n bench m hnsm hbnd hm
  have leMove (m : Nat) (hm : m ≤ moves + 8 * n + 6 * (bench - n)) :
      m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 :=
    Nat.le_trans hm hbud.1
  have leSmall (m : Nat) (hm : m ≤ 6 * n) :
      m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 :=
    Nat.le_trans hm hbud.2.1
  have leBench (m : Nat) (hm : m ≤ bench) :
      m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 :=
    Nat.le_trans hm hbud.2.2.1
  have leCube (m : Nat) (hm : m ≤ 3 * (n - 1)) :
      m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 :=
    Nat.le_trans hm hbud.2.2.2
  have hfit1 : FitsLen (cOps + 1) := FitsLen.of_le hfitC (Nat.le_succ (cOps + 1))
  have hposS : 0 < script := Nat.lt_trans (by decide) hs1
  have hnb : n ≤ bench := by omega
  have hmovCast : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [hmoves, ofNat_eq_natCast]
  have hpeakCast : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hpeak, ofNat_eq_natCast]
  have hstrictCast : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hstrict, ofNat_eq_natCast]
  let feed := markerDownFeed b ctrl mx
  let b1 := cubeOffBoard feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  let b1On := { b1 with sudo_5Board_9marker_on := true }
  have hcube1 : Ecbs.cube b ((0 : Nat) : Int) ((0 : Nat) : Int) = .ok b1On := by
    simpa [feed, b1, b1On] using
      cube_down_eq b 0 0 x w h r n k moves holeN bench pk peakS cOps cg ctrl mx script
        hmk hoff hm hc hmx hscript hposS hfitD hops hop1 hfit1 h0D h0H hheld0 hhome0 h7
        hstrictCast hpeakCast hn0 hn hx (fit n (leSmall n (by omega)))
        hmovCast hbl hcg hspan
        (fit (3 * (n - 1)) (leCube _ (Nat.le_refl _)))
        (fit (moves + 2 * n) (leMove _ (by omega)))
        hhole hxt hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm
        (fit bench (leBench _ (Nat.le_refl _)))
        (fit (moves + 2 * n + 3 * (bench - n)) (leMove _ (by omega)))
  let laneX := laneFold n (n - k) (combStrip n bench x)
  have hlaneX : b1.sudo_5Board_5bench = embed laneX := by
    simpa [b1, laneX] using
      cube_off_bench feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  have htakeX : laneX.take n = fieldCube n k bench x := by
    simpa [laneX] using cube_off_prefix n k bench x
  have hlenX : laneX.length = bench := by
    dsimp [laneX]
    rw [laneFold_length n (n - k) (combStrip n bench x)
        (by rw [combStrip_length]; exact hnb), combStrip_length]
  have hzeroX : ∀ i, n ≤ i → ∀ hi : i < laneX.length, laneX[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hlenX]; exact hii
    have hc0 := cube_off_high x n k bench hn0
      (by rw [hgap]; exact Nat.mul_pos hw0 hrP) i hi hbi
    exact (coeff_eq_get laneX i hii).symm.trans (by simpa [laneX] using hc0)
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    have hs := cube_off_held feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, feed, markerDownFeed, Array.size_set, hszD] using congrArg Array.size hs
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    have hs := cube_off_home feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, feed, markerDownFeed, Array.size_set, hszH] using congrArg Array.size hs
  have h0D1 : 0 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h0H1 : 0 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty0 : b1.sudo_5Board_4held[0] = false := by
    have hget := array_at_eq
      (cube_off_held feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H) 0 h0D1
    simp only [Array.getElem_set] at hget
    simpa [b1] using hget
  have hheld1b : b1.sudo_5Board_4held[1] = true := by
    have hget := array_at_eq
      (cube_off_held feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H) 1 h1D1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    simpa [b1, feed, markerDownFeed] using hget.trans hheld1
  have hhome1b : b1.sudo_5Board_4home[1] = embed y := by
    have hget := array_at_eq
      (cube_off_home feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H) 1 h1H1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    simpa [b1, feed, markerDownFeed] using hget.trans hhome1
  let mv1 := cubeMoves moves x n k bench
  let pk1 := raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ false) 7)
  let peakS1 := raisedPeak peakS (countHeld b.sudo_5Board_4held 7)
  let hole1 := raisedHole holeN (topIdx (combStrip n bench x))
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv1 := by
    simpa [b1, mv1] using
      cube_off_moves feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk1 := by
    have hs := cube_off_peak feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, pk1, feed, markerDownFeed] using hs
  have hsl1 : b1.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    have hs := cube_off_slides feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, feed, markerDownFeed] using hs.trans hslides
  have hon1 : b1.sudo_5Board_8bench_on = true := by
    simpa [b1] using cube_off_on feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  have hto1 : b1.sudo_5Board_8bench_to = ((0 : Nat) : Int) := by
    simpa [b1] using cube_off_to feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  have htier1 : b1.sudo_5Board_1t = feed.sudo_5Board_1t := by
    simpa [b1] using cube_off_tier feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
  have hstrict1 : b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS1 := by
    have hs := cube_off_strict feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, peakS1, feed, markerDownFeed] using hs
  have hhole1 : b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1 := by
    have hs := cube_off_hole feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    simpa [b1, hole1, feed, markerDownFeed] using hs
  have hm1 : b1.sudo_5Board_6marker = Int.ofNat 0 := by
    rw [show b1.sudo_5Board_6marker = feed.sudo_5Board_6marker from
      offMarker feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H]
    simp [feed, markerDownFeed]
  have hc1 : b1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) := by
    rw [cube_off_ctrl feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H]
    simp [feed, markerDownFeed, hc]
  have hx1 : b1.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx 1) := by
    rw [show b1.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        feed.sudo_5Board_4cost.sudo_5Costs_17script_marker_max from
      offMax feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H]
    simp [feed, markerDownFeed]
  have hs1b : b1.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    rw [htier1]
    simp [feed, markerDownFeed, hscript]
  have hops1b : 1 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hs := cube_off_ops feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H
    have hsz : b1.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [b1, Array.size_set] using congrArg Array.size hs
    have hszF : feed.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simp [feed, markerDownFeed]
    rw [hsz, hszF]
    exact hops
  have hop1b : b1.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((cOps + 1 : Nat) : Int) := by
    have hget := array_at_eq
      (cube_off_ops feed 0 0 x n k moves holeN bench pk peakS cOps hops h0D h0H) 1 hops1b
    simp only [Array.getElem_set, if_true] at hget
    simpa [b1] using hget
  let pegX := pegCount (laneX.take n)
  have hpegDef : pegX = pegCount (laneX.take n) := rfl
  have hpegX : pegX ≤ n := by
    dsimp [pegX]
    exact Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hposX : 0 < laneX.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le hn0 hnb
  have hmv1le : mv1 ≤ moves + 2 * n + 3 * (bench - n) := by
    simpa [mv1] using cubeMoves_le moves x n k bench
  let ctrl1 := ctrl + 1
  let mx1 := max mx 1
  have hmkOn : b1On.sudo_5Board_9marker_on = true := rfl
  have honOn : b1On.sudo_5Board_8bench_on = true := by simpa [b1On] using hon1
  have hmOn : b1On.sudo_5Board_6marker = Int.ofNat 0 := by simpa [b1On] using hm1
  have hcOn : b1On.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl1 := by
    simpa [b1On, ctrl1] using hc1
  have hxOn : b1On.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx1 := by
    simpa [b1On, mx1] using hx1
  have hsOn : b1On.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [b1On] using hs1b
  have hfitM0 : FitsLen (0 + 1) := fits_small (by decide)
  have hfit2 : FitsLen (0 + 2) := fits_small (by decide)
  have hbound0 : 0 + 1 < script := by simpa using hs1
  have hopsOn : 1 < b1On.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [b1On] using hops1b
  have hopOn : b1On.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsOn = ((cOps + 1 : Nat) : Int) := by
    simpa [b1On] using hop1b
  have hne10 : (1 : Nat) ≠ 0 := by decide
  have hmv1N : b1On.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv1 := by
    simpa [b1On] using hmv1
  have hslOn : b1On.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simpa [b1On] using hsl1
  have hpkOn : b1On.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk1 := by
    simpa [b1On] using hpk1
  have hbenchOn : b1On.sudo_5Board_5bench = embed laneX := by simpa [b1On] using hlaneX
  have htoOn : b1On.sudo_5Board_8bench_to = ((0 : Nat) : Int) := by simpa [b1On] using hto1
  have hemptyOn : b1On.sudo_5Board_4held[0] = false := by simpa [b1On] using hempty0
  have hheld1On : b1On.sudo_5Board_4held[1] = true := by simpa [b1On] using hheld1b
  have hhome1On : b1On.sudo_5Board_4home[1] = embed y := by simpa [b1On] using hhome1b
  have hstrictOn : b1On.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS1 : Int) := by
    rw [show b1On.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict from rfl, hstrict1, ofNat_eq_natCast]
  have hholeOn : b1On.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1 := by
    simpa [b1On] using hhole1
  have hnOn : b1On.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hn]
  have hblOn : b1On.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hbl]
  have hcgOn : b1On.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hcg]
  have hwOn : b1On.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hw]
  have hhOn : b1On.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hh]
  have hrOn : b1On.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hr]
  have hkOn : b1On.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [show b1On.sudo_5Board_1t = b1.sudo_5Board_1t from rfl, htier1]
    simp [feed, markerDownFeed, hk]
  have h0DOn : 0 < b1On.sudo_5Board_4held.size := by simpa [b1On] using h0D1
  have h0HOn : 0 < b1On.sudo_5Board_4home.size := by simpa [b1On] using h0H1
  have h1DOn : 1 < b1On.sudo_5Board_4held.size := by simpa [b1On] using h1D1
  have h1HOn : 1 < b1On.sudo_5Board_4home.size := by simpa [b1On] using h1H1
  have h7On : 7 ≤ b1On.sudo_5Board_4held.size := by simpa [b1On] using h7_1
  have hszDOn : b1On.sudo_5Board_4held.size = 8 := by simpa [b1On] using hszD1
  have hszHOn : b1On.sudo_5Board_4home.size = 8 := by simpa [b1On] using hszH1
  have hfitLX : FitsLen laneX.length := fit _ (leBench _ (by rw [hlenX]; exact Nat.le_refl _))
  have hpegFit : FitsLen (2 * pegX) := fit _ (leSmall _ (by omega))
  have hfitMvX : FitsLen (mv1 + 2 * pegX) := fit _ (leMove _ (by omega))
  have hfitSlX : FitsLen (slides + 2 * pegX) := fit _ (leSmall _ (by omega))
  have hfm2 : FitsLen (mv1 + 2 * pegX + 2 * n) := fit _ (leMove _ (by omega))
  have hfold2 : FitsLen (mv1 + 2 * pegX + 2 * n + 3 * (bench - n)) :=
    fit _ (leMove _ (by omega))
  exact
    { b1, b1On, feed, laneX, mv1, pk1, peakS1, hole1, pegX,
      hcube := hcube1, htakeX, hlenX, hzeroX, hposX, hpegX, hpegDef, hmv1le,
      hszD1, hszH1, htier1, h0D, h0H, hmkOn, honOn, hmOn, hcOn, hxOn, hsOn,
      hopsOn, hopOn, hmv1N, hslOn, hpkOn, hbenchOn, htoOn, hemptyOn,
      hheld1On, hhome1On, hstrictOn, hholeOn, hnOn, hblOn, hcgOn,
      hwOn, hhOn, hrOn, hkOn, h0DOn, h0HOn, h1DOn, h1HOn, hszDOn, hszHOn, h7On,
      hfitLX, hpegFit, hfitMvX, hfitSlX, hfm2, hfold2 }

/-- The up cube starts on the board the across cube leaves: the bench is still
    on, aimed at across, and the marker is seated at 0. -/
theorem across_up_cube (b : Ecbs.Board) (x y : List Nat)
    (n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat)
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (hyt : allTritList y) (hy : y.length = n) (hn0 : 0 < n)
    (hs1 : 1 < script) (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    Ecbs.cube a.b1On ((1 : Nat) : Int) ((1 : Nat) : Int) =
      (do
        let r ← Ecbs.cube (markerUpFeed a.b1On 0 (ctrl + 1) (max mx 1))
          ((1 : Nat) : Int) ((1 : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  have hfitM0 : FitsLen (0 + 1) := fits_small (by decide)
  have hfit20 : FitsLen (0 + 2) := fits_small (by decide)
  have hbound0 : 0 + 1 < script := hs1
  have hne : (1 : Nat) ≠ 0 := by decide
  have hnb : n ≤ a.laneX.length := by rw [a.hlenX]; omega
  have hpegFit : FitsLen (2 * pegCount (List.take n a.laneX)) := by
    rw [← a.hpegDef]; exact a.hpegFit
  have hfitMv : FitsLen (a.mv1 + 2 * pegCount (List.take n a.laneX)) := by
    rw [← a.hpegDef]; exact a.hfitMvX
  have hfitSl : FitsLen (slides + 2 * pegCount (List.take n a.laneX)) := by
    rw [← a.hpegDef]; exact a.hfitSlX
  have hfm : FitsLen (a.mv1 + 2 * pegCount (List.take n a.laneX) + 2 * n) := by
    rw [← a.hpegDef]; exact a.hfm2
  have hfold : FitsLen (a.mv1 + 2 * pegCount (List.take n a.laneX) + 2 * n + 3 * (bench - n)) := by
    rw [← a.hpegDef]; exact a.hfold2
  exact cube_bench_up a.b1On 1 1 0 y a.laneX w h r n k a.mv1 slides a.hole1 bench a.pk1
      a.peakS1 (cOps + 1) cg 0 (ctrl + 1) (max mx 1) script
      a.hmkOn a.honOn a.hmOn a.hcOn a.hxOn a.hsOn hbound0 hfitM0 hfitU hfit20
      a.hopsOn a.hopOn hfitC hne a.h1DOn a.h1HOn a.hheld1On a.hhome1On
      a.h0DOn a.h0HOn a.h7On a.htoOn a.hemptyOn a.hbenchOn a.hstrictOn a.hpkOn
      hn0 a.hnOn hy a.hposX hnb a.hzeroX
      hnFit a.hfitLX a.hmv1N a.hslOn hpegFit hfitMv hfitSl
      a.hblOn a.hcgOn hspan h3 hfm a.hholeOn hyt
      hw0 hh0 hrR hrP hnE hkLe hgap a.hwOn a.hhOn a.hrOn a.hkOn hsm hnsm
      hbenchFit hfold

end EcbsLink2.Link2
