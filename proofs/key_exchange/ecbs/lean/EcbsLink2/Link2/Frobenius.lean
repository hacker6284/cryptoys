/-
  `frobenius_affine` cubes the across band and the up band.
  SPEC.md §3 R5 line 138, the affine form `walk_chord` uses.
  The second cube slides the first product home (`cube_settle_other`); the
  closing `settle` is `settle_refines`. `settleBoard` stays a name.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CurveCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] settleBoard placeBoard

private theorem tier_of (t : Spec.Tier) (b : Ecbs.Board) (hb : b.sudo_5Board_1t = embTier t) :
    b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n ∧
    b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat t.k ∧
    b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat t.w ∧
    b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat t.h ∧
    b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat t.r ∧
    b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat t.benchlen ∧
    b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat t.combgap := by
  rw [hb]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem two_cube_budget (moves n bench : Nat)
    (hm : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n) :
    moves + 8 * n + 6 * (bench - n) ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    6 * n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    bench ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    3 * (n - 1) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

/-- Across and up, both held, bench off. `frobenius_affine` replaces them by
    their cubes and leaves every other home alone. -/
theorem frobenius_affine_refines (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (b : Ecbs.Board) (x y : List Nat)
    (moves slides pk peakS holeN cOps : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hops1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hT : b.sudo_5Board_1t = embTier t)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops1 = (cOps : Int))
    (hfitC : FitsLen (cOps + 2))
    (hheld0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (hhome0 : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed x)
    (hheld1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (hhome1 : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed y)
    (hmv : moves ≤ t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 6 * t.n)
    (hsl : slides ≤ 2 * t.n) :
    ∃ (bF : Ecbs.Board) (mvF slF pkF : Nat),
      Ecbs.frobenius_affine b = .ok bF ∧
      bF.sudo_5Board_9marker_on = false ∧
      bF.sudo_5Board_8bench_on = false ∧
      bF.sudo_5Board_4home.size = 8 ∧
      bF.sudo_5Board_4held.size = 8 ∧
      bF.sudo_5Board_1t = embTier t ∧
      (∀ (h : 0 < bF.sudo_5Board_4held.size), bF.sudo_5Board_4held[0] = true) ∧
      (∀ (h : 0 < bF.sudo_5Board_4home.size),
        bF.sudo_5Board_4home[0] = embed (fieldCube t.n t.k t.benchlen x)) ∧
      (∀ (h : 1 < bF.sudo_5Board_4held.size), bF.sudo_5Board_4held[1] = true) ∧
      (∀ (h : 1 < bF.sudo_5Board_4home.size),
        bF.sudo_5Board_4home[1] = embed (fieldCube t.n t.k t.benchlen y)) ∧
      (∀ j, 2 ≤ j → j < 7 →
        ∀ (hD : j < bF.sudo_5Board_4held.size) (hH : j < bF.sudo_5Board_4home.size)
          (hDb : j < b.sudo_5Board_4held.size) (hHb : j < b.sudo_5Board_4home.size),
          bF.sudo_5Board_4held[j] = b.sudo_5Board_4held[j] ∧
          bF.sudo_5Board_4home[j] = b.sudo_5Board_4home[j]) ∧
      bF.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvF ∧
      bF.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slF ∧
      bF.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkF ∧
      mvF ≤ t.n * (t.n + 1) + 9 * (t.benchlen - t.n) + 14 * t.n ∧
      slF ≤ 6 * t.n ∧
      1 < bF.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let cg := t.combgap
  have hfields := tier_of t b hT
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have hbud := two_cube_budget moves n bench (by simpa [n, bench] using hmv)
  have hslN : slides ≤ 2 * n := by simpa [n] using hsl
  have fit (m : Nat) (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m :=
    curveLayFit n bench m hnsm hbnd hm
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
  have hfit1 : FitsLen (cOps + 1) := Nat.le_trans (Nat.le_succ (cOps + 1)) hfitC
  have hnb : n ≤ bench := by
    have hm := lay.mul_span
    have h0 := lay.board.n_pos
    omega
  have hnCast : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [hfields.1]; exact ofNat_eq_natCast _
  have hpeakCast : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hpeak]; exact ofNat_eq_natCast _
  have hstrictCast : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hstrict]; exact ofNat_eq_natCast _
  have hmovCast : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    rw [hmoves]; exact ofNat_eq_natCast _
  let b1 := cubeOffBoard b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hcube1 : Ecbs.cube b ((0 : Nat) : Int) ((0 : Nat) : Int) = .ok b1 := by
    simpa [b1] using
      cube_off_eq b 0 0 x w h r n k moves holeN bench pk peakS cOps cg
        hmk hoff hops1 hop1 hfit1
        hfields.2.2.2.2.2.1 hfields.2.2.2.2.2.2 sat.cube_span
        h0D h0H hheld0 hhome0 h7 lay.board.n_pos hnCast
        (by simpa [n] using hx) (fit n (leSmall n (by omega)))
        hmovCast hpeakCast hstrictCast hxt
        (fit (3 * (n - 1)) (leCube _ (Nat.le_refl _)))
        (fit (moves + 2 * n) (leMove _ (by omega)))
        lay.w_pos lay.h_pos lay.r_lt lay.r_pos lay.n_eq lay.k_le lay.gap_eq
        (by rw [hfields.2.2.1])
        (by rw [hfields.2.2.2.1])
        (by rw [hfields.2.2.2.2.1])
        (by rw [hfields.2.1])
        hhole lay.small hnsm
        (fit bench (leBench _ (Nat.le_refl _)))
        (fit (moves + 2 * n + 3 * (bench - n)) (leMove _ (by omega)))
  let laneX := laneFold n (n - k) (combStrip n bench x)
  have hlaneX : b1.sudo_5Board_5bench = embed laneX := by
    simpa [b1, laneX] using cube_off_bench b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have htakeX : laneX.take n = fieldCube n k bench x := by
    simpa [laneX] using cube_off_prefix n k bench x
  have hcombX : (combStrip n bench x).length = bench := combStrip_length n bench x
  have hlenX : laneX.length = bench := by
    dsimp [laneX]
    rw [laneFold_length n (n - k) (combStrip n bench x) (by rw [hcombX]; exact hnb)]
    exact hcombX
  have hzeroX : ∀ i, n ≤ i → ∀ hi : i < laneX.length, laneX[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hlenX]; exact hii
    have hc := cube_off_high x n k bench lay.board.n_pos
      (by rw [lay.gap_eq]; exact Nat.mul_pos lay.w_pos lay.r_pos) i hi hbi
    exact (coeff_eq_get laneX i hii).symm.trans (by simpa [laneX] using hc)
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    have hs := cube_off_held b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
    simpa [b1, Array.size_set, hszD] using congrArg Array.size hs
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    have hs := cube_off_home b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
    simpa [b1, Array.size_set, hszH] using congrArg Array.size hs
  have h0D1 : 0 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h0H1 : 0 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty0 : b1.sudo_5Board_4held[0] = false := by
    have hget := get_eq_of_array
      (cube_off_held b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) 0 h0D1
    simp only [Array.getElem_set] at hget
    simpa [b1] using hget
  have hheld1b : b1.sudo_5Board_4held[1] = true := by
    have hget := get_eq_of_array
      (cube_off_held b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) 1 h1D1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans hheld1
  have hhome1b : b1.sudo_5Board_4home[1] = embed y := by
    have hget := get_eq_of_array
      (cube_off_home b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) 1 h1H1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans hhome1
  let mv1 := cubeMoves moves x n k bench
  let pk1 := raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ false) 7)
  let peakS1 := raisedPeak peakS (countHeld b.sudo_5Board_4held 7)
  let hole1 := raisedHole holeN (topIdx (combStrip n bench x))
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv1 := by
    simpa [b1, mv1] using
      cube_off_moves b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk1 := by
    simpa [b1, pk1] using
      cube_off_peak b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hsl1 : b1.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    have hs := cube_off_slides b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
    simpa [b1] using hs.trans hslides
  have hmk1 : b1.sudo_5Board_9marker_on = false := by
    simpa [b1] using cube_off_marker b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hon1 : b1.sudo_5Board_8bench_on = true := by
    simpa [b1] using cube_off_on b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hto1 : b1.sudo_5Board_8bench_to = ((0 : Nat) : Int) := by
    simpa [b1] using cube_off_to b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have htier1 : b1.sudo_5Board_1t = b.sudo_5Board_1t := by
    simpa [b1] using cube_off_tier b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hstrict1 : b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS1 := by
    simpa [b1, peakS1] using
      cube_off_strict b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hhole1 : b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1 := by
    simpa [b1, hole1] using
      cube_off_hole b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
  have hops1b : 1 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    have hs := cube_off_ops b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H
    have hsz : b1.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [b1, Array.size_set] using congrArg Array.size hs
    rw [hsz]
    exact hops1
  have hop1b : b1.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((cOps + 1 : Nat) : Int) := by
    have hget := get_eq_of_array
      (cube_off_ops b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) 1 hops1b
    simp only [Array.getElem_set] at hget
    simpa [b1] using hget
  let pegX := pegCount (laneX.take n)
  have hpegX : pegX ≤ n := by
    dsimp [pegX]
    exact Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hposX : 0 < laneX.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le (by simpa [n] using lay.board.n_pos) hnb
  have hmv1le : mv1 ≤ moves + 2 * n + 3 * (bench - n) := by
    simpa [mv1] using cubeMoves_le moves x n k bench
  let bS := settleBoard b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hset1 : Ecbs.cube b1 ((1 : Nat) : Int) ((1 : Nat) : Int) =
      Ecbs.cube bS ((1 : Nat) : Int) ((1 : Nat) : Int) := by
    exact cube_settle_other b1 1 1 0 laneX n mv1 slides pk1 (cOps + 1)
      hmk1 hon1 hto1 h0H1 h0D1 h7_1 hempty0 hlaneX
      (by rw [htier1]; exact hnCast) hposX (by rw [hlenX]; exact hnb) hzeroX
      (fit n (leSmall n (by omega)))
      (fit laneX.length (leBench _ (by rw [hlenX]; exact Nat.le_refl _)))
      hmv1 hsl1 hpk1
      (fit (2 * pegX) (leSmall _ (by omega)))
      (fit (mv1 + 2 * pegX) (leMove _ (by omega)))
      (fit (slides + 2 * pegX) (leSmall _ (by omega)))
      hops1b (by rw [hop1b])
      hfitC
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    rw [settle_marker_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1]; exact hmk1
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hheldS := settle_held_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hhomeS := settle_home_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have htierS := settle_tier_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hmovS := settle_moves_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hslS := settle_slides_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hpeakS := settle_peak_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1 hpk1
  have hstrictS := settle_strict_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hholeS := settle_hole_eq b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hopsS := settle_ops b1 0 h0H1 h0D1 laneX n mv1 slides pk1
  have hszDS : bS.sudo_5Board_4held.size = 8 := by
    rw [hheldS, Array.size_set, hszD1]
  have hszHS : bS.sudo_5Board_4home.size = 8 := by
    rw [hhomeS, Array.size_set, hszH1]
  have h1DS : 1 < bS.sudo_5Board_4held.size := by rw [hszDS]; decide
  have h1HS : 1 < bS.sudo_5Board_4home.size := by rw [hszHS]; decide
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by rw [hszDS]; decide
  have hheld1S : bS.sudo_5Board_4held[1] = true := by
    have hget := get_eq_of_array hheldS 1 h1DS
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans hheld1b
  have hhome1S : bS.sudo_5Board_4home[1] = embed y := by
    have hget := get_eq_of_array hhomeS 1 h1HS
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans hhome1b
  let mvS := mv1 + 2 * pegX
  let slS := slides + 2 * pegX
  let pkS := if pk1 < countHeld (b1.sudo_5Board_4held.set ⟨0, h0D1⟩ true) 7
    then countHeld (b1.sudo_5Board_4held.set ⟨0, h0D1⟩ true) 7 else pk1
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvS := by
    simpa [bS, mvS, pegX] using hmovS
  have hslSeq : bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slS := by
    simpa [bS, slS, pegX] using hslS
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkS := by
    simpa [bS, pkS] using hpeakS
  have hstrictSeq : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS1 := by
    rw [hstrictS]; exact hstrict1
  have hholeSeq : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole1 := by
    rw [hholeS]; exact hhole1
  have hops1S : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b1.sudo_5Board_4cost.sudo_5Costs_3ops.size from congrArg Array.size hopsS]
    exact hops1b
  have hop1S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((cOps + 1 : Nat) : Int) := by
    have hget := get_eq_of_array hopsS 1 hops1S
    exact hget.trans hop1b
  have hmvSle : mvS ≤ moves + 4 * n + 3 * (bench - n) := by
    dsimp [mvS]
    have : 2 * pegX ≤ 2 * n := Nat.mul_le_mul_left 2 hpegX
    omega
  have hytS : allTritList y := hyt
  let b2 := cubeOffBoard bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hcube2 : Ecbs.cube bS ((1 : Nat) : Int) ((1 : Nat) : Int) = .ok b2 := by
    simpa [b2] using
      cube_off_eq bS 1 1 y w h r n k mvS hole1 bench pkS peakS1 (cOps + 1) cg
        hmkS hoffS hops1S (by rw [hop1S])
        hfitC
        (by rw [htierS, htier1, hfields.2.2.2.2.2.1])
        (by rw [htierS, htier1, hfields.2.2.2.2.2.2])
        sat.cube_span
        h1DS h1HS hheld1S hhome1S h7S lay.board.n_pos
        (by rw [htierS, htier1]; exact hnCast)
        (by simpa [n] using hy) (fit n (leSmall n (by omega)))
        (by rw [hmvS]; exact ofNat_eq_natCast _)
        (by rw [hpkS]; exact ofNat_eq_natCast _)
        (by rw [hstrictSeq]; exact ofNat_eq_natCast _)
        hytS
        (fit (3 * (n - 1)) (leCube _ (Nat.le_refl _)))
        (fit (mvS + 2 * n) (leMove _ (by omega)))
        lay.w_pos lay.h_pos lay.r_lt lay.r_pos lay.n_eq lay.k_le lay.gap_eq
        (by rw [htierS, htier1, hfields.2.2.1])
        (by rw [htierS, htier1, hfields.2.2.2.1])
        (by rw [htierS, htier1, hfields.2.2.2.2.1])
        (by rw [htierS, htier1, hfields.2.1])
        hholeSeq lay.small hnsm
        (fit bench (leBench _ (Nat.le_refl _)))
        (fit (mvS + 2 * n + 3 * (bench - n)) (leMove _ (by omega)))
  let laneY := laneFold n (n - k) (combStrip n bench y)
  have hlaneY : b2.sudo_5Board_5bench = embed laneY := by
    simpa [b2, laneY] using
      cube_off_bench bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have htakeY : laneY.take n = fieldCube n k bench y := by
    simpa [laneY] using cube_off_prefix n k bench y
  have hlenY : laneY.length = bench := by
    dsimp [laneY]
    rw [laneFold_length n (n - k) (combStrip n bench y)
      (by rw [combStrip_length]; exact hnb), combStrip_length]
  have hzeroY : ∀ i, n ≤ i → ∀ hi : i < laneY.length, laneY[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hlenY]; exact hii
    have hc := cube_off_high y n k bench lay.board.n_pos
      (by rw [lay.gap_eq]; exact Nat.mul_pos lay.w_pos lay.r_pos) i hi hbi
    exact (coeff_eq_get laneY i hii).symm.trans (by simpa [laneY] using hc)
  let mv2 := cubeMoves mvS y n k bench
  let pk2 := raisedPeak pkS (countHeld (bS.sudo_5Board_4held.set ⟨1, h1DS⟩ false) 7)
  have hmv2 : b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 := by
    simpa [b2, mv2] using
      cube_off_moves bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hpk2 : b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 := by
    simpa [b2, pk2] using
      cube_off_peak bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hsl2 : b2.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slS := by
    have hs := cube_off_slides bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
    simpa [b2] using hs.trans hslSeq
  have hmk2 : b2.sudo_5Board_9marker_on = false := by
    simpa [b2] using
      cube_off_marker bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hon2 : b2.sudo_5Board_8bench_on = true := by
    simpa [b2] using
      cube_off_on bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hto2 : b2.sudo_5Board_8bench_to = ((1 : Nat) : Int) := by
    simpa [b2] using
      cube_off_to bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
  have hszD2 : b2.sudo_5Board_4held.size = 8 := by
    have hs := cube_off_held bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
    simpa [b2, Array.size_set, hszDS] using congrArg Array.size hs
  have hszH2 : b2.sudo_5Board_4home.size = 8 := by
    have hs := cube_off_home bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
    simpa [b2, Array.size_set, hszHS] using congrArg Array.size hs
  have h1D2 : 1 < b2.sudo_5Board_4held.size := by rw [hszD2]; decide
  have h1H2 : 1 < b2.sudo_5Board_4home.size := by rw [hszH2]; decide
  have h0D2 : 0 < b2.sudo_5Board_4held.size := by rw [hszD2]; decide
  have h0H2 : 0 < b2.sudo_5Board_4home.size := by rw [hszH2]; decide
  have h7_2 : 7 ≤ b2.sudo_5Board_4held.size := by rw [hszD2]; decide
  have hempty1 : b2.sudo_5Board_4held[1] = false := by
    have hget := get_eq_of_array
      (cube_off_held bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS) 1 h1D2
    simp only [Array.getElem_set] at hget
    simpa [b2] using hget
  have hn2 : b2.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    have ht := cube_off_tier bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS
    have hte : b2.sudo_5Board_1t = bS.sudo_5Board_1t := by simpa [b2] using ht
    rw [hte, htierS, htier1]
    exact hnCast
  let pegY := pegCount (laneY.take n)
  have hpegY : pegY ≤ n := by
    dsimp [pegY]
    exact Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hmv2le : mv2 ≤ mvS + 2 * n + 3 * (bench - n) := by
    simpa [mv2] using cubeMoves_le mvS y n k bench
  have hsettle2 := settle_refines b2 1 laneY n mv2 slS pk2
    h1H2 h1D2 h7_2 hon2 hto2 hempty1 hlaneY hn2
    (by
      rw [hlenY]
      exact Nat.lt_of_lt_of_le (by simpa [n] using lay.board.n_pos) hnb)
    (by rw [hlenY]; exact hnb) hzeroY
    (fit n (leSmall n (by omega)))
    (fit laneY.length (leBench _ (by rw [hlenY]; exact Nat.le_refl _)))
    hmv2 hsl2 hpk2
    (fit (2 * pegY) (leSmall _ (by omega)))
    (fit (mv2 + 2 * pegY) (leMove _ (by omega)))
    (fit (slS + 2 * pegY) (leSmall _ (by
      dsimp [slS]
      omega)))
  let bF := settleBoard b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hbF : Ecbs.settle b2 = .ok bF := by simpa [bF] using hsettle2
  have hheldF := settle_held_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hhomeF := settle_home_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have htierF := settle_tier_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hmovF := settle_moves_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hslFeq := settle_slides_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hpeakF := settle_peak_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2 hpk2
  have hoffF := settle_bench_off b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  have hmkF := settle_marker_eq b2 1 h1H2 h1D2 laneY n mv2 slS pk2
  let mvF := mv2 + 2 * pegY
  let slF := slS + 2 * pegY
  let pkF := if pk2 < countHeld (b2.sudo_5Board_4held.set ⟨1, h1D2⟩ true) 7
    then countHeld (b2.sudo_5Board_4held.set ⟨1, h1D2⟩ true) 7 else pk2
  have hszDF : bF.sudo_5Board_4held.size = 8 := by
    have hs := congrArg Array.size hheldF
    simpa [bF, Array.size_set, hszD2] using hs
  have hszHF : bF.sudo_5Board_4home.size = 8 := by
    have hs := congrArg Array.size hhomeF
    simpa [bF, Array.size_set, hszH2] using hs
  unfold Ecbs.frobenius_affine
  rw [show Ecbs.across = ((0 : Nat) : Int) from rfl,
      show Ecbs.up = ((1 : Nat) : Int) from rfl]
  rw [hcube1, ok_bind]
  dsimp only
  rw [hset1, hcube2, ok_bind, hbF, ok_bind, pure_eq_ok]
  refine ⟨bF, mvF, slF, pkF, rfl, ?_, hoffF, hszHF, hszDF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmkF]; exact hmk2
  · simpa [bF] using htierF.trans
      ((cube_off_tier bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS).trans
        (htierS.trans (htier1.trans hT)))
  · intro h0
    have hget := get_eq_of_array hheldF 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array
      (cube_off_held bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS) 0
      (by rw [hszD2]; decide)
    have hne0 : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne0] at hsrc
    have hS := get_eq_of_array hheldS 0 (by rw [hszDS]; decide)
    simp only [Array.getElem_set] at hS
    exact hget.trans (hsrc.trans hS)
  · intro h0
    have hget := get_eq_of_array hhomeF 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array
      (cube_off_home bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS) 0
      (by rw [hszH2]; decide)
    have hne0 : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne0] at hsrc
    have hS := get_eq_of_array hhomeS 0 (by rw [hszHS]; decide)
    simp only [Array.getElem_set] at hS
    have hlenTake : (laneX.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left (by rw [hlenX]; exact hnb)]
    simpa [bF, htakeX, n, k, bench] using hget.trans (hsrc.trans hS)
  · intro h1
    have hget := get_eq_of_array hheldF 1 h1
    simp only [Array.getElem_set] at hget
    exact hget
  · intro h1
    have hget := get_eq_of_array hhomeF 1 h1
    simp only [Array.getElem_set] at hget
    simpa [htakeY, n, k, bench] using hget
  · intro j hj2 hj7 hD hH hDb hHb
    have hne1 : (1 : Nat) ≠ j := by omega
    have hne0 : (0 : Nat) ≠ j := by omega
    have hgetD := get_eq_of_array hheldF j hD
    simp only [Array.getElem_set, hne1] at hgetD
    have hD2 : j < b2.sudo_5Board_4held.size := by rw [hszD2]; omega
    have hsrcD := get_eq_of_array
      (cube_off_held bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS) j hD2
    simp only [Array.getElem_set, hne1] at hsrcD
    have hDS : j < bS.sudo_5Board_4held.size := by rw [hszDS]; omega
    have hSD := get_eq_of_array hheldS j hDS
    simp only [Array.getElem_set, hne0] at hSD
    have hD1 : j < b1.sudo_5Board_4held.size := by rw [hszD1]; omega
    have h1Dget := get_eq_of_array
      (cube_off_held b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) j hD1
    simp only [Array.getElem_set, hne0] at h1Dget
    have hgetH := get_eq_of_array hhomeF j hH
    simp only [Array.getElem_set, hne1] at hgetH
    have hH2 : j < b2.sudo_5Board_4home.size := by rw [hszH2]; omega
    have hsrcH := get_eq_of_array
      (cube_off_home bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS) j hH2
    simp only [Array.getElem_set, hne1] at hsrcH
    have hHS : j < bS.sudo_5Board_4home.size := by rw [hszHS]; omega
    have hSH := get_eq_of_array hhomeS j hHS
    simp only [Array.getElem_set, hne0] at hSH
    have hH1 : j < b1.sudo_5Board_4home.size := by rw [hszH1]; omega
    have h1Hget := get_eq_of_array
      (cube_off_home b 0 0 x n k moves holeN bench pk peakS cOps hops1 h0D h0H) j hH1
    simp only [Array.getElem_set, hne0] at h1Hget
    exact ⟨hgetD.trans (hsrcD.trans (hSD.trans h1Dget)),
      hgetH.trans (hsrcH.trans (hSH.trans h1Hget))⟩
  · simpa [bF, mvF, pegY] using hmovF
  · simpa [bF, slF, pegY] using hslFeq
  · simpa [bF, pkF] using hpeakF
  · dsimp [mvF]
    have : 2 * pegY ≤ 2 * n := Nat.mul_le_mul_left 2 hpegY
    have hmvSle' : mvS ≤ moves + 4 * n + 3 * (bench - n) := hmvSle
    omega
  · dsimp [slF, slS]
    have : 2 * pegY ≤ 2 * n := Nat.mul_le_mul_left 2 hpegY
    have : 2 * pegX ≤ 2 * n := Nat.mul_le_mul_left 2 hpegX
    omega
  · have hopsF := settle_ops b2 1 h1H2 h1D2 laneY n mv2 slS pk2
    have hsz : b2.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [b2, Array.size_set] using congrArg Array.size
        (cube_off_ops bS 1 1 y n k mvS hole1 bench pkS peakS1 (cOps + 1) hops1S h1DS h1HS)
    have hsz2 : 1 < b2.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hsz]; exact hops1S
    have hszF : bF.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b2.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [bF] using congrArg Array.size hopsF
    rw [hszF]
    exact hsz2

end EcbsLink2.Link2
