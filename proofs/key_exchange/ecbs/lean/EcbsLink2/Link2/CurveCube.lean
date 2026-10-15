/-
  The cube in `on_curve`, read off an abstract board. `settleBoard` stays a
  name: each field is a projection lemma. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.CurveCopy
import EcbsLink2.Link2.SlideGap

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem set_true_id (a : Array Bool) (i : Nat) (hi : i < a.size) (ht : a[i] = true) :
    a.set ⟨i, hi⟩ true = a := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j hj hj'
    by_cases h : j = i
    · simp [h, Array.getElem_set, ht]
    · have hne : i ≠ j := Ne.symm h
      simp [Array.getElem_set, hne]

private theorem settledCube_le (moves peg n bench : Nat)
    (hm : moves ≤ n * (n + 1) + 3 * (bench - n) + 6 * n) (hp : peg ≤ n) :
    moves + 2 * peg ≤ n * (n + 1) + 3 * (bench - n) + 8 * n ∧
    moves + 2 * peg + 2 * n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    moves + 2 * peg + 2 * n + 3 * (bench - n) ≤
      2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    3 * (n - 1) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    bench ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    (1 : Nat) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

private theorem cubed_le (mvS n bench : Nat)
    (hm : mvS ≤ n * (n + 1) + 3 * (bench - n) + 8 * n) :
    mvS + 2 * n + 3 * (bench - n) ≤ n * (n + 1) + 6 * (bench - n) + 10 * n := by
  omega

private theorem twoPeg_le (peg n : Nat) (hp : peg ≤ n) : 0 + 2 * peg ≤ 2 * n := by
  omega

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

/-- `cube (settleBoard b …)` on the gap copy. The result is a variable `bC`
    plus the fields the spare multiply reads. -/
theorem curve_cube_step (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (b : Ecbs.Board) (x y lane : List Nat) (moves pk peakS holeN : Nat)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (hops1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hx : x.length = t.n) (hxt : allTritList x)
    (hmk : b.sudo_5Board_9marker_on = false)
    (_hon : b.sudo_5Board_8bench_on = true)
    (_hto : b.sudo_5Board_8bench_to = Ecbs.gap)
    (_hempty5 : b.sudo_5Board_4held[5]'h5D = false)
    (_hbench : b.sudo_5Board_5bench = embed lane)
    (hT : b.sudo_5Board_1t = embTier t)
    (_hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (_hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk)
    (hhome2 : ∀ (h : 2 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[2] = embed x)
    (hheld2 : ∀ (h : 2 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[2] = true)
    (hhome3 : ∀ (h : 3 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[3] = embed x)
    (hheld3 : ∀ (h : 3 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[3] = true)
    (hhome4 : ∀ (h : 4 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[4] = embed y)
    (hheld4 : ∀ (h : 4 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[4] = true)
    (hheld6 : ∀ (h : 6 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[6] = false)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (_hpos : 0 < lane.length) (_hnle : t.n ≤ lane.length)
    (_hzero : ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops1 = (0 : Int))
    (hop0 : ∀ (h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1)
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (htake : lane.take t.n = fieldMul t.n t.k t.benchlen y y)
    (hmv : moves ≤ t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 6 * t.n) :
    ∃ (bC : Ecbs.Board) (pkC peakC holeC mvC slC : Nat),
      Ecbs.cube (settleBoard b 5 h5H h5D lane t.n moves 0 pk) Ecbs.bottom Ecbs.bottom =
        .ok bC ∧
      bC.sudo_5Board_9marker_on = false ∧
      bC.sudo_5Board_8bench_on = true ∧
      bC.sudo_5Board_8bench_to = Ecbs.bottom ∧
      bC.sudo_5Board_5bench =
        embed (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)) ∧
      (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).take t.n =
        fieldCube t.n t.k t.benchlen x ∧
      (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).length = t.benchlen ∧
      (∀ i, t.n ≤ i →
        ∀ hi : i < (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).length,
          (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x))[i] = 0) ∧
      bC.sudo_5Board_4home.size = 8 ∧
      bC.sudo_5Board_4held.size = 8 ∧
      (∀ (h : 2 < bC.sudo_5Board_4held.size), bC.sudo_5Board_4held[2] = false) ∧
      (∀ (h : 2 < bC.sudo_5Board_4home.size), bC.sudo_5Board_4home[2] = (#[] : Array Int)) ∧
      (∀ (h : 3 < bC.sudo_5Board_4held.size), bC.sudo_5Board_4held[3] = true) ∧
      (∀ (h : 3 < bC.sudo_5Board_4home.size), bC.sudo_5Board_4home[3] = embed x) ∧
      (∀ (h : 4 < bC.sudo_5Board_4held.size), bC.sudo_5Board_4held[4] = true) ∧
      (∀ (h : 4 < bC.sudo_5Board_4home.size), bC.sudo_5Board_4home[4] = embed y) ∧
      (∀ (h : 5 < bC.sudo_5Board_4held.size), bC.sudo_5Board_4held[5] = true) ∧
      (∀ (h : 5 < bC.sudo_5Board_4home.size),
        bC.sudo_5Board_4home[5] = embed (fieldMul t.n t.k t.benchlen y y)) ∧
      (∀ (h : 6 < bC.sudo_5Board_4held.size), bC.sudo_5Board_4held[6] = false) ∧
      bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC ∧
      bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slC ∧
      bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkC ∧
      bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakC ∧
      bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC ∧
      bC.sudo_5Board_1t = embTier t ∧
      0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ (h : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        bC.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1) ∧
      mvC ≤ t.n * (t.n + 1) + 6 * (t.benchlen - t.n) + 10 * t.n ∧
      slC ≤ 2 * t.n := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let cg := t.combgap
  let s := settleBoard b 5 h5H h5D lane n moves 0 pk
  have hheldS := settle_held_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hhomeS := settle_home_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have htierS := settle_tier_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hmovS := settle_moves_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hslS := settle_slides_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hmkS := settle_marker_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hoffS := settle_bench_off b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hstrictS := settle_strict_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hholeS := settle_hole_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hopsS := settle_ops b 5 ⟨h5H, h5D⟩ lane n moves 0 pk
  have hpeakS := settle_peak_eq b 5 ⟨h5H, h5D⟩ lane n moves 0 pk hpeak
  have hszHs : s.sudo_5Board_4home.size = 8 := by
    simp only [s, hhomeS, Array.size_set, hszH]
  have hszDs : s.sudo_5Board_4held.size = 8 := by
    simp only [s, hheldS, Array.size_set, hszD]
  have h2Db : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h2Hb : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3Db : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3Hb : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4Db : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4Hb : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6Db : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h2Ds : 2 < s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have h2Hs : 2 < s.sudo_5Board_4home.size := by rw [hszHs]; decide
  have h3Ds : 3 < s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have h3Hs : 3 < s.sudo_5Board_4home.size := by rw [hszHs]; decide
  have h4Ds : 4 < s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have h4Hs : 4 < s.sudo_5Board_4home.size := by rw [hszHs]; decide
  have h5Ds : 5 < s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have h5Hs : 5 < s.sudo_5Board_4home.size := by rw [hszHs]; decide
  have h6Ds : 6 < s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have h7s : 7 ≤ s.sudo_5Board_4held.size := by rw [hszDs]; decide
  have hheld2s : s.sudo_5Board_4held[2] = true := by
    have hget := get_eq_of_array hheldS 2 h2Ds
    have hne : (5 : Nat) ≠ 2 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hheld2 h2Db)
  have hhome2s : s.sudo_5Board_4home[2] = embed x := by
    have hget := get_eq_of_array hhomeS 2 h2Hs
    have hne : (5 : Nat) ≠ 2 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hhome2 h2Hb)
  have hset2 : s.sudo_5Board_4held.set ⟨2, h2Ds⟩ true = s.sudo_5Board_4held :=
    set_true_id _ 2 h2Ds hheld2s
  have hpkCube : s.sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak pk (countHeld (s.sudo_5Board_4held.set ⟨2, h2Ds⟩ true) 7) : Int) := by
    rw [hset2]
    simp only [s] at hpeakS
    rw [hpeakS]
    have hc : countHeld s.sudo_5Board_4held 7 =
        countHeld (b.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 := by
      simpa [s] using countHeld_congr _ _ hheldS 7
    rw [← hc, raisedPeak]
    exact ofNat_eq_natCast _
  have hfields := tier_of t s (htierS.trans hT)
  let pegY := pegCount (lane.take n)
  let mvS := moves + 2 * pegY
  have hpegY : pegY ≤ n := by
    dsimp [pegY]
    exact Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hmvS : s.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    simp only [s, mvS, pegY] at hmovS ⊢
    rw [hmovS]
    exact ofNat_eq_natCast _
  have hstrictC : s.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp only [s] at hstrictS
    rw [hstrictS, hstrict]
    exact ofNat_eq_natCast _
  have hholeC : s.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN := by
    simp only [s] at hholeS
    rw [hholeS, hhole]
  have hops1s : 1 < s.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simp only [s, hopsS]; exact hops1
  have hop1s : s.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (0 : Int) := by
    have hget := get_eq_of_array hopsS 1 hops1s
    simp only [s] at hget
    exact hget.trans hop1
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have fit (m : Nat) (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m :=
    curveLayFit n bench m hnsm hbnd hm
  have hbounds := settledCube_le moves pegY n bench hmv hpegY
  have hmvSle : mvS ≤ n * (n + 1) + 3 * (bench - n) + 8 * n := by
    simpa [mvS] using hbounds.1
  have hcube := curve_cube_bottom s x w h r n k mvS holeN bench pk peakS 0 cg (by simpa [s] using hmkS.trans hmk) (by simpa [s] using hoffS) hops1s hop1s (fit 1 hbounds.2.2.2.2.2.2) hfields.2.2.2.2.2.1 hfields.2.2.2.2.2.2 sat.cube_span h2Ds h2Hs hheld2s hhome2s h7s lay.board.n_pos (by rw [hfields.1]; exact ofNat_eq_natCast _) (by simpa [n] using hx) (fit n hbounds.2.2.2.2.1) hmvS hpkCube hstrictC hxt (fit (3 * (n - 1)) hbounds.2.2.2.1) (fit (mvS + 2 * n) (by simpa [mvS] using hbounds.2.1)) ⟨lay.w_pos, lay.h_pos, lay.r_lt, lay.r_pos, lay.n_eq, lay.k_le, lay.gap_eq⟩ hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2.1 hfields.2.1 hholeC lay.small hnsm (fit bench hbounds.2.2.2.2.2.1) (fit (mvS + 2 * n + 3 * (bench - n)) (by simpa [mvS] using hbounds.2.2.1))
  obtain ⟨bC, hok, honC, htoC, hbenchC, htakeC, hheldC, hhomeC, hmkC, hhigh, hmovC,
      hpeakC, hslidesC, htC, hopsC, hstrictC', hholeC'⟩ := hcube
  have hszHC : bC.sudo_5Board_4home.size = 8 := by
    rw [hhomeC, Array.size_set, hszHs]
  have hszDC : bC.sudo_5Board_4held.size = 8 := by
    rw [hheldC, Array.size_set, hszDs]
  let cLane := laneFold n (n - k) (combStrip n bench x)
  have hcomb : (combStrip n bench x).length = bench := combStrip_length n bench x
  have hnb : n ≤ bench := by
    have hm := lay.mul_span
    have h0 := lay.board.n_pos
    omega
  have hcl : cLane.length = bench := by
    dsimp [cLane]
    rw [laneFold_length n (n - k) (combStrip n bench x) (by rw [hcomb]; exact hnb)]
    exact hcomb
  have hzeroC : ∀ i, n ≤ i → ∀ hi : i < cLane.length, cLane[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hcl]; exact hii
    have hc := hhigh i hi hbi
    have hget := coeff_eq_get cLane i hii
    exact hget.symm.trans (by simpa [cLane, n, k, bench] using hc)
  have hheldAt {v : Bool} (j : Nat) (hj : j < bC.sudo_5Board_4held.size) (hne : j ≠ 2)
      (hs : ∀ (h : j < s.sudo_5Board_4held.size), s.sudo_5Board_4held[j] = v) :
      bC.sudo_5Board_4held[j] = v := by
    have hget := get_eq_of_array hheldC j hj
    have hne' : (2 : Nat) ≠ j := Ne.symm hne
    simp only [Array.getElem_set, hne'] at hget
    exact hget.trans (hs _)
  have hhomeAt {v : Array Int} (j : Nat) (hj : j < bC.sudo_5Board_4home.size) (hne : j ≠ 2)
      (hs : ∀ (h : j < s.sudo_5Board_4home.size), s.sudo_5Board_4home[j] = v) :
      bC.sudo_5Board_4home[j] = v := by
    have hget := get_eq_of_array hhomeC j hj
    have hne' : (2 : Nat) ≠ j := Ne.symm hne
    simp only [Array.getElem_set, hne'] at hget
    exact hget.trans (hs _)
  have hheld3s : ∀ (h : 3 < s.sudo_5Board_4held.size), s.sudo_5Board_4held[3] = true := by
    intro h
    have hget := get_eq_of_array hheldS 3 h
    have hne : (5 : Nat) ≠ 3 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hheld3 h3Db)
  have hhome3s : ∀ (h : 3 < s.sudo_5Board_4home.size), s.sudo_5Board_4home[3] = embed x := by
    intro h
    have hget := get_eq_of_array hhomeS 3 h
    have hne : (5 : Nat) ≠ 3 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hhome3 h3Hb)
  have hheld4s : ∀ (h : 4 < s.sudo_5Board_4held.size), s.sudo_5Board_4held[4] = true := by
    intro h
    have hget := get_eq_of_array hheldS 4 h
    have hne : (5 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hheld4 h4Db)
  have hhome4s : ∀ (h : 4 < s.sudo_5Board_4home.size), s.sudo_5Board_4home[4] = embed y := by
    intro h
    have hget := get_eq_of_array hhomeS 4 h
    have hne : (5 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hhome4 h4Hb)
  have hheld5s : ∀ (h : 5 < s.sudo_5Board_4held.size), s.sudo_5Board_4held[5] = true := by
    intro h
    have hget := get_eq_of_array hheldS 5 h
    simp only [Array.getElem_set] at hget
    exact hget
  have hhome5s : ∀ (h : 5 < s.sudo_5Board_4home.size),
      s.sudo_5Board_4home[5] = embed (fieldMul n k bench y y) := by
    intro h
    have hget := get_eq_of_array hhomeS 5 h
    simp only [Array.getElem_set] at hget
    simpa [n, k, bench, htake] using hget
  have hheld6s : ∀ (h : 6 < s.sudo_5Board_4held.size), s.sudo_5Board_4held[6] = false := by
    intro h
    have hget := get_eq_of_array hheldS 6 h
    have hne : (5 : Nat) ≠ 6 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans (hheld6 h6Db)
  let mvC := cubeMoves mvS x n k bench
  let slC := 0 + 2 * pegY
  have hmvCle : mvC ≤ n * (n + 1) + 6 * (bench - n) + 10 * n :=
    Nat.le_trans (by simpa [mvC] using cubeMoves_le mvS x n k bench) (cubed_le mvS n bench hmvSle)
  have hslCle : slC ≤ 2 * n := by simpa [slC] using twoPeg_le pegY n hpegY
  have hmovEq : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [mvC, mvS, pegY, n, k, bench] using hmovC
  have hslEq : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slC := by
    simp only [s] at hslS
    rw [hslidesC, hslS]
  have hop0C : ∀ (h0 : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bC.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1 := by
    intro h0
    have hget := get_eq_of_array hopsC 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsz0 : 0 < s.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [show s.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size from by simp only [s, hopsS]]
      exact Nat.lt_trans (by decide : (0 : Nat) < 1) hops1
    have hsrc := get_eq_of_array hopsS 0 hsz0
    simp only [s] at hsrc
    exact hget.trans (hsrc.trans (hop0 _))
  have hops0C : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsC, Array.size_set]
    rw [show s.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size from by simp only [s, hopsS]]
    exact Nat.lt_trans (by decide : (0 : Nat) < 1) hops1
  obtain ⟨pkC, hpkEq⟩ :=
    show ∃ pkC, bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkC from ⟨_, hpeakC⟩
  obtain ⟨peakC, hstEq⟩ :=
    show ∃ peakC, bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakC from
      ⟨_, hstrictC'⟩
  obtain ⟨holeC, hhEq⟩ :=
    show ∃ holeC, bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeC from
      ⟨_, hholeC'⟩
  refine ⟨bC, pkC, peakC, holeC, mvC, slC, ?_, hmkC, honC, ?_, hbenchC, htakeC, ?_, ?_,
      hszHC, hszDC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmovEq, hslEq,
      hpkEq, hstEq, hhEq, ?_, hops0C, hop0C, ?_, hslCle⟩
  · simpa [s, Ecbs.bottom] using hok
  · rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]; exact htoC
  · simpa [cLane, n, k, bench] using hcl
  · simpa [cLane, n] using hzeroC
  · intro h2
    have hget := get_eq_of_array hheldC 2 h2
    simp only [Array.getElem_set] at hget
    exact hget
  · intro h2
    have hget := get_eq_of_array hhomeC 2 h2
    simp only [Array.getElem_set] at hget
    exact hget
  · intro hj
    exact hheldAt 3 hj (by decide) hheld3s
  · intro hj
    exact hhomeAt 3 hj (by decide) hhome3s
  · intro hj
    exact hheldAt 4 hj (by decide) hheld4s
  · intro hj
    exact hhomeAt 4 hj (by decide) hhome4s
  · intro hj
    exact hheldAt 5 hj (by decide) hheld5s
  · intro hj
    simpa [n, k, bench] using hhomeAt 5 hj (by decide) hhome5s
  · intro hj
    exact hheldAt 6 hj (by decide) hheld6s
  · rw [htC]
    simp only [s] at htierS
    exact htierS.trans hT
  · simpa [n, bench] using hmvCle

end EcbsLink2.Link2
