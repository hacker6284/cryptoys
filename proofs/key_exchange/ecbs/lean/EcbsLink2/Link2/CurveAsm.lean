/-
  `curve_test` is `new_board`, the two puts, and `on_curve`.
  The pieces are the curve lemmas; this file only chains them.
-/
import EcbsLink2.Link2.CurveTest
import EcbsLink2.Link2.CurveCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem curve_decide_onCurve (n k bench : Nat) (x y : List Nat) :
    decide (fieldMul n k bench y y =
        fieldAdd n
          (fieldAdd n (fieldCube n k bench x) (mirrorTrits (fieldMul n k bench x x)))
          (1 :: List.replicate (n - 1) 0)) =
      onCurve n k bench x y := by
  unfold onCurve
  rfl

/-- From the board that already holds `x³`, `x²`, and `y²`, the rest of `on_curve`
    is the spec predicate. -/
theorem curve_suffix (b : Ecbs.Board) (x y x3 x2 y2 : List Nat) (n k bench moves : Nat)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hheld2 : b.sudo_5Board_4held[2] = true)
    (harr2 : b.sudo_5Board_4home[2] = embed x3)
    (hheld5 : b.sudo_5Board_4held[5] = true)
    (harr5 : b.sudo_5Board_4home[5] = embed y2)
    (hheld6 : b.sudo_5Board_4held[6] = true)
    (harr6 : b.sudo_5Board_4home[6] = embed x2)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx3 : x3.length = n) (hx2 : x2.length = n) (hy2 : y2.length = n) (hpos : 0 < n)
    (ht3 : allTritList x3) (ht2 : allTritList x2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hf : FitsLen n)
    (hfitC : FitsLen (moves + pegCount x2 + pegCount x2))
    (hfitW : FitsLen (moves + pegCount x2 + pegCount x2 + 1))
    (hfitG : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2))
    (hfitBot : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2 + n))
    (hx3f : x3 = fieldCube n k bench x) (hx2f : x2 = fieldMul n k bench x x)
    (hy2f : y2 = fieldMul n k bench y y) :
    ∃ bF,
      (Ecbs.add b Ecbs.bottom Ecbs.spare true >>= fun b1 =>
        Ecbs.clear b1 Ecbs.spare >>= fun b2 =>
        Ecbs.white0 b2 Ecbs.bottom >>= fun b3 =>
        Ecbs.value b3 Ecbs.gap >>= fun g =>
        Ecbs.value b3 Ecbs.bottom >>= fun bot =>
        Ecbs.clear b3 Ecbs.gap >>= fun b4 =>
        Ecbs.clear b4 Ecbs.bottom >>= fun b5 =>
        pure (SudoRt.SEq.beq g bot, b5)) =
        .ok (onCurve n k bench x y, bF) := by
  obtain ⟨bF, h⟩ := curve_white_beq b x3 x2 y2 n moves h2H h2D h5H h5D h6H h6D
    hheld2 harr2 hheld5 harr5 hheld6 harr6 hn hx3 hx2 hy2 hpos ht3 ht2 hm hfit hf
    hfitC hfitW hfitG hfitBot
  refine ⟨bF, ?_⟩
  rw [h, hx3f, hx2f, hy2f, curve_decide_onCurve]

private theorem fitsCap {k : Nat}
    (hk : k ≤ 4 * (1000000 * 1000001) + 40 * 1000001) : FitsLen k := by
  have hbig : 4 * (1000000 * 1000001) + 40 * 1000001 ≤ 9223372036854775807 := by
    decide
  unfold FitsLen i64MaxNat
  omega

/-- A counter under two schoolbooks, on a `FieldLay` tier, still fits an i64. -/
private theorem layFit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m := by
  have hp : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hn (by omega)
  have h2 : 2 * (n * (n + 1)) ≤ 2 * (1000000 * 1000001) := Nat.mul_le_mul_left 2 hp
  have h12 : 12 * bench ≤ 12 * 1000001 := Nat.mul_le_mul_left 12 hb
  have h24 : 24 * n ≤ 24 * 1000000 := Nat.mul_le_mul_left 24 hn
  have hsum : 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ≤
      4 * (1000000 * 1000001) + 40 * 1000001 := by omega
  exact fitsCap (Nat.le_trans hm hsum)

private theorem take_self (xs : List Nat) (n : Nat) (h : xs.length = n) : xs.take n = xs := by
  rw [← h]
  exact List.take_length xs

theorem zeroPeg_length (n : Nat) : (zeroPeg n).length = n := by
  simp [zeroPeg]

theorem zeroPeg_trits (n : Nat) : allTritList (zeroPeg n) := by
  intro x hx
  simp [zeroPeg, List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩
  decide

private theorem mulPeak_h6 (held0 heldF : Array Bool) (h6 h6' : 6 < held0.size) (peak : Nat) :
    mulPeak held0 heldF h6 peak = mulPeak held0 heldF h6' peak := by
  have hs : held0.set ⟨6, h6⟩ true = held0.set ⟨6, h6'⟩ true := by
    apply Array.ext
    · simp [Array.size_set]
    · intro i hi hi'
      by_cases h : i = 6
      · simp [h, Array.getElem_set]
      · simp [Array.getElem_set, h]
  unfold mulPeak
  rw [hs]

private theorem set_true_id (a : Array Bool) (i : Nat) (hi : i < a.size) (ht : a[i] = true) :
    a.set ⟨i, hi⟩ true = a := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j hj hj'
    by_cases h : j = i
    · simp [h, Array.getElem_set, ht]
    · have hne : i ≠ j := Ne.symm h
      simp [Array.getElem_set, hne]

private theorem settle_off_mark (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8bench_on = false ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + 2 * pegCount (xs.take n)) ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (xs.take n)) := by
  unfold settleBoard
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals split <;> rfl

private theorem settle_peak_of (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨home, hD⟩ true) 7)) := by
  unfold settleBoard raisedPeak
  split
  · next hlt => simp [hlt]
  · next hnk => simpa [hnk, ofNat_eq_natCast] using hpeak

private theorem place_lane (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_5bench = b.sudo_5Board_5bench ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size ∧
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold placeBoard
  dsimp only
  split <;> simp [Array.size_set]

/-- `on_curve` after the two puts is the cube of the settled gap, then the spare
    multiply, the settle, and the add-through-clears tail. The board in the cube is
    named, not unfolded. The conjuncts are the fields the cube step reads. -/
theorem curve_on_prefix (t : Spec.Tier) (lay : FieldLay t) (sat : TierSat t)
    (x y : List Nat) (hx : x.length = t.n) (hy : y.length = t.n)
    (_hxt : allTritList x) (hyt : allTritList y) :
    ∃ (b : Ecbs.Board) (lane : List Nat) (moves pk peakS holeN : Nat)
      (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
      (hops1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      Ecbs.on_curve (boardCurve t x y) =
        (Ecbs.cube (settleBoard b 5 h5H h5D lane t.n moves 0 pk) Ecbs.bottom Ecbs.bottom >>= fun bC =>
          Ecbs.mul bC Ecbs.spare Ecbs.base_across Ecbs.base_across true false false >>= fun bM =>
          Ecbs.settle bM >>= fun bS =>
          Ecbs.add bS Ecbs.bottom Ecbs.spare true >>= fun bA =>
          Ecbs.clear bA Ecbs.spare >>= fun bW =>
          Ecbs.white0 bW Ecbs.bottom >>= fun b3 =>
          Ecbs.value b3 Ecbs.gap >>= fun g =>
          Ecbs.value b3 Ecbs.bottom >>= fun bot =>
          Ecbs.clear b3 Ecbs.gap >>= fun b4 =>
          Ecbs.clear b4 Ecbs.bottom >>= fun b5 =>
          pure (SudoRt.SEq.beq g bot, b5)) ∧
      b.sudo_5Board_9marker_on = false ∧
      b.sudo_5Board_8bench_on = true ∧
      b.sudo_5Board_8bench_to = Ecbs.gap ∧
      b.sudo_5Board_4held[5]'h5D = false ∧
      b.sudo_5Board_5bench = embed lane ∧
      b.sudo_5Board_1t = embTier t ∧
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0 ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
      (∀ (h : 2 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[2] = embed x) ∧
      (∀ (h : 2 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[2] = true) ∧
      (∀ (h : 3 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[3] = embed x) ∧
      (∀ (h : 3 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[3] = true) ∧
      (∀ (h : 4 < b.sudo_5Board_4home.size), b.sudo_5Board_4home[4] = embed y) ∧
      (∀ (h : 4 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[4] = true) ∧
      (∀ (h : 6 < b.sudo_5Board_4held.size), b.sudo_5Board_4held[6] = false) ∧
      b.sudo_5Board_4home.size = 8 ∧
      b.sudo_5Board_4held.size = 8 ∧
      0 < lane.length ∧
      t.n ≤ lane.length ∧
      (∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0) ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops1 = (0 : Int) ∧
      (∀ (h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
        b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1) ∧
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS ∧
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN ∧
      lane.take t.n = fieldMul t.n t.k t.benchlen y y ∧
      moves ≤ t.n * (t.n + 1) + 3 * (t.benchlen - t.n) + 6 * t.n := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let cg := t.combgap
  have hn0 : 0 < n := lay.board.n_pos
  have hnb : n ≤ bench := by have hs := lay.mul_span; omega
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have hfn : FitsLen n := fits_small hnsm
  have hfb : FitsLen bench := layFit n bench bench hnsm hbnd (by omega)
  have h3span : 3 * (n - 1) < bench := cube_span_le n bench cg sat.cube_span
  have h3fit : FitsLen (3 * (n - 1)) := layFit n bench _ hnsm hbnd (by omega)
  let schY := school n y y (List.replicate bench 0) false
  let yLane := laneFold n (n - k) schY
  let comb := combStrip n bench x
  let cLane := laneFold n (n - k) comb
  let schX := school n x x (List.replicate bench 0) false
  let xLane := laneFold n (n - k) schX
  have hschY : schY.length = bench := by
    simpa [schY, List.length_replicate] using
      school_length y y (List.replicate bench 0) false n
  have hschX : schX.length = bench := by
    simpa [schX, List.length_replicate] using
      school_length x x (List.replicate bench 0) false n
  have hcomb : comb.length = bench := combStrip_length n bench x
  have hyl : yLane.length = bench := by
    change (laneFold n (n - k) schY).length = bench
    rw [laneFold_length n (n - k) schY (by rw [hschY]; exact hnb)]
    exact hschY
  have hcl : cLane.length = bench := by
    change (laneFold n (n - k) comb).length = bench
    rw [laneFold_length n (n - k) comb (by rw [hcomb]; exact hnb)]
    exact hcomb
  have hxl : xLane.length = bench := by
    change (laneFold n (n - k) schX).length = bench
    rw [laneFold_length n (n - k) schX (by rw [hschX]; exact hnb)]
    exact hschX
  have hpx : pegCount x ≤ n := by simpa [hx, n] using pegCount_le x
  have hpy : pegCount y ≤ n := by simpa [hy, n] using pegCount_le y
  have hpegY : pegCount (yLane.take n) ≤ n :=
    Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hpegC : pegCount (cLane.take n) ≤ n :=
    Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hpegXl : pegCount (xLane.take n) ≤ n :=
    Nat.le_trans (pegCount_le _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hsmY : schoolMoves y y n n ≤ n * (n + 1) := schoolMoves_bound y y n
  have hsmX : schoolMoves x x n n ≤ n * (n + 1) := schoolMoves_bound x x n
  have hfcY : foldCharge n (n - k) schY ≤ 3 * (bench - n) := by
    simpa [hschY] using foldCharge_bound n (n - k) schY
  have hfcX : foldCharge n (n - k) schX ≤ 3 * (bench - n) := by
    simpa [hschX] using foldCharge_bound n (n - k) schX
  let mv1 := mulMoves (pegCount x + pegCount y) y y n k bench
  have hmv1 : mv1 =
      (pegCount x + pegCount y) + pegCount y + schoolMoves y y n n +
        foldCharge n (n - k) schY := by
    simp [mv1, mulMoves, schY]
  have hmv1le : mv1 ≤ n * (n + 1) + 3 * (bench - n) + 3 * n := by
    rw [hmv1]; omega
  let mvCopy := mv1 + pegCount x
  let mvGap := mvCopy + 2 * pegCount (yLane.take n)
  have hmvGapLe : mvGap ≤ n * (n + 1) + 3 * (bench - n) + 6 * n := by
    dsimp [mvGap, mvCopy]; omega
  /- The settle after the across copy charges `mv1`, the copied pegs, and twice
     the pegs in the length-`n` prefix of the gap lane. -/
  have hfitGap : FitsLen (mv1 + pegCount x + 2 * pegCount (yLane.take n)) := by
    have hpt : pegCount (yLane.take n) ≤ (yLane.take n).length := pegCount_le _
    have hlenT : (yLane.take n).length ≤ n := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    have hxLen : x.length = n := by simpa [n] using hx
    have hyLen : y.length = n := by simpa [n] using hy
    have hsm := schoolMoves_bound y y n
    have hfb := foldCharge_bound n (n - k) schY
    have hsch : schY.length = bench := hschY
    rw [hsch] at hfb
    have hmvEq : mv1 = (pegCount x + pegCount y) + pegCount y + schoolMoves y y n n +
        foldCharge n (n - k) schY := hmv1
    have hle : mv1 + pegCount x + 2 * pegCount (yLane.take n) ≤
        n * (n + 1) + 3 * (bench - n) + 6 * n := by
      rw [hmvEq]
      have hpx' : pegCount x ≤ n := by simpa [hxLen] using pegCount_le x
      have hpy' : pegCount y ≤ n := by simpa [hyLen] using pegCount_le y
      have hpt' : pegCount (yLane.take n) ≤ n := Nat.le_trans hpt hlenT
      omega
    have hp : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hnsm (by omega)
    have h3b : 3 * bench ≤ 3 * 1000001 := Nat.mul_le_mul_left 3 hbnd
    have h6n : 6 * n ≤ 6 * 1000000 := Nat.mul_le_mul_left 6 hnsm
    have hcap : n * (n + 1) + 3 * (bench - n) + 6 * n ≤
        4 * (1000000 * 1000001) + 40 * 1000001 := by omega
    unfold FitsLen i64MaxNat
    have hbig : 4 * (1000000 * 1000001) + 40 * 1000001 ≤ 9223372036854775807 := by
      decide
    omega
  let mvCube := cubeMoves mvGap x n k bench
  have hcubeLe : mvCube ≤ mvGap + 2 * n + 3 * (bench - n) := cubeMoves_le mvGap x n k bench
  have hmvCubeLe : mvCube ≤ n * (n + 1) + 6 * (bench - n) + 8 * n := by omega
  let mvPre := mvCube + 2 * pegCount (cLane.take n)
  let mvMul := mulMoves mvPre x x n k bench
  have hmvMul : mvMul = mvPre + pegCount x + schoolMoves x x n n +
      foldCharge n (n - k) schX := by
    simp [mvMul, mulMoves, schX]
  have hmvMulLe : mvMul ≤ 2 * (n * (n + 1)) + 9 * (bench - n) + 11 * n := by
    rw [hmvMul]; omega
  let mvSet := mvMul + 2 * pegCount (xLane.take n)
  have hmvSetLe : mvSet ≤ 2 * (n * (n + 1)) + 9 * (bench - n) + 13 * n := by
    dsimp [mvSet]; omega
  have fit (m : Nat) (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m :=
    layFit n bench m hnsm hbnd hm
  obtain ⟨b1, hmul, hon1, hto1, hbench1, htake1, h3, h4, _h2e, hh3, hh4, hh2, hhs, hds,
      _h5e, hh5, hhigh, hmov, hpeak1, htier, hslides, hmk1, hops1, hstrict1, hhole1, hh6,
      hfit1⟩ :=
    curve_mul_gap t lay x y hx hy hyt
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h2D1 : 2 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h3H1 : 3 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h3D1 : 3 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h5H1 : 5 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h5D1 : 5 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h6H1 : 6 < b1.sudo_5Board_4home.size := by rw [hhs]; decide
  have h6D1 : 6 < b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h7b : 7 ≤ b1.sudo_5Board_4held.size := by rw [hds]; decide
  have h6U : 6 < (boardCurve t x y).sudo_5Board_4held.size := by
    simp [boardCurve, baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]
  let pk1 := mulPeak (boardCurve t x y).sudo_5Board_4held b1.sudo_5Board_4held h6U 2
  have hpeakPk : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (pk1 : Int) := by
    simpa [pk1] using hpeak1
  have htakeY : yLane.take n = fieldMul n k bench y y := by
    simpa [yLane, schY, n, k, bench] using htake1
  have hbenchY : b1.sudo_5Board_5bench = embed yLane := by
    simpa [yLane, schY, n, k, bench] using hbench1
  have hzeroY : ∀ i, n ≤ i → ∀ hi : i < yLane.length, yLane[i] = 0 := by
    intro i hi hii
    have hbi : i < bench := by rw [← hyl]; exact hii
    have hc := hhigh i hi hbi
    have hget := coeff_eq_get yLane i hii
    rw [← hget]
    simpa [yLane, schY, n, k, bench] using hc
  have hposY : 0 < yLane.length := by rw [hyl]; omega
  let bCopy := placeBoard b1 2 h2H1 h2D1 x mv1 pk1
  have hcopy := curve_copy_across b1 x n mv1 pk1 h2H1 h2D1 h3H1 h3D1 h7b
    (hh3 h3D1) (h3 h3H1) (hh2 h2D1)
    (by rw [htier]; exact ofNat_eq_natCast n)
    (by simpa [n] using hx) hfn
    (by simpa [mv1, n, k, bench] using hmov)
    hpeakPk hfit1
  have hlane := place_lane b1 2 h2H1 h2D1 x mv1 pk1
  have hidle := place_idle b1 2 h2H1 h2D1 x mv1 pk1
  have h2b : 2 < bCopy.sudo_5Board_4held.size := by
    rw [show bCopy.sudo_5Board_4held.size = b1.sudo_5Board_4held.size from by
      simpa [bCopy] using hlane.2.2.2]
    exact h2D1
  have h5Hb : 5 < bCopy.sudo_5Board_4home.size := by
    rw [show bCopy.sudo_5Board_4home.size = b1.sudo_5Board_4home.size from by
      simpa [bCopy] using hlane.2.2.1]
    exact h5H1
  have h5Db : 5 < bCopy.sudo_5Board_4held.size := by
    rw [show bCopy.sudo_5Board_4held.size = b1.sudo_5Board_4held.size from by
      simpa [bCopy] using hlane.2.2.2]
    exact h5D1
  have h7c : 7 ≤ bCopy.sudo_5Board_4held.size := by
    rw [show bCopy.sudo_5Board_4held.size = b1.sudo_5Board_4held.size from by
      simpa [bCopy] using hlane.2.2.2]
    exact h7b
  have hmovC : bCopy.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvCopy := by
    simpa [bCopy, mvCopy] using place_moves b1 2 h2H1 h2D1 x mv1 pk1
  have hslideC : bCopy.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0 := by
    rw [show bCopy.sudo_5Board_4cost.sudo_5Costs_6slides =
      b1.sudo_5Board_4cost.sudo_5Costs_6slides from by simpa [bCopy] using hidle.2.2.2.1]
    simpa [ofNat_eq_natCast] using hslides
  have hheldCopy : bCopy.sudo_5Board_4held = b1.sudo_5Board_4held.set ⟨2, h2D1⟩ true := by
    simp [bCopy, placeBoard]
    split <;> rfl
  have hoccEq : countHeld (bCopy.sudo_5Board_4held.set ⟨2, h2b⟩ true) 7 =
      countHeld (b1.sudo_5Board_4held.set ⟨2, h2D1⟩ true) 7 := by
    have hset : bCopy.sudo_5Board_4held.set ⟨2, h2b⟩ true =
        b1.sudo_5Board_4held.set ⟨2, h2D1⟩ true := by
      apply Array.ext
      · simp [hheldCopy, Array.size_set]
      · intro i hi hi'
        by_cases h : i = 2
        · simp [h, hheldCopy, Array.getElem_set]
        · have hne : (2 : Nat) ≠ i := Ne.symm h
          simp [hheldCopy, Array.getElem_set, hne]
    exact countHeld_congr _ _ hset 7
  have hpeakC : bCopy.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pk1 (countHeld (bCopy.sudo_5Board_4held.set ⟨2, h2b⟩ true) 7)) := by
    rw [hoccEq]
    simpa [bCopy, raisedPeak] using
      place_peak b1 2 h2H1 h2D1 x mv1 pk1 hpeakPk
  have hbenchC : bCopy.sudo_5Board_5bench = embed yLane := by
    rw [show bCopy.sudo_5Board_5bench = b1.sudo_5Board_5bench from by
      simpa [bCopy] using hlane.1, hbenchY]
  have htoC : bCopy.sudo_5Board_8bench_to = Ecbs.gap := by
    rw [show bCopy.sudo_5Board_8bench_to = b1.sudo_5Board_8bench_to from by
      simpa [bCopy] using hlane.2.1, hto1]
  have honC : bCopy.sudo_5Board_8bench_on = true := by
    rw [show bCopy.sudo_5Board_8bench_on = b1.sudo_5Board_8bench_on from by
      simpa [bCopy] using hidle.2.1]
    exact hon1
  have hmkC : bCopy.sudo_5Board_9marker_on = false := by
    rw [show bCopy.sudo_5Board_9marker_on = b1.sudo_5Board_9marker_on from by
      simpa [bCopy] using hidle.1]
    exact hmk1
  have hempty5 : bCopy.sudo_5Board_4held[5] = false := by
    have hF : 5 < bCopy.sudo_5Board_4held.size := h5Db
    have hgot := place_held_other b1 2 5 h2H1 h2D1 x mv1 pk1 (by decide) h5D1 hF
    simpa [bCopy] using hgot.trans (hh5 h5D1)
  have htCopy : bCopy.sudo_5Board_1t = embTier t := by
    rw [show bCopy.sudo_5Board_1t = b1.sudo_5Board_1t from by simpa [bCopy] using hidle.2.2.2.2.1,
      htier]
  have hnC : bCopy.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htCopy]; exact ofNat_eq_natCast n
  have hopsC : bCopy.sudo_5Board_4cost.sudo_5Costs_3ops =
      b1.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simpa [bCopy] using hidle.2.2.1
  have hopsSzC : 1 < bCopy.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsC, hops1]
    simp [boardCurve, baseAcrossBoard, built_ops_blank, Array.size_set, Array.size_mkArray]
  have hop1C : bCopy.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hopsSzC = (0 : Int) := by
    have hget := get_eq_of_array hopsC 1 hopsSzC
    simpa [hops1, boardCurve, baseAcrossBoard, built_ops_blank, Array.getElem_set,
      Array.getElem_mkArray] using hget
  have hstrictC : bCopy.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b1.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
    simpa [bCopy] using hidle.2.2.2.2.2.1
  have hholeC : bCopy.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b1.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
    simpa [bCopy] using hidle.2.2.2.2.2.2
  have hcubeEq := curve_cube_settles bCopy yLane n mvCopy 0 pk1 0
    hmkC honC htoC h5Hb h5Db h2b h7c hempty5 hbenchC hnC hposY
    (by rw [hyl]; exact hnb) hzeroY hfn (by rw [hyl]; exact hfb) hmovC hslideC hpeakC
    (fit (2 * pegCount (yLane.take n)) (by omega)) hfitGap
    (fit (0 + 2 * pegCount (yLane.take n)) (by omega)) hopsSzC hop1C
    (fit 1 (by omega))
  have hop0b : ∀ (h : 0 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      b1.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1 := by
    intro h
    have hget := get_eq_of_array hops1 0 h
    simpa [boardCurve, baseAcrossBoard, built_ops_blank, Array.getElem_set,
      Array.getElem_mkArray] using hget
  obtain ⟨hszHc, hszDc, hhome2, hheld2, hhome3, hheld3, hhome4, hheld4, hheld6,
      hstrictEq, hholeEq, hop0⟩ :=
    curve_copy_pack b1 x y mv1 pk1 h2H1 h2D1 hhs hds h3 h4 hh3 hh4 hh6 hop0b
  have hstrictEx : ∃ peakS,
      bCopy.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat peakS :=
    ⟨_, hstrictEq.trans hstrict1⟩
  obtain ⟨peakS, hstrictPk⟩ := hstrictEx
  have hholeEx : ∃ holeN,
      bCopy.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN :=
    ⟨_, hholeEq.trans hhole1⟩
  obtain ⟨holeN, hholePk⟩ := hholeEx
  have hmvB : mvCopy ≤ n * (n + 1) + 3 * (bench - n) + 6 * n := by
    have hle : mvCopy ≤ mvGap := by
      dsimp [mvGap]
      omega
    exact Nat.le_trans hle hmvGapLe
  refine ⟨bCopy, yLane, mvCopy,
      raisedPeak pk1 (countHeld (bCopy.sudo_5Board_4held.set ⟨2, h2b⟩ true) 7),
      peakS, holeN, h5Hb, h5Db, hopsSzC, ?_, hmkC, honC, htoC, hempty5, hbenchC,
      htCopy, ?_, hslideC, hpeakC, hhome2, hheld2, hhome3, hheld3, hhome4, hheld4,
      hheld6, hszHc, hszDc, hposY, ?_, ?_, hop1C, hop0, hstrictPk, hholePk, ?_, hmvB⟩
  · unfold Ecbs.on_curve
    rw [hmul, ok_bind]
    dsimp only
    rw [hcopy, ok_bind]
    rw [hcubeEq]
  · simpa [ofNat_eq_natCast] using hmovC
  · rw [hyl]; exact hnb
  · simpa [n] using hzeroY
  · simpa [n, k, bench] using htakeY

end EcbsLink2.Link2
