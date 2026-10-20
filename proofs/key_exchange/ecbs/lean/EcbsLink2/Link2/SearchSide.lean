/-
  `curve_side` after the planted copy. The cube is `search_cube`. The spare
  multiply squares the peg, the settle seats that square, and the mirror-add
  writes `curveSide` into the bottom.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchCube
import EcbsLink2.Link2.CurveSideClose
import EcbsLink2.Link2.CheckTail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem bind_pure {α : Type} (m : Except SudoRt.Trap α) :
    (m >>= fun x => pure x) = m := by
  cases m <;> simp [ok_bind, error_bind]

private theorem curve_do_split (t : Spec.Tier) (j : Nat) :
    (do
        let b ← Ecbs.new_board (embTier t)
        let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        let b ← Ecbs.put b Ecbs.base_across x
        Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) =
      (do
        let b ← (do
          let b ← (do
            let b ← Ecbs.new_board (embTier t)
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b Ecbs.base_across x
            let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
            Ecbs.cube b Ecbs.bottom Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false
          Ecbs.settle b)
        let b ← Ecbs.add b Ecbs.bottom Ecbs.spare true
        let b ← Ecbs.clear b Ecbs.spare
        Ecbs.white0 b Ecbs.bottom) := by
  unfold Ecbs.curve_side
  simp only [bind_assoc, bind_pure]

private theorem mul_moves_cap (moves : Nat) (xs ys : List Nat) (n k bench : Nat)
    (hy : ys.length = n) :
    mulMoves moves xs ys n k bench ≤
      moves + n + n * (n + 1) + 3 * (bench - n) := by
  have hsch : (school n xs ys (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hF := foldCharge_bound n (n - k) (school n xs ys (List.replicate bench 0) false)
  rw [hsch] at hF
  have hS := schoolMoves_bound xs ys n
  have hP : pegCount ys ≤ n := by
    have h := pegCount_le ys
    rwa [hy] at h
  dsimp only [mulMoves]
  omega

private theorem side_le (mv0 mv pegL pegX n bench : Nat)
    (hm : mv ≤ mv0 + pegX + pegX + 2 * n + 3 * (bench - n))
    (hX : pegX ≤ n) (hL : pegL ≤ n) :
    let bound := mv0 + 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8
    2 * pegL ≤ bound ∧
    mv + 2 * pegL ≤ bound ∧
    mv + 2 * pegL + pegX ≤ bound ∧
    mv + 2 * pegL + pegX + n * (n + 1) ≤ bound ∧
    mv + 2 * pegL + pegX + n * (n + 1) + 3 * (bench - n) ≤ bound ∧
    mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n ≤ bound ∧
    mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n + 2 * n + 1 ≤ bound ∧
    2 * (n - 1) ≤ bound ∧
    n ≤ bound ∧
    bench ≤ bound ∧
    (1 : Nat) ≤ bound ∧
    2 * n ≤ bound := by
  omega

private theorem zero_two (a n : Nat) (ha : 2 * a ≤ n) : 0 + 2 * a ≤ n := by
  omega

private theorem two_pegs (a b n : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (0 + 2 * a) + 2 * b ≤ 2 * n + 2 * n := by
  omega

private theorem four_in_room (mv pegL n bench : Nat) :
    2 * n + 2 * n ≤
      mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n := by
  have hprod : n * 1 ≤ n * (n + 1) := Nat.mul_le_mul_left n (by omega : 1 ≤ n + 1)
  have hn : n ≤ n * (n + 1) := by simpa [Nat.mul_one] using hprod
  omega

private theorem settle_room (mvM pegS mv pegL n bench : Nat)
    (hm : mvM ≤ mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n))
    (hp : pegS ≤ n) :
    mvM + 2 * pegS ≤
      mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n := by
  omega

private theorem close_room (mvS mv pegL n bench : Nat)
    (hm : mvS ≤ mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n) :
    mvS + 2 * n + 1 ≤
      mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n + 2 * n + 1 := by
  omega

/-- Moves `curve_side` can spend on one planted peg: the cube, the spare square,
    and the mirror-add that writes the curve side. -/
def sideCap (n bench : Nat) : Nat :=
  n * (n + 1) + 11 * n + 6 * (bench - n) + 1

private theorem side_cap_le (mv0 mv pegL pegX n bench : Nat)
    (hmv : mv ≤ mv0 + pegX + pegX + 2 * n + 3 * (bench - n))
    (hL : pegL ≤ n) (hX : pegX ≤ n) :
    mv + 2 * pegL + n + n * (n + 1) + 3 * (bench - n) + 2 * n + 2 * n + 1 ≤
      mv0 + sideCap n bench := by
  unfold sideCap
  omega

private theorem close_under_cap (mv peg n bench : Nat)
    (hpeg : peg ≤ n) (h : mv + 2 * n + 1 ≤ sideCap n bench) :
    mv + 2 * peg + 1 ≤ sideCap n bench := by
  omega

private theorem four_n (sl0 a b n : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (sl0 + 2 * a) + 2 * b ≤ sl0 + 4 * n := by
  have h := two_pegs a b n ha hb
  omega

private theorem sq_trits (n k bench : Nat) (x : List Nat)
    (hx : x.length = n) (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench x x) := by
  have htk : x.take n = x := by
    have h := List.take_length x
    rwa [hx] at h
  simpa [htk] using fieldMul_trits n k bench x x hspan hn

/-- Cube, square into the spare, settle. Bottom holds `x³` and the spare holds `x²`. -/
theorem search_square (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ (bS : Ecbs.Board) (mv : Nat),
      (do
          let b ← (do
            let b ← Ecbs.new_board (embTier t)
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b Ecbs.base_across x
            let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
            Ecbs.cube b Ecbs.bottom Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false
          Ecbs.settle b) = .ok bS ∧
        (∀ h : 2 < bS.sudo_5Board_4home.size,
          bS.sudo_5Board_4home[2] = embed (fieldCube t.n t.k t.benchlen (basisPeg t.n j))) ∧
        (∀ h : 2 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[2] = true) ∧
        (∀ h : 6 < bS.sudo_5Board_4home.size,
          bS.sudo_5Board_4home[6] = embed (fieldMul t.n t.k t.benchlen
            (basisPeg t.n j) (basisPeg t.n j))) ∧
        (∀ h : 6 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[6] = true) ∧
        (∀ h : 3 < bS.sudo_5Board_4home.size,
          bS.sudo_5Board_4home[3] = embed (basisPeg t.n j)) ∧
        (∀ h : 3 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[3] = true) ∧
        bS.sudo_5Board_8bench_on = false ∧
        bS.sudo_5Board_1t = embTier t ∧
        bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        FitsLen (mv + 2 * t.n + 1) ∧
        bS.sudo_5Board_4home.size = 8 ∧
        bS.sudo_5Board_4held.size = 8 ∧
        (∀ h : 1 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[1] = false) ∧
        (∀ h : 5 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[5] = false) ∧
        bS.sudo_5Board_9marker_on = false ∧
        bS.sudo_5Board_6marker = -1 ∧
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 ∧
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
        (∀ h : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size,
          bS.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1) ∧
        (∀ h : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size,
          bS.sudo_5Board_4cost.sudo_5Costs_3ops[1] = 1) ∧
        (∀ h : 1 < bS.sudo_5Board_4home.size, bS.sudo_5Board_4home[1] = (#[] : Array Int)) ∧
        (∀ h : 5 < bS.sudo_5Board_4home.size, bS.sudo_5Board_4home[5] = (#[] : Array Int)) ∧
        (∃ sl, bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧ sl ≤ 4 * t.n) ∧
        (∃ pk, bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
        (∃ ps, bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps) ∧
        (∃ holeN, bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN) ∧
        mv + 2 * t.n + 1 ≤ sideCap t.n t.benchlen ∧
        (∀ h : 0 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[0] = false) ∧
        (∀ h : 0 < bS.sudo_5Board_4home.size, bS.sudo_5Board_4home[0] = (#[] : Array Int)) := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hpeg : pegCount x ≤ t.n := by
    have h := pegCount_le x
    rwa [hx] at h
  obtain ⟨bC, hdo, honC, htoC, hbenchC, htakeC, hlenC, hzeroC, hmkC, hszHC, hszDC,
      hheld2C, _hhome2C, hheld3C, hhome3C, hheld6C, hmovC, hslC, hpkE, hpsE, hholeE,
      htierC, hopsC, hop0C, hheld1C, hheld5C, hmarkC, hctrlC, hmxC, hopSzC, hop1C,
      hhome1C, hhome5C, hheld0C, hhome0C⟩ :=
    search_cube t hOk hsh sat j hj
  obtain ⟨pk, hpk⟩ := hpkE
  obtain ⟨ps, hps⟩ := hpsE
  obtain ⟨holeN, hhole⟩ := hholeE
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  let lane := laneFold n (n - k) (combStrip n bench x)
  let mv := cubeMoves (pegCount x + pegCount x) x n k bench
  have hmvLe := cubeMoves_le (pegCount x + pegCount x) x n k bench
  have hpegL : pegCount (lane.take n) ≤ n := pegCount_take_le lane n
  have hmv0 : mv ≤ 0 + pegCount x + pegCount x + 2 * n + 3 * (bench - n) := by
    simpa [mv, Nat.zero_add] using hmvLe
  have hroom := side_le 0 mv (pegCount (lane.take n)) (pegCount x) n bench hmv0 hpeg hpegL
  have fit (m : Nat) (hm : m ≤ 0 + 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m := by
    have hpoly : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
      simpa [Nat.zero_add] using hm
    exact curveLayFit n bench m hsh.n_small hsh.small.2.2.2 hpoly
  have hnle : n ≤ bench := by
    have hsp := sat.cube_span
    omega
  have hposC : 0 < lane.length := by
    rw [hlenC]
    have hsp := sat.cube_span
    omega
  have h2H : 2 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
  have h2D : 2 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
  have h3H : 3 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
  have h3D : 3 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
  have h6H : 6 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
  have h6D : 6 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
  have hto2 : bC.sudo_5Board_8bench_to = ((2 : Nat) : Int) := by
    rw [htoC]; rfl
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierC]; exact ofNat_eq_natCast _
  have hslI : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0 := by
    rw [hslC]; exact (ofNat_eq_natCast 0).symm
  have hpsI : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int) := by
    rw [hps]; exact ofNat_eq_natCast _
  have hmul := curve_mul_spare bC x lane t.w t.h t.r n k mv 0 holeN bench pk ps 0
    hmkC honC hto2 h2H h2D h3H h3D h6H h6D (by rw [hszDC]; decide)
    (hheld2C h2D) (hheld3C h3D) (hhome3C h3H) (hheld6C h6D)
    (by simpa [lane] using hbenchC) hnC hposC (by rw [hlenC]; exact hnle)
    (by simpa [lane] using hzeroC)
    (fit n hroom.2.2.2.2.2.2.2.2.1) (fit lane.length (by rw [hlenC]; exact hroom.2.2.2.2.2.2.2.2.2.1))
    hmovC hslI hpk hpsI
    (fit (2 * pegCount (lane.take n)) hroom.1)
    (fit (mv + 2 * pegCount (lane.take n)) hroom.2.1)
    (fit (0 + 2 * pegCount (lane.take n)) (zero_two _ _ hroom.1))
    hopsC (hop0C hopsC)
    (fit 1 hroom.2.2.2.2.2.2.2.2.2.2.1)
    hx hxt
    (by rw [htierC]; rfl) (by rw [htierC]; rfl) (by rw [htierC]; rfl) (by rw [htierC]; rfl)
    (by rw [htierC]; rfl) hhole hOk.n_pos sat.mul_span
    (fit (2 * (n - 1)) hroom.2.2.2.2.2.2.2.1)
    (fit bench hroom.2.2.2.2.2.2.2.2.2.1)
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x) hroom.2.2.1)
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1)) hroom.2.2.2.1)
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1) + 3 * (bench - n))
      hroom.2.2.2.2.1)
    ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
    hsh.small hsh.n_small
  obtain ⟨bM, hokM, honM, htoM, htakeM, hhome2M, hbenchM, hhighM, hmovM, hslM, htM,
      hheld6M, hheld2M, hheldPM, hhomeP, hszHM, hszDM, hpkM, hmkM, hmarkM, hctrlM,
      hmxM, hopsM, _hstrictM, _hholeM⟩ := hmul
  obtain ⟨pkM, hpkM⟩ := hpkM
  let laneS := laneFold n (n - k) (school n x x (List.replicate bench 0) false)
  have hlenS : laneS.length = bench := by
    have hsch : (school n x x (List.replicate bench 0) false).length = bench := by
      rw [school_length, List.length_replicate]
    dsimp [laneS]
    rw [laneFold_length n (n - k) (school n x x (List.replicate bench 0) false)
      (by rw [hsch]; exact hnle), hsch]
  have hzeroS : ∀ i, n ≤ i → ∀ hi : i < laneS.length, laneS[i] = 0 := by
    intro i hi hlt
    have hltb : i < bench := by rwa [hlenS] at hlt
    have hc := hhighM i hi hltb
    simpa [laneS, coeff_eq_get _ _ hlt] using hc
  have hposS : 0 < laneS.length := by rw [hlenS]; omega
  have h6HM : 6 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
  have h6DM : 6 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
  have h2HM : 2 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
  have h2DM : 2 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
  have h3HM : 3 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
  have h3DM : 3 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
  have hto6 : bM.sudo_5Board_8bench_to = ((6 : Nat) : Int) := by
    rw [htoM]; rfl
  have hnM : bM.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htM, htierC]; exact ofNat_eq_natCast _
  let mvM := mulMoves (mv + 2 * pegCount (lane.take n)) x x n k bench
  have hpegS : pegCount (laneS.take n) ≤ n := pegCount_take_le laneS n
  have hmvMle : mvM ≤ mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) := by
    dsimp [mvM]
    exact mul_moves_cap (mv + 2 * pegCount (lane.take n)) x x n k bench hx
  have hset := curve_settle_spare bM laneS (fieldMul n k bench x x) n mvM
      (0 + 2 * pegCount (lane.take n)) pkM
      h6HM h6DM (by rw [hszDM, hszDC]; decide) honM hto6 (hheld6M h6DM)
      (by simpa [laneS] using hbenchM) hnM hposS (by rw [hlenS]; exact hnle) hzeroS
      (fit n hroom.2.2.2.2.2.2.2.2.1)
      (fit laneS.length (by rw [hlenS]; exact hroom.2.2.2.2.2.2.2.2.2.1))
      (by simpa [mvM] using hmovM)
      hslM
      hpkM
      (fit (2 * pegCount (laneS.take n))
        (Nat.le_trans (Nat.mul_le_mul_left 2 hpegS) hroom.2.2.2.2.2.2.2.2.2.2.2))
      (fit (mvM + 2 * pegCount (laneS.take n))
        (Nat.le_trans (settle_room mvM (pegCount (laneS.take n)) mv (pegCount (lane.take n)) n bench
          hmvMle hpegS) hroom.2.2.2.2.2.1))
      (fit ((0 + 2 * pegCount (lane.take n)) + 2 * pegCount (laneS.take n))
        (Nat.le_trans (two_pegs _ _ _ hpegL hpegS)
          (Nat.le_trans (four_in_room mv (pegCount (lane.take n)) n bench) hroom.2.2.2.2.2.1)))
      (by simpa [laneS] using htakeM)
  obtain ⟨bS, hokS, hoffS, hhome6S, hheld6S, hhomePS, hheldPS, hmovS, htS, hszHS, hszDS,
      hmkS, hmarkS, hctrlS, hmxS, hopsS, hslS, hpeakS, hstrictS, hholeS⟩ := hset
  let mvS := mvM + 2 * pegCount (laneS.take n)
  have hmvInner : mvS ≤
      mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) + 2 * n := by
    dsimp [mvS]
    exact settle_room mvM (pegCount (laneS.take n)) mv (pegCount (lane.take n)) n bench hmvMle hpegS
  have hmvSle : mvS + 2 * n + 1 ≤
      mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) + 2 * n + 2 * n + 1 :=
    close_room mvS mv (pegCount (lane.take n)) n bench hmvInner
  refine ⟨bS, mvS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hoffS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdo, ok_bind, hokM, ok_bind]
    exact hokS
  · intro h
    have hget := hhomePS 2 h2HM h (by decide)
    rw [hget, hhome2M h2HM, htakeC]
  · intro h
    have hget := hheldPS 2 h2DM h (by decide)
    rw [hget]
    exact hheld2M h2DM
  · intro h
    simpa [x] using hhome6S h
  · intro h
    exact hheld6S h
  · intro h
    have hget := hhomePS 3 h3HM h (by decide)
    rw [hget]
    exact (hhomeP 3 h3H h3HM (by decide) (by decide)).trans (hhome3C h3H)
  · intro h
    have hget := hheldPS 3 h3DM h (by decide)
    rw [hget]
    exact (hheldPM 3 h3D h3DM (by decide) (by decide)).trans (hheld3C h3D)
  · rw [htS, htM, htierC]
  · simpa [mvS, ofNat_eq_natCast] using hmovS
  · exact fit (mvS + 2 * n + 1) (Nat.le_trans hmvSle hroom.2.2.2.2.2.2.1)
  · rw [hszHS, hszHM, hszHC]
  · rw [hszDS, hszDM, hszDC]
  · intro h
    have h1C : 1 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
    have h1M : 1 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
    have hM := hheldPM 1 h1C h1M (by decide) (by decide)
    have hS := hheldPS 1 h1M h (by decide)
    exact hS.trans (hM.trans (hheld1C h1C))
  · intro h
    have h5C : 5 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
    have h5M : 5 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
    have hM := hheldPM 5 h5C h5M (by decide) (by decide)
    have hS := hheldPS 5 h5M h (by decide)
    exact hS.trans (hM.trans (hheld5C h5C))
  · rw [hmkS]; exact hmkM
  · rw [hmarkS, hmarkM, hmarkC]
  · rw [hctrlS, hctrlM, hctrlC]
  · rw [hmxS, hmxM, hmxC]
  · rw [hopsS, hopsM, Array.size_set]; exact hopSzC
  · intro h
    have hM : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hsz := congrArg Array.size hopsS
      rw [hsz] at h
      exact h
    have hget := get_eq_of_array hopsM 0 hM
    simp [Array.getElem_set, Nat.zero_add, ofNat_eq_natCast] at hget
    exact cell_eq_of hopsS hget
  · intro h
    have hM : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      have hsz := congrArg Array.size hopsS
      rw [hsz] at h
      exact h
    have hget := get_eq_of_array hopsM 1 hM
    have hne : (0 : Nat) ≠ 1 := by decide
    simp [Array.getElem_set, hne] at hget
    have h1C : 1 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hopSzC]; decide
    exact cell_eq_of hopsS (hget.trans (hop1C h1C))
  · intro h
    have h1C : 1 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
    have h1M : 1 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
    have hM := hhomeP 1 h1C h1M (by decide) (by decide)
    have hS := hhomePS 1 h1M h (by decide)
    exact hS.trans (hM.trans (hhome1C h1C))
  · intro h
    have h5C : 5 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
    have h5M : 5 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
    have hM := hhomeP 5 h5C h5M (by decide) (by decide)
    have hS := hhomePS 5 h5M h (by decide)
    exact hS.trans (hM.trans (hhome5C h5C))
  · refine ⟨(0 + 2 * pegCount (lane.take n)) + 2 * pegCount (laneS.take n), hslS, ?_⟩
    simpa [n, Nat.zero_add] using
      four_n 0 (pegCount (lane.take n)) (pegCount (laneS.take n)) n hpegL hpegS
  · exact hpeakS
  · rcases _hstrictM with ⟨psM, hpsM⟩
    exact ⟨psM, hstrictS.trans hpsM⟩
  · rcases _hholeM with ⟨holeM, hholeM⟩
    exact ⟨holeM, hholeS.trans hholeM⟩
  · simpa [n, bench, Nat.zero_add] using
      Nat.le_trans hmvSle (side_cap_le 0 mv (pegCount (lane.take n)) (pegCount x) n bench
        hmv0 hpegL hpeg)
  · intro h
    have h0C : 0 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
    have h0M : 0 < bM.sudo_5Board_4held.size := by rw [hszDM, hszDC]; decide
    have hM := hheldPM 0 h0C h0M (by decide) (by decide)
    have hS := hheldPS 0 h0M h (by decide)
    exact hS.trans (hM.trans (hheld0C h0C))
  · intro h
    have h0C : 0 < bC.sudo_5Board_4home.size := by rw [hszHC]; decide
    have h0M : 0 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHC]; decide
    have hM := hhomeP 0 h0C h0M (by decide) (by decide)
    have hS := hhomePS 0 h0M h (by decide)
    exact hS.trans (hM.trans (hhome0C h0C))

/-- The board `curve_side` leaves for one search hole: curve side in the bottom,
    the planted peg still in base-across, up and the gap empty, marker down,
    bench off, and the op slots and counters the gap square reads. -/
structure SideAt (b : Ecbs.Board) (t : Spec.Tier) (j : Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  markerOn : b.sudo_5Board_9marker_on = false
  marker : b.sudo_5Board_6marker = -1
  benchOff : b.sudo_5Board_8bench_on = false
  botHome : ∀ h : 2 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[2] = embed (curveSide t.n t.k t.benchlen (basisPeg t.n j))
  botHeld : ∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true
  baseHome : ∀ h : 3 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[3] = embed (basisPeg t.n j)
  baseHeld : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
  upHome : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = (#[] : Array Int)
  upHeld : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = false
  axHome : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = (#[] : Array Int)
  axHeld : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = false
  gapHome : ∀ h : 5 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[5] = (#[] : Array Int)
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = false
  spareOff : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = false
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t)
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 1
  ops1 : ∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = 1
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    mv ≤ sideCap t.n t.benchlen
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧ sl ≤ 4 * t.n
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- The planted copy, cubed and closed, is `curveSide`, with the ledger `SideAt`. -/
theorem search_side (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) = .ok b' ∧
        SideAt b' t j := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hnle : t.n ≤ t.benchlen := by
    have hsp := sat.cube_span
    omega
  have hspan : 3 * (t.n - 1) < t.benchlen := cube_span_le t.n t.benchlen t.combgap sat.cube_span
  have hcubeT : allTritList (fieldCube t.n t.k t.benchlen x) :=
    fieldCube_trits t.n t.k t.benchlen x hxt hspan hsh.k_le
  have hmulT : allTritList (fieldMul t.n t.k t.benchlen x x) :=
    sq_trits t.n t.k t.benchlen x hx hspan hnle
  have hcubeL : (fieldCube t.n t.k t.benchlen x).length = t.n :=
    fieldCube_length t.n t.k t.benchlen x hnle
  have hmulL : (fieldMul t.n t.k t.benchlen x x).length = t.n :=
    fieldMul_length t.n t.k t.benchlen x x hnle
  obtain ⟨bS, mv, hdo, hhome2, hheld2, hhome6, hheld6, hhome3, hheld3, hoff, htier, hmov,
      hfit, hszH, hszD, hheld1, hheld5, hmk, hmark, hctrl, hmx, hopSz, hop0, hop1,
      hhome1, hhome5, hslE, hpkE, hstrictE, hholeE, hcap, hheld0, hhome0⟩ :=
    search_square t hOk hsh sat j hj
  have h2H : 2 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have h6H : 6 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have hn : bS.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; exact ofNat_eq_natCast _
  obtain ⟨bW, hrun, hhome, hk, hmvW⟩ := curve_side_of_cube bS 2 6 x t.n t.k t.benchlen mv
    h2H h2D h6H h6D (by decide) (by decide)
    (hheld2 h2D) (by simpa [x] using hhome2 h2H) (hheld6 h6D) (by simpa [x] using hhome6 h6H)
    hn hx hOk.n_pos hxt hmov hfit hoff hcubeL hmulL hcubeT hmulT
  have h1S : 1 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have h5S : 5 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h5D : 5 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3S : 3 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3D : 3 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  refine ⟨bW, ?_, ?_⟩
  · rw [curve_do_split, hdo, ok_bind]
    simpa [show ((2 : Nat) : Int) = Ecbs.bottom from rfl,
      show ((6 : Nat) : Int) = Ecbs.spare from rfl] using hrun
  · refine
      { tier := hk.tier.trans htier
        markerOn := hk.markerOn.trans hmk
        marker := hk.marker.trans hmark
        benchOff := hk.bench.trans hoff
        botHome := by
          intro h
          simpa [x] using hhome h
        botHeld := hk.dstHeld
        baseHome := by
          intro h
          have hpre := hk.home 3 (by decide) (by decide) h3S h
          simpa [x] using hpre.trans (hhome3 h3S)
        baseHeld := by
          intro h
          exact (hk.held 3 (by decide) h3D h).trans (hheld3 h3D)
        upHome := by
          intro h
          exact (hk.home 1 (by decide) (by decide) h1S h).trans (hhome1 h1S)
        upHeld := by
          intro h
          exact (hk.held 1 (by decide) h1D h).trans (hheld1 h1D)
        axHome := by
          intro h
          have h0S : 0 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
          exact (hk.home 0 (by decide) (by decide) h0S h).trans (hhome0 h0S)
        axHeld := by
          intro h
          have h0D : 0 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
          exact (hk.held 0 (by decide) h0D h).trans (hheld0 h0D)
        gapHome := by
          intro h
          exact (hk.home 5 (by decide) (by decide) h5S h).trans (hhome5 h5S)
        gapHeld := by
          intro h
          exact (hk.held 5 (by decide) h5D h).trans (hheld5 h5D)
        spareOff := hk.spareHeld
        szH := hk.szH.trans hszH
        szD := hk.szD.trans hszD
        ctrl := hk.ctrl.trans hctrl
        mx := hk.mx.trans hmx
        opsSz := by rw [hk.ops]; exact hopSz
        ops0 := by
          intro h
          have hS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [← hk.ops]; exact h
          have hget := hop0 hS
          simpa [hk.ops] using hget
        ops1 := by
          intro h
          have hS : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [← hk.ops]; exact h
          simpa [hk.ops] using hop1 hS
        moves := by
          have hpegM : pegCount (fieldMul t.n t.k t.benchlen x x) ≤ t.n := by
            have h := pegCount_le (fieldMul t.n t.k t.benchlen x x)
            rwa [hmulL] at h
          exact ⟨mv + 2 * pegCount (fieldMul t.n t.k t.benchlen x x) + 1, hmvW,
            close_under_cap mv _ t.n t.benchlen hpegM hcap⟩
        slides := by
          rcases hslE with ⟨sl, hsl, hle⟩
          exact ⟨sl, hk.slides.trans hsl, hle⟩
        peak := by
          rcases hpkE with ⟨pk, hpk⟩
          exact ⟨pk, hk.peak.trans hpk⟩
        strict := by
          rcases hstrictE with ⟨ps, hps⟩
          exact ⟨ps, hk.strict.trans hps⟩
        hole := by
          rcases hholeE with ⟨holeN, hhole⟩
          exact ⟨holeN, hk.hole.trans hhole⟩ }

end EcbsLink2.Link2
