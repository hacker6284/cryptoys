/-
  `curve_side` after the planted copy. The cube is `search_cube`. The spare
  multiply squares the peg, the settle seats that square, and the mirror-add
  writes `curveSide` into the bottom.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchCube
import EcbsLink2.Link2.SearchCubeAt
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

private theorem plant_ge (n bench : Nat) : plantRoom n bench ≤ perHole n bench := by
  unfold perHole
  omega

private theorem room_times (p k : Nat) (hk : 0 < k) : p ≤ p * k := by
  have hmul : p * 1 ≤ p * k := Nat.mul_le_mul_left p hk
  simpa [Nat.mul_one] using hmul

private theorem move_budget (mv n bench k : Nat) (hk : 0 < k) :
    mv + plantRoom n bench ≤ mv + perHole n bench * k :=
  Nat.add_le_add_left (Nat.le_trans (plant_ge n bench) (room_times _ _ hk)) mv

private theorem slide_four (sl n k : Nat) (hk : 0 < k) :
    sl + 4 * n ≤ sl + perSlide n * k := by
  unfold perSlide
  have h4 : 4 * n ≤ 4 * n * n + 6 * n := by omega
  exact Nat.add_le_add_left (Nat.le_trans h4 (room_times (4 * n * n + 6 * n) k hk)) sl

private theorem two_in_four (sl a n : Nat) (ha : a ≤ n) : sl + 2 * a ≤ sl + 4 * n := by
  omega

private theorem cube_base (mv0 inc peg n bench : Nat)
    (h : inc ≤ peg + peg + 2 * n + 3 * (bench - n)) :
    mv0 + inc ≤ mv0 + peg + peg + 2 * n + 3 * (bench - n) := by
  omega

private theorem assoc_room (mv n bench : Nat) :
    mv + 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 = mv + plantRoom n bench := by
  unfold plantRoom
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
  let mv0 : Nat := 0
  let mv := mv0 + cubeMoves (pegCount x + pegCount x) x n k bench
  have hmvLe := cubeMoves_le (pegCount x + pegCount x) x n k bench
  have hpegL : pegCount (lane.take n) ≤ n := pegCount_take_le lane n
  have hmvBase : mv ≤ mv0 + pegCount x + pegCount x + 2 * n + 3 * (bench - n) := by
    have hinc : cubeMoves (pegCount x + pegCount x) x n k bench ≤
        pegCount x + pegCount x + 2 * n + 3 * (bench - n) := hmvLe
    simpa [mv, mv0, Nat.zero_add] using Nat.add_le_add_left hinc mv0
  have hroom := side_le mv0 mv (pegCount (lane.take n)) (pegCount x) n bench hmvBase hpeg hpegL
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
  have hmovI : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    simpa [mv, mv0, Nat.zero_add, x] using hmovC
  have hmul := curve_mul_spare bC x lane t.w t.h t.r n k mv 0 holeN bench pk ps 0
    hmkC honC hto2 h2H h2D h3H h3D h6H h6D (by rw [hszDC]; decide)
    (hheld2C h2D) (hheld3C h3D) (hhome3C h3H) (hheld6C h6D)
    (by simpa [lane] using hbenchC) hnC hposC (by rw [hlenC]; exact hnle)
    (by simpa [lane] using hzeroC)
    (fit n hroom.2.2.2.2.2.2.2.2.1) (fit lane.length (by rw [hlenC]; exact hroom.2.2.2.2.2.2.2.2.2.1))
    hmovI hslI hpk hpsI
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
  · simpa [mv0, n, bench, Nat.zero_add] using
      Nat.le_trans hmvSle (side_cap_le mv0 mv (pegCount (lane.take n)) (pegCount x) n bench
        hmvBase hpegL hpeg)
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

/-- Homes and op slots the gap square reads off the spare-square board.
    `o0` and `o1` are the plant's op counters. The spare multiply has bumped
    slot 0 once. -/
structure SquareKeep (b : Ecbs.Board) (t : Spec.Tier) (j o0 o1 holesLeft : Nat) : Prop where
  marker : b.sudo_5Board_6marker = -1
  markerOn : b.sudo_5Board_9marker_on = false
  upHome : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = (#[] : Array Int)
  upHeld : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = false
  axHome : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = (#[] : Array Int)
  axHeld : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = false
  baseHome : ∀ h : 3 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[3] = embed (basisPeg t.n j)
  baseHeld : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = false
  spareHeld : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = true
  peak : ∃ (pk : Nat), b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ (ps : Nat), b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ (holeN : Nat), b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN
  mx : ∃ (mxN : Nat), b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mxN
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((o0 + 1 : Nat) : Int)
  ops1 : ∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((o1 + 1 : Nat) : Int)
  opsRoom : FitsLen (o0 + perOp t.n * holesLeft)
  ops1Room : FitsLen (o1 + perOp t.n * holesLeft)

/-- Spare square on the cube `search_cube_at` leaves. Moves stay under
    `mv0 + sideCap`, slides under `sl0 + 4 * n`, and control stays `c0 + tierR`. -/
theorem search_square_at (b0 : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n)
    (mv0 sl0 c0 : Nat)
    (hmv : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ (bS : Ecbs.Board) (mv : Nat) (sl : Nat),
      (do
          let b ← (do
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b0 Ecbs.base_across x
            let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
            Ecbs.cube b Ecbs.bottom Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false
          Ecbs.settle b) = .ok bS ∧
        bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
        mv ≤ mv0 + sideCap t.n t.benchlen ∧
        bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
        sl ≤ sl0 + 4 * t.n ∧
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t) ∧
        bS.sudo_5Board_8bench_on = false ∧
        FitsLen (mv + 2 * t.n + 1) ∧
        mv + 2 * t.n + 1 ≤ mv0 + sideCap t.n t.benchlen ∧
        (∀ h : 2 < bS.sudo_5Board_4home.size,
          bS.sudo_5Board_4home[2] = embed (fieldCube t.n t.k t.benchlen (basisPeg t.n j))) ∧
        (∀ h : 2 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[2] = true) ∧
        (∀ h : 6 < bS.sudo_5Board_4home.size,
          bS.sudo_5Board_4home[6] =
            embed (fieldMul t.n t.k t.benchlen (basisPeg t.n j) (basisPeg t.n j))) ∧
        (∀ h : 6 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[6] = true) ∧
        bS.sudo_5Board_4home.size = 8 ∧
        bS.sudo_5Board_4held.size = 8 ∧
        bS.sudo_5Board_1t = embTier t ∧
        ∃ o0 o1, SquareKeep bS t j o0 o1 holesLeft := by
  obtain ⟨bC, hcube, cu⟩ :=
    search_cube_at b0 t holesLeft hp hOk hsh sat j hj mv0 sl0 c0 hmv hsl0 hc0
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hpeg : pegCount x ≤ t.n := by
    have h := pegCount_le x
    rwa [hx] at h
  rcases hp.moves with ⟨mvP, hmvP, hfitM⟩
  have hmvSame : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv)
  have hbudget : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
    simpa [hmvSame] using hfitM
  rcases hp.slides with ⟨slP, hslP, hfitS⟩
  have hslSame : slP = sl0 := Int.ofNat.inj (hslP.symm.trans hsl0)
  have hslideBudget : FitsLen (sl0 + perSlide t.n * holesLeft) := by
    simpa [hslSame] using hfitS
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  let lane := laneFold n (n - k) (combStrip n bench x)
  let mv := mv0 + cubeMoves (pegCount x + pegCount x) x n k bench
  have hmvLe := cubeMoves_le (pegCount x + pegCount x) x n k bench
  have hpegL : pegCount (lane.take n) ≤ n := pegCount_take_le lane n
  have hbase : mv ≤ mv0 + pegCount x + pegCount x + 2 * n + 3 * (bench - n) := by
    simpa [mv] using cube_base mv0 (cubeMoves (pegCount x + pegCount x) x n k bench)
      (pegCount x) n bench hmvLe
  have hroom := side_le mv0 mv (pegCount (lane.take n)) (pegCount x) n bench hbase hpeg hpegL
  have fit (m : Nat)
      (hm : m ≤ mv0 + 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m := by
    have hpoly : m ≤ mv0 + plantRoom n bench := by rwa [assoc_room mv0 n bench] at hm
    exact FitsLen.of_le hbudget (Nat.le_trans hpoly (move_budget mv0 n bench holesLeft hp.holesPos))
  have sfit (m : Nat) (hm : m ≤ sl0 + 4 * n) : FitsLen m :=
    FitsLen.of_le hslideBudget (Nat.le_trans hm (slide_four sl0 n holesLeft hp.holesPos))
  have hnle : n ≤ bench := by
    have hsp := sat.cube_span
    omega
  have hlenC : lane.length = bench := by
    have h := cu.len
    unfold cubeLane at h
    simpa [lane, x, n, k, bench] using h
  have hbenchC : bC.sudo_5Board_5bench = embed lane := by
    have h := cu.bench
    unfold cubeLane at h
    simpa [lane, x, n, k, bench] using h
  have htakeC : lane.take n = fieldCube n k bench x := by
    have h := cu.take
    unfold cubeLane at h
    simpa [lane, x, n, k, bench] using h
  have hzeroC : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
    intro i hi hlt
    have h := cu.high i hi (by simpa [lane, x, n, k, bench, cubeLane] using hlt)
    unfold cubeLane at h
    simpa [lane, x, n, k, bench] using h
  have hmovC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    have h := cu.moves
    unfold cubeSpend at h
    simpa [mv, x, n, k, bench] using h
  rcases cu.peak with ⟨pk, hpk⟩
  rcases cu.strict with ⟨ps, hps⟩
  rcases cu.hole with ⟨holeN, hhole⟩
  rcases cu.ops0 with ⟨o0, ho0, hfo0, hroom0⟩
  rcases cu.ops1 with ⟨o1, ho1, hroom1⟩
  have hposC : 0 < lane.length := by rw [hlenC]; omega
  have h2H : 2 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
  have h2D : 2 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
  have h3H : 3 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
  have h3D : 3 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
  have h6H : 6 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
  have h6D : 6 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
  have hto2 : bC.sudo_5Board_8bench_to = ((2 : Nat) : Int) := by rw [cu.benchTo]; rfl
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [cu.tier]; exact ofNat_eq_natCast _
  have hpsI : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int) := by
    rw [hps]; exact ofNat_eq_natCast _
  have hmul := curve_mul_spare bC x lane t.w t.h t.r n k mv sl0 holeN bench pk ps o0
    cu.markerOn cu.benchOn hto2 h2H h2D h3H h3D h6H h6D (by rw [cu.szD]; decide)
    (cu.held2 h2D) (cu.held3 h3D) (cu.home3 h3H) (cu.held6 h6D)
    hbenchC hnC hposC (by rw [hlenC]; exact hnle) hzeroC
    (fit n (by simpa [n] using hroom.2.2.2.2.2.2.2.2.1))
    (fit lane.length (by rw [hlenC]; exact (by simpa [bench] using hroom.2.2.2.2.2.2.2.2.2.1)))
    hmovC cu.slides hpk hpsI
    (fit (2 * pegCount (lane.take n)) hroom.1)
    (fit (mv + 2 * pegCount (lane.take n)) hroom.2.1)
    (sfit (sl0 + 2 * pegCount (lane.take n)) (two_in_four sl0 _ n hpegL))
    (by rw [cu.opsSz]; decide) (ho0 (by rw [cu.opsSz]; decide)) hfo0
    hx hxt
    (by rw [cu.tier]; rfl) (by rw [cu.tier]; rfl) (by rw [cu.tier]; rfl)
    (by rw [cu.tier]; rfl) (by rw [cu.tier]; rfl) hhole hOk.n_pos sat.mul_span
    (fit (2 * (n - 1)) (by simpa [n] using hroom.2.2.2.2.2.2.2.1))
    (fit bench (by simpa [bench] using hroom.2.2.2.2.2.2.2.2.2.1))
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x) hroom.2.2.1)
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1)) hroom.2.2.2.1)
    (fit (mv + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1) + 3 * (bench - n))
      hroom.2.2.2.2.1)
    ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
    hsh.small hsh.n_small
  obtain ⟨bM, hokM, honM, htoM, htakeM, hhome2M, hbenchM, hhighM, hmovM, hslM, htM,
      hheld6M, hheld2M, hheldPM, hhomeP, hszHM, hszDM, hpkM, hmkM, hmarkM, hctrlM,
      hmxM, hopsM, hstrictM, hholeM⟩ := hmul
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
  have h6HM : 6 < bM.sudo_5Board_4home.size := by rw [hszHM, cu.szH]; decide
  have h6DM : 6 < bM.sudo_5Board_4held.size := by rw [hszDM, cu.szD]; decide
  let mvM := mulMoves (mv + 2 * pegCount (lane.take n)) x x n k bench
  have hpegS : pegCount (laneS.take n) ≤ n := pegCount_take_le laneS n
  have hmvMle : mvM ≤ mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) := by
    dsimp [mvM]
    exact mul_moves_cap (mv + 2 * pegCount (lane.take n)) x x n k bench hx
  have hset := curve_settle_spare bM laneS (fieldMul n k bench x x) n mvM
      (sl0 + 2 * pegCount (lane.take n)) pkM
      h6HM h6DM (by rw [hszDM, cu.szD]; decide) honM
      (by rw [htoM]; rfl) (hheld6M h6DM)
      (by simpa [laneS] using hbenchM) (by rw [htM, cu.tier]; exact ofNat_eq_natCast _)
      hposS (by rw [hlenS]; exact hnle) hzeroS
      (fit n (by simpa [n] using hroom.2.2.2.2.2.2.2.2.1))
      (fit laneS.length (by rw [hlenS]; exact (by simpa [bench] using hroom.2.2.2.2.2.2.2.2.2.1)))
      (by simpa [mvM] using hmovM) hslM hpkM
      (fit (2 * pegCount (laneS.take n))
        (Nat.le_trans (Nat.mul_le_mul_left 2 hpegS) hroom.2.2.2.2.2.2.2.2.2.2.2))
      (fit (mvM + 2 * pegCount (laneS.take n))
        (Nat.le_trans (settle_room mvM (pegCount (laneS.take n)) mv (pegCount (lane.take n)) n bench
          hmvMle hpegS) hroom.2.2.2.2.2.1))
      (sfit ((sl0 + 2 * pegCount (lane.take n)) + 2 * pegCount (laneS.take n))
        (four_n sl0 (pegCount (lane.take n)) (pegCount (laneS.take n)) n hpegL hpegS))
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
  have hcap := Nat.le_trans hmvSle (side_cap_le mv0 mv (pegCount (lane.take n)) (pegCount x) n bench
    hbase hpegL hpeg)
  have h2HM : 2 < bM.sudo_5Board_4home.size := by rw [hszHM, cu.szH]; decide
  have h2DM : 2 < bM.sudo_5Board_4held.size := by rw [hszDM, cu.szD]; decide
  refine ⟨bS, mvS, (sl0 + 2 * pegCount (lane.take n)) + 2 * pegCount (laneS.take n),
      ?_, ?_, ?_, ?_, ?_, ?_, hoffS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcube, ok_bind, hokM, ok_bind]
    exact hokS
  · simpa [mvS, ofNat_eq_natCast] using hmovS
  · exact Nat.le_trans (Nat.le_add_right mvS (2 * n + 1)) (by simpa [n, bench] using hcap)
  · exact hslS
  · simpa [n] using
      four_n sl0 (pegCount (lane.take n)) (pegCount (laneS.take n)) n hpegL hpegS
  · rw [hctrlS, hctrlM]
    exact cu.ctrl
  · exact fit (mvS + 2 * n + 1) (Nat.le_trans hmvSle hroom.2.2.2.2.2.2.1)
  · simpa [n, bench] using hcap
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
  · rw [hszHS, hszHM]; exact cu.szH
  · rw [hszDS, hszDM]; exact cu.szD
  · rw [htS, htM]; exact cu.tier
  · refine ⟨o0, o1, ?_⟩
    refine
      { marker := by rw [hmarkS, hmarkM]; exact cu.marker
        markerOn := by rw [hmkS]; exact hmkM
        upHome := by
          intro h
          have hC : 1 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
          have hM : 1 < bM.sudo_5Board_4home.size := by rw [hszHM]; exact hC
          exact (hhomePS 1 hM h (by decide)).trans
            ((hhomeP 1 hC hM (by decide) (by decide)).trans (cu.home1 hC))
        upHeld := by
          intro h
          have hC : 1 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
          have hM : 1 < bM.sudo_5Board_4held.size := by rw [hszDM]; exact hC
          exact (hheldPS 1 hM h (by decide)).trans
            ((hheldPM 1 hC hM (by decide) (by decide)).trans (cu.held1 hC))
        axHome := by
          intro h
          have hC : 0 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
          have hM : 0 < bM.sudo_5Board_4home.size := by rw [hszHM]; exact hC
          exact (hhomePS 0 hM h (by decide)).trans
            ((hhomeP 0 hC hM (by decide) (by decide)).trans (cu.home0 hC))
        axHeld := by
          intro h
          have hC : 0 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
          have hM : 0 < bM.sudo_5Board_4held.size := by rw [hszDM]; exact hC
          exact (hheldPS 0 hM h (by decide)).trans
            ((hheldPM 0 hC hM (by decide) (by decide)).trans (cu.held0 hC))
        baseHome := by
          intro h
          have hC : 3 < bC.sudo_5Board_4home.size := by rw [cu.szH]; decide
          have hM : 3 < bM.sudo_5Board_4home.size := by rw [hszHM]; exact hC
          exact (hhomePS 3 hM h (by decide)).trans
            ((hhomeP 3 hC hM (by decide) (by decide)).trans (cu.home3 hC))
        baseHeld := by
          intro h
          have hC : 3 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
          have hM : 3 < bM.sudo_5Board_4held.size := by rw [hszDM]; exact hC
          exact (hheldPS 3 hM h (by decide)).trans
            ((hheldPM 3 hC hM (by decide) (by decide)).trans (cu.held3 hC))
        gapHeld := by
          intro h
          have hC : 5 < bC.sudo_5Board_4held.size := by rw [cu.szD]; decide
          have hM : 5 < bM.sudo_5Board_4held.size := by rw [hszDM]; exact hC
          exact (hheldPS 5 hM h (by decide)).trans
            ((hheldPM 5 hC hM (by decide) (by decide)).trans (cu.held5 hC))
        spareHeld := hheld6S
        peak := hpeakS
        strict := by
          rcases hstrictM with ⟨psM, hpsM⟩
          exact ⟨psM, hstrictS.trans hpsM⟩
        hole := by
          rcases hholeM with ⟨holeM, hholeEq⟩
          exact ⟨holeM, hholeS.trans hholeEq⟩
        mx := by
          rcases cu.mx with ⟨mxN, hmx0⟩
          exact ⟨mxN, (hmxS.trans hmxM).trans hmx0⟩
        opsSz := by rw [hopsS, hopsM, Array.size_set]; exact cu.opsSz
        ops0 := by
          intro h
          have hM : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            have hsz := congrArg Array.size hopsS
            rw [hsz] at h
            exact h
          have hget := get_eq_of_array hopsM 0 hM
          simp [Array.getElem_set, ofNat_eq_natCast] at hget
          exact cell_eq_of hopsS hget
        ops1 := by
          intro h
          have hM : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            have hsz := congrArg Array.size hopsS
            rw [hsz] at h
            exact h
          have hget := get_eq_of_array hopsM 1 hM
          have hne : (0 : Nat) ≠ 1 := by decide
          simp [Array.getElem_set, hne] at hget
          exact cell_eq_of hopsS (hget.trans (ho1 (by rw [cu.opsSz]; decide)))
        opsRoom := hroom0
        ops1Room := hroom1 }

private theorem close_rel (mv0 mv peg n bench : Nat)
    (hpeg : peg ≤ n) (h : mv + 2 * n + 1 ≤ mv0 + sideCap n bench) :
    mv + 2 * peg + 1 ≤ mv0 + sideCap n bench := by
  omega

private theorem curve_from (b : Ecbs.Board) (n j : Nat) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        let b ← Ecbs.put b Ecbs.base_across x
        Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) =
      (((do
          let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
          Ecbs.cube b Ecbs.bottom Ecbs.bottom) >>= fun b =>
        (do
          let b ← Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false
          Ecbs.settle b)) >>= fun b =>
        (do
          let b ← Ecbs.add b Ecbs.bottom Ecbs.spare true
          let b ← Ecbs.clear b Ecbs.spare
          Ecbs.white0 b Ecbs.bottom)) := by
  unfold Ecbs.curve_side
  simp only [bind_assoc, bind_pure]

/-- Close the planted curve. Control stays `c0 + tierR`. The mirror-add spends
    at most one peg on top of the square, still inside `mv0 + sideCap`. -/
theorem search_side_at (b0 : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n)
    (mv0 sl0 c0 : Nat)
    (hmv : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ (bW : Ecbs.Board) (mv sl : Nat),
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b0 Ecbs.base_across x
          Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) = .ok bW ∧
        bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
        mv ≤ mv0 + sideCap t.n t.benchlen ∧
        bW.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
        sl ≤ sl0 + 4 * t.n ∧
        bW.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t) ∧
        (∀ h : 2 < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[2] =
            embed (curveSide t.n t.k t.benchlen (basisPeg t.n j))) := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hnle : t.n ≤ t.benchlen := by
    have hsp := sat.cube_span
    omega
  have hspan : 3 * (t.n - 1) < t.benchlen :=
    cube_span_le t.n t.benchlen t.combgap sat.cube_span
  obtain ⟨bS, mv, sl, hdo, hmov, _hle, hsl, hsle, hctrl, hoff, hfit, hclose,
      hhome2, hheld2, hhome6, hheld6, hszH, hszD, htier, _keep⟩ :=
    search_square_at b0 t holesLeft hp hOk hsh sat j hj mv0 sl0 c0 hmv hsl0 hc0
  have hcubeL : (fieldCube t.n t.k t.benchlen x).length = t.n :=
    fieldCube_length t.n t.k t.benchlen x hnle
  have hmulL : (fieldMul t.n t.k t.benchlen x x).length = t.n :=
    fieldMul_length t.n t.k t.benchlen x x hnle
  have hcubeT : allTritList (fieldCube t.n t.k t.benchlen x) :=
    fieldCube_trits t.n t.k t.benchlen x hxt hspan hsh.k_le
  have hmulT : allTritList (fieldMul t.n t.k t.benchlen x x) :=
    sq_trits t.n t.k t.benchlen x hx hspan hnle
  have h2H : 2 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have h6H : 6 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have hpegM : pegCount (fieldMul t.n t.k t.benchlen x x) ≤ t.n := by
    have h := pegCount_le (fieldMul t.n t.k t.benchlen x x)
    rwa [hmulL] at h
  obtain ⟨bW, hrun, hhome, hk, hmvW⟩ := curve_side_of_cube bS 2 6 x t.n t.k t.benchlen mv
    h2H h2D h6H h6D (by decide) (by decide)
    (hheld2 h2D) (by simpa [x] using hhome2 h2H)
    (hheld6 h6D) (by simpa [x] using hhome6 h6H)
    (by rw [htier]; exact ofNat_eq_natCast _) hx hOk.n_pos hxt hmov hfit hoff
    hcubeL hmulL hcubeT hmulT
  refine ⟨bW, mv + 2 * pegCount (fieldMul t.n t.k t.benchlen x x) + 1, sl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [curve_from b0 t.n j, hdo, ok_bind]
    simpa [show ((2 : Nat) : Int) = Ecbs.bottom from rfl,
      show ((6 : Nat) : Int) = Ecbs.spare from rfl] using hrun
  · simpa [ofNat_eq_natCast] using hmvW
  · exact close_rel mv0 mv _ t.n t.benchlen hpegM hclose
  · rw [hk.slides]; exact hsl
  · exact hsle
  · rw [hk.ctrl]; exact hctrl
  · intro h
    simpa [x] using hhome h

end EcbsLink2.Link2
