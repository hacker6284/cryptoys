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

private theorem side_le (mv pegL pegX n bench : Nat)
    (hm : mv ≤ pegX + pegX + 2 * n + 3 * (bench - n))
    (hX : pegX ≤ n) (hL : pegL ≤ n) :
    let bound := 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8
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
        (∀ h : 5 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[5] = false) := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hpeg : pegCount x ≤ t.n := by
    have h := pegCount_le x
    rwa [hx] at h
  obtain ⟨bC, hdo, honC, htoC, hbenchC, htakeC, hlenC, hzeroC, hmkC, hszHC, hszDC,
      hheld2C, _hhome2C, hheld3C, hhome3C, hheld6C, hmovC, hslC, hpkE, hpsE, hholeE,
      htierC, hopsC, hop0C, hheld1C, hheld5C⟩ := search_cube t hOk hsh sat j hj
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
  have hroom := side_le mv (pegCount (lane.take n)) (pegCount x) n bench hmvLe hpeg hpegL
  have fit (m : Nat) (hm : m ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8) : FitsLen m :=
    curveLayFit n bench m hsh.n_small hsh.small.2.2.2 hm
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
      hheld6M, hheld2M, hheldPM, hhomeP, hszHM, hszDM, hpkM⟩ := hmul
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
  obtain ⟨bS, hokS, hoffS, hhome6S, hheld6S, hhomePS, hheldPS, hmovS, htS, hszHS, hszDS⟩ := hset
  let mvS := mvM + 2 * pegCount (laneS.take n)
  have hmvInner : mvS ≤
      mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) + 2 * n := by
    dsimp [mvS]
    exact settle_room mvM (pegCount (laneS.take n)) mv (pegCount (lane.take n)) n bench hmvMle hpegS
  have hmvSle : mvS + 2 * n + 1 ≤
      mv + 2 * pegCount (lane.take n) + n + n * (n + 1) + 3 * (bench - n) + 2 * n + 2 * n + 1 :=
    close_room mvS mv (pegCount (lane.take n)) n bench hmvInner
  refine ⟨bS, mvS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hoffS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- The planted copy, cubed and closed, is `curveSide`. -/
theorem search_side (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) = .ok b' ∧
        (∀ h : 2 < b'.sudo_5Board_4home.size,
          b'.sudo_5Board_4home[2] =
            embed (curveSide t.n t.k t.benchlen (basisPeg t.n j))) := by
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
  obtain ⟨bS, mv, hdo, hhome2, hheld2, hhome6, hheld6, _, _, hoff, htier, hmov,
      hfit, hszH, hszD, _, _⟩ := search_square t hOk hsh sat j hj
  have h2H : 2 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have h6H : 6 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
  have h6D : 6 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
  have hn : bS.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [htier]; exact ofNat_eq_natCast _
  obtain ⟨bW, hrun, hhome⟩ := curve_side_of_cube bS 2 6 x t.n t.k t.benchlen mv
    h2H h2D h6H h6D (by decide) (by decide)
    (hheld2 h2D) (by simpa [x] using hhome2 h2H) (hheld6 h6D) (by simpa [x] using hhome6 h6H)
    hn hx hOk.n_pos hxt hmov hfit hoff hcubeL hmulL hcubeT hmulT
  refine ⟨bW, ?_, ?_⟩
  · rw [curve_do_split, hdo, ok_bind]
    simpa [show ((2 : Nat) : Int) = Ecbs.bottom from rfl,
      show ((6 : Nat) : Int) = Ecbs.spare from rfl] using hrun
  · intro h
    simpa [x] using hhome h

end EcbsLink2.Link2
