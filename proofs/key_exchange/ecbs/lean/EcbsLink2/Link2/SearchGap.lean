/-
  After `curve_side`, the card squares the bottom into the empty gap and settles.
  The gap home is `fieldMul` of the curve side with itself. The bottom stays the
  curve side, and up stays empty.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchSide
import EcbsLink2.Link2.FieldNeg

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

def layBound (n bench : Nat) : Nat :=
  2 * (n * (n + 1)) + 12 * bench + 24 * n + 8

/-- Moves after the gap square has been settled into the gap. -/
def gapCap (n bench : Nat) : Nat :=
  sideCap n bench + n + n * (n + 1) + 3 * (bench - n) + 2 * n

private theorem lay_ge (n bench : Nat) :
    2 * (n - 1) ≤ layBound n bench ∧
    n ≤ layBound n bench ∧
    bench ≤ layBound n bench ∧
    (1 : Nat) ≤ layBound n bench ∧
    (2 : Nat) ≤ layBound n bench ∧
    2 * n ≤ layBound n bench ∧
    6 * n ≤ layBound n bench := by
  unfold layBound
  omega

private theorem move_room (mv peg n bench : Nat)
    (hm : mv ≤ sideCap n bench) (hp : peg ≤ n) :
    mv + peg ≤ layBound n bench ∧
    mv + peg + n * (n + 1) ≤ layBound n bench ∧
    mv + peg + n * (n + 1) + 3 * (bench - n) ≤ layBound n bench ∧
    mv + n + n * (n + 1) + 3 * (bench - n) + 2 * n ≤ layBound n bench := by
  unfold sideCap at hm
  unfold layBound
  omega

private theorem spent_le (mv peg n bench : Nat)
    (hm : mv ≤ sideCap n bench) (hp : peg ≤ n) :
    mv + n + n * (n + 1) + 3 * (bench - n) + 2 * peg ≤ gapCap n bench := by
  unfold gapCap
  unfold sideCap
  unfold sideCap at hm
  omega

private theorem slide_room (sl peg n bench : Nat) (hs : sl ≤ 4 * n) (hp : peg ≤ n) :
    sl + 2 * peg ≤ layBound n bench ∧ sl + 2 * peg ≤ 4 * n + 2 * n := by
  have h6 := (lay_ge n bench).2.2.2.2.2.2
  omega

private theorem mul_then_settle (mvM mv peg n bench : Nat)
    (hm : mvM ≤ mv + n + n * (n + 1) + 3 * (bench - n))
    (hp : peg ≤ n) :
    mvM + 2 * peg ≤ mv + n + n * (n + 1) + 3 * (bench - n) + 2 * n := by
  omega

private theorem gap_moves_cap (moves : Nat) (xs : List Nat) (n k bench : Nat)
    (hy : xs.length = n) :
    mulMoves moves xs xs n k bench ≤
      moves + n + n * (n + 1) + 3 * (bench - n) := by
  have hsch : (school n xs xs (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hF := foldCharge_bound n (n - k) (school n xs xs (List.replicate bench 0) false)
  rw [hsch] at hF
  have hS := schoolMoves_bound xs xs n
  have hP : pegCount xs ≤ n := by
    have h := pegCount_le xs
    rwa [hy] at h
  dsimp only [mulMoves]
  omega

private theorem add_len (n : Nat) (xs ys : List Nat) : (fieldAdd n xs ys).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem side_len (n k bench : Nat) (x : List Nat) :
    (curveSide n k bench x).length = n := by
  unfold curveSide
  rw [add_len]

private theorem side_trits (n k bench : Nat) (x : List Nat) :
    allTritList (curveSide n k bench x) := by
  unfold curveSide
  exact fieldAdd_trits _ _ _

private theorem skip6 (a : Array Bool) (i : Nat) (hi : i < a.size) (h6 : 6 < a.size)
    (hne : i ≠ 6) :
    ((a.set ⟨6, h6⟩ true).set ⟨6, by rw [Array.size_set]; exact h6⟩ false)[i]'(by
        rw [Array.size_set, Array.size_set]; exact hi) =
      a[i] := by
  have hne6 : (6 : Nat) ≠ i := Ne.symm hne
  simp [Array.getElem_set, hne6]

/-- The board after the gap square is settled. Up is still empty. -/
structure GapAt (b : Ecbs.Board) (t : Spec.Tier) (j : Nat) : Prop where
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
  gapHome : ∀ h : 5 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[5] =
      embed (fieldMul t.n t.k t.benchlen
        (curveSide t.n t.k t.benchlen (basisPeg t.n j))
        (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = true
  spareOff : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = false
  buOff : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4] = false
  buHome : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4] = (#[] : Array Int)
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t)
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 2
  ops1 : ∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = 1
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    mv ≤ gapCap t.n t.benchlen
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    sl ≤ 4 * t.n + 2 * t.n
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- Square the curve side into the gap and settle that square. -/
theorem search_gap (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← (do
            let b ← Ecbs.new_board (embTier t)
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b Ecbs.base_across x
            Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
          Ecbs.settle b) = .ok b' ∧
        GapAt b' t j := by
  let x := basisPeg t.n j
  let side := curveSide t.n t.k t.benchlen x
  obtain ⟨b0, hdo, s⟩ := search_side t hOk hsh sat j hj
  rcases s.moves with ⟨mv, hmv, hmvLe⟩
  rcases s.slides with ⟨sl, hsl, hslLe⟩
  rcases s.peak with ⟨pk, hpk⟩
  rcases s.strict with ⟨ps, hps⟩
  rcases s.hole with ⟨holeN, hhole⟩
  have hmvI : b0.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    simpa [ofNat_eq_natCast] using hmv
  have hslI : b0.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := by
    simpa [ofNat_eq_natCast] using hsl
  have hpkI : b0.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    simpa [ofNat_eq_natCast] using hpk
  have hpsI : b0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int) := by
    simpa [ofNat_eq_natCast] using hps
  have hholeI : b0.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN := hhole
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  have hnle : n ≤ bench := mul_span_n n bench hOk.n_pos sat.mul_span
  have hlenS : side.length = n := side_len n k bench x
  have hxt : allTritList side := side_trits n k bench x
  have hpegS : pegCount side ≤ n := by
    have h := pegCount_le side
    rwa [hlenS] at h
  have hroom := move_room mv (pegCount side) n bench hmvLe hpegS
  have hstatic := lay_ge n bench
  have fit (m : Nat) (hm : m ≤ layBound n bench) : FitsLen m :=
    curveLayFit n bench m hsh.n_small hsh.small.2.2.2 hm
  have h2H : 2 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
  have h2D : 2 < b0.sudo_5Board_4held.size := by rw [s.szD]; decide
  have h5H : 5 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
  have h5D : 5 < b0.sudo_5Board_4held.size := by rw [s.szD]; decide
  have h6H : 6 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
  have h6D : 6 < b0.sudo_5Board_4held.size := by rw [s.szD]; decide
  have hops0 : 0 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [s.opsSz]; decide
  have hmul := mul_refines b0 5 2 2 side side t.w t.h t.r n k mv holeN bench pk ps 1
    s.markerOn s.benchOff hops0 (by simpa [ofNat_eq_natCast] using s.ops0 hops0)
    (fit 2 hstatic.2.2.2.2.1)
    (by rw [s.tier]; rfl)
    h2D h2H (s.botHeld h2D) (by simpa [side, x] using s.botHome h2H)
    h2D h2H (s.botHeld h2D) (by simpa [side, x] using s.botHome h2H)
    h6D h6H (s.spareOff h6D) (by rw [s.szD]; decide)
    (by decide) (by decide) hOk.n_pos
    (by rw [s.tier]; exact ofNat_eq_natCast _)
    hlenS hlenS (fit n hstatic.2.1) hmvI hpkI hpsI
    (fit (mv + pegCount side) hroom.1)
    sat.mul_span hxt
    (fit (2 * (n - 1)) hstatic.1)
    (fit (mv + pegCount side + n * (n + 1)) hroom.2.1)
    ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
    (by rw [s.tier]; rfl) (by rw [s.tier]; rfl) (by rw [s.tier]; rfl) (by rw [s.tier]; rfl)
    hholeI hsh.small hsh.n_small
    (fit bench hstatic.2.2.1)
    (fit (mv + pegCount side + n * (n + 1) + 3 * (bench - n)) hroom.2.2.1)
  obtain ⟨bM, hokM, honM, htoM, hbenchM, htakeM, hhighM, hmovM, hpkM, hslM, htM,
      hszHM, hheldM, _h5, hhomeM, hmkM, hopsM, hstrictM, hholeM, hmarkM, hctrlM,
      hmxM, _hi, _row, _fr⟩ := hmul
  let lane := laneFold n (n - k) (school n side side (List.replicate bench 0) false)
  have hsch : (school n side side (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hlenL : lane.length = bench := by
    dsimp [lane]
    rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hnle), hsch]
  have hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
    intro i hi hlt
    have hbi : i < bench := by rwa [hlenL] at hlt
    have hc := hhighM i hi hbi
    rw [← coeff_eq_get lane i hlt]
    simpa [lane] using hc
  have h5HM : 5 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
  have h5DM : 5 < bM.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set, s.szD]; decide
  have h6DM : 6 < bM.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set, s.szD]; decide
  have h7M : 7 ≤ bM.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set, s.szD]; decide
  have hgapE : bM.sudo_5Board_4held[5] = false := by
    have hne : (5 : Nat) ≠ 6 := by decide
    have hskip := skip6 b0.sudo_5Board_4held 5 h5D h6D hne
    simpa [← hheldM, s.gapHeld h5D] using hskip
  let mvM := mulMoves mv side side n k bench
  let pkM := mulPeak b0.sudo_5Board_4held bM.sudo_5Board_4held h6D pk
  have hpkMI : bM.sudo_5Board_4cost.sudo_5Costs_4peak = (pkM : Int) := by
    simpa [pkM, ofNat_eq_natCast] using hpkM
  have hslMI : bM.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) := by
    simpa [ofNat_eq_natCast] using hslM.trans hslI
  have hpegL : pegCount (lane.take n) ≤ n := pegCount_take_le lane n
  have hmovLe := gap_moves_cap mv side n k bench hlenS
  have hset := settle_refines bM 5 lane n mvM sl pkM h5HM h5DM h7M honM
    (by rw [htoM]) hgapE (by simpa [lane] using hbenchM)
    (by rw [htM, s.tier]; exact ofNat_eq_natCast _)
    (by rw [hlenL]; exact Nat.lt_of_lt_of_le hOk.n_pos hnle)
    (by rw [hlenL]; exact hnle) hzero
    (fit n hstatic.2.1)
    (fit lane.length (by rw [hlenL]; exact hstatic.2.2.1))
    (by simpa [mvM, ofNat_eq_natCast] using hmovM)
    hslMI hpkMI
    (fit (2 * pegCount (lane.take n)) (Nat.le_trans (Nat.mul_le_mul_left 2 hpegL) hstatic.2.2.2.2.2.1))
    (fit (mvM + 2 * pegCount (lane.take n))
      (Nat.le_trans (mul_then_settle mvM mv (pegCount (lane.take n)) n bench hmovLe hpegL)
        hroom.2.2.2))
    (fit (sl + 2 * pegCount (lane.take n)) (slide_room sl (pegCount (lane.take n)) n bench hslLe hpegL).1)
  let b' := settleBoard bM 5 h5HM h5DM lane n mvM sl pkM
  refine ⟨b', ?_, ?_⟩
  · rw [hdo, ok_bind]
    rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl,
      show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hokM, ok_bind]
    exact hset
  · exact {
      tier := by rw [settle_tier_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, htM]; exact s.tier
      markerOn := by
        rw [settle_marker_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM]
        exact hmkM
      marker := by
        rw [settle_ix_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, hmarkM]
        exact s.marker
      benchOff := settle_bench_off bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
      botHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 2 := by decide
        have h2M : 2 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
        have hM := hhomeM 2 h2H h2M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, side, x, s.botHome]
      botHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 2 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, s.botHeld]
      baseHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 3 := by decide
        have h3H : 3 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
        have h3M : 3 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
        have hM := hhomeM 3 h3H h3M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, x, s.baseHome]
      baseHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 3 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, s.baseHeld]
      upHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 1 := by decide
        have h1H : 1 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
        have h1M : 1 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
        have hM := hhomeM 1 h1H h1M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, s.upHome]
      upHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 1 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, s.upHeld]
      axHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 0 := by decide
        have h0H : 0 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
        have h0M : 0 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
        have hM := hhomeM 0 h0H h0M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, s.axHome]
      axHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 0 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, s.axHeld]
      gapHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        simp [b', hS, Array.getElem_set, htakeM, lane, side, x]
      gapHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        simp [b', hS, Array.getElem_set]
      spareOff := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 6 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM]
      buOff := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 4 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, s.buOff]
      buHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hne : (5 : Nat) ≠ 4 := by decide
        have h4H : 4 < b0.sudo_5Board_4home.size := by rw [s.szH]; decide
        have h4M : 4 < bM.sudo_5Board_4home.size := by rw [hszHM, s.szH]; decide
        have hM := hhomeM 4 h4H h4M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, s.buHome]
      szH := by
        rw [settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, Array.size_set, hszHM]
        exact s.szH
      szD := by
        rw [settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, Array.size_set, hheldM,
          Array.size_set, Array.size_set]
        exact s.szD
      ctrl := by
        rw [settle_ctrl_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, hctrlM]
        exact s.ctrl
      mx := by
        rw [settle_mx_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, hmxM]
        exact s.mx
      opsSz := by
        rw [settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM, hopsM, Array.size_set]
        exact s.opsSz
      ops0 := by
        intro h
        have hS := settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hsz : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [← hS]; exact h
        have hget := get_eq_of_array hopsM 0 hsz
        simp [Array.getElem_set, ofNat_eq_natCast] at hget
        exact cell_eq_of hS hget
      ops1 := by
        intro h
        have hS := settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        have hsz : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [← hS]; exact h
        have hget := get_eq_of_array hopsM 1 hsz
        have hne : (0 : Nat) ≠ 1 := by decide
        simp [Array.getElem_set, hne] at hget
        have h1 : 1 < b0.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [s.opsSz]; decide
        exact cell_eq_of hS (hget.trans (s.ops1 h1))
      moves := by
        refine ⟨mvM + 2 * pegCount (lane.take n), ?_, ?_⟩
        · dsimp [b']
          simpa [ofNat_eq_natCast] using
            settle_moves_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
        · exact Nat.le_trans
            (Nat.add_le_add_right hmovLe (2 * pegCount (lane.take n)))
            (spent_le mv (pegCount (lane.take n)) n bench hmvLe hpegL)
      slides := by
        refine ⟨sl + 2 * pegCount (lane.take n), ?_, (slide_room sl _ n bench hslLe hpegL).2⟩
        dsimp [b']
        simpa [ofNat_eq_natCast] using
          settle_slides_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM
      peak := by
        dsimp [b']
        exact ⟨_, settle_peak_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM hpkMI⟩
      strict := by
        dsimp [b']
        exact ⟨_, (settle_strict_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM).trans hstrictM⟩
      hole := by
        dsimp [b']
        exact ⟨_, (settle_hole_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM sl pkM).trans hholeM⟩ }

private theorem lay_le_per (n bench : Nat) : layBound n bench ≤ perHole n bench := by
  unfold layBound perHole plantRoom
  omega

private theorem times_ge (p k : Nat) (hk : 0 < k) : p ≤ p * k := by
  simpa [Nat.mul_one] using Nat.mul_le_mul_left p hk

private theorem rel_fit (mv n bench k m : Nat) (hk : 0 < k)
    (hm : m ≤ mv + layBound n bench) :
    m ≤ mv + perHole n bench * k :=
  Nat.le_trans hm (Nat.add_le_add_left (Nat.le_trans (lay_le_per n bench) (times_ge _ _ hk)) mv)

private theorem gap_move (mv0 mv peg n bench : Nat)
    (hm : mv ≤ mv0 + sideCap n bench) (hp : peg ≤ n) :
    mv + peg ≤ mv0 + layBound n bench ∧
    mv + peg + n * (n + 1) ≤ mv0 + layBound n bench ∧
    mv + peg + n * (n + 1) + 3 * (bench - n) ≤ mv0 + layBound n bench ∧
    mv + n + n * (n + 1) + 3 * (bench - n) + 2 * peg ≤ mv0 + gapCap n bench := by
  unfold gapCap layBound
  unfold sideCap
  unfold sideCap at hm
  omega

private theorem close_rel (mv0 mv peg n bench : Nat)
    (hpeg : peg ≤ n) (h : mv + 2 * n + 1 ≤ mv0 + sideCap n bench) :
    mv + 2 * peg + 1 ≤ mv0 + sideCap n bench := by
  omega

private theorem in_lay (mv m bound : Nat) (hm : m ≤ bound) : m ≤ mv + bound :=
  Nat.le_trans hm (Nat.le_add_left _ _)

private theorem gap_lay (n bench : Nat) : gapCap n bench ≤ layBound n bench := by
  unfold gapCap sideCap layBound
  omega

private theorem under_lay (mv m n bench : Nat) (hm : m ≤ mv + gapCap n bench) :
    m ≤ mv + layBound n bench := by
  exact Nat.le_trans hm (Nat.add_le_add_left (gap_lay n bench) mv)

private theorem two_peg_lay (mv peg n bench : Nat) (hp : peg ≤ n) :
    2 * peg ≤ mv + layBound n bench := by
  have h2 : 2 * n ≤ layBound n bench := (lay_ge n bench).2.2.2.2.2.1
  have hpeg : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  exact Nat.le_trans (Nat.le_trans hpeg h2) (Nat.le_add_left _ mv)

private theorem spent_gap (mv0 mv mvM peg n bench : Nat)
    (hm : mv ≤ mv0 + sideCap n bench) (hp : peg ≤ n)
    (hM : mvM ≤ mv + n + n * (n + 1) + 3 * (bench - n)) :
    mvM + 2 * peg ≤ mv0 + gapCap n bench :=
  Nat.le_trans (Nat.add_le_add_right hM (2 * peg))
    (gap_move mv0 mv peg n bench hm hp).2.2.2

private theorem slide_out (sl0 sl peg n : Nat) (hs : sl ≤ sl0 + 4 * n) (hp : peg ≤ n) :
    sl + 2 * peg ≤ sl0 + 6 * n := by
  omega

private theorem op_two (o n k : Nat) (hk : 0 < k) : o + 2 ≤ o + perOp n * k := by
  have h2 : 2 ≤ perOp n := by
    unfold perOp
    exact Nat.le_add_left 2 n
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  have hmul : 2 * k ≤ perOp n * k := Nat.mul_le_mul_right k h2
  have htwo : 2 ≤ 2 * k := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left 2 hk1
  exact Nat.add_le_add_left (Nat.le_trans htwo hmul) o

private theorem sq_trits (n k bench : Nat) (x : List Nat)
    (hx : x.length = n) (hspan : 3 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench x x) := by
  have htk : x.take n = x := by
    have h := List.take_length x
    rwa [hx] at h
  simpa [htk] using fieldMul_trits n k bench x x hspan hn

private theorem slide_gap (sl0 sl peg n k : Nat) (hs : sl ≤ sl0 + 4 * n) (hp : peg ≤ n)
    (hk : 0 < k) : sl + 2 * peg ≤ sl0 + perSlide n * k := by
  unfold perSlide
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left 2 hp
  have htail : sl0 + 4 * n + 2 * n ≤ sl0 + (4 * n * n + 6 * n) * k := by
    have h6 : 6 * n ≤ 4 * n * n + 6 * n := Nat.le_add_left _ _
    have hmul : 4 * n * n + 6 * n ≤ (4 * n * n + 6 * n) * k := times_ge _ _ hk
    omega
  omega

private theorem curve_from_gap (b : Ecbs.Board) (n j : Nat) :
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


/-- The board after the gap square, with counters relative to the plant. -/
structure GapKeep (b : Ecbs.Board) (t : Spec.Tier)
    (j mv0 sl0 c0 o0 o1 holesLeft : Nat) : Prop where
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
  gapHome : ∀ h : 5 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[5] =
      embed (fieldMul t.n t.k t.benchlen
        (curveSide t.n t.k t.benchlen (basisPeg t.n j))
        (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = true
  spareOff : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = false
  buOff : ∀ h : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4] = false
  buHome : ∀ h : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4] = (#[] : Array Int)
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)
  mx : ∃ mxN, b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mxN
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((o0 + 2 : Nat) : Int)
  ops1 : ∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((o1 + 1 : Nat) : Int)
  opsRoom : FitsLen (o0 + perOp t.n * holesLeft)
  ops1Room : FitsLen (o1 + perOp t.n * holesLeft)
  moves : ∃ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
    mv ≤ mv0 + gapCap t.n t.benchlen
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    sl ≤ sl0 + 6 * t.n
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- Square the curve side into the gap. Moves stay under `mv0 + gapCap`,
    slides under `sl0 + 6 * n`, and control stays `c0 + tierR`. -/
theorem search_gap_at (b0 : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n)
    (mv0 sl0 c0 : Nat)
    (hmv : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ (b' : Ecbs.Board) (o0 o1 : Nat),
      (do
          let b ← (do
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b0 Ecbs.base_across x
            Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
          Ecbs.settle b) = .ok b' ∧
        GapKeep b' t j mv0 sl0 c0 o0 o1 holesLeft := by
  let x := basisPeg t.n j
  let side := curveSide t.n t.k t.benchlen x
  obtain ⟨bS, mvS, slS, hsq, hmovS, _hleS, hslS, hsleS, hctrlS, hoffS, hfitS, hclose,
      hhome2, hheld2, hhome6, hheld6, hszH, hszD, htier, oKeep⟩ :=
    search_square_at b0 t holesLeft hp hOk hsh sat j hj mv0 sl0 c0 hmv hsl0 hc0
  rcases oKeep with ⟨oA, oB, sk⟩
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hnle : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hOk.n_pos sat.mul_span
  have hlenS : side.length = t.n := side_len t.n t.k t.benchlen x
  have hsideT : allTritList side := side_trits t.n t.k t.benchlen x
  have hpegS : pegCount side ≤ t.n := by
    have h := pegCount_le side
    rwa [hlenS] at h
  have hspan : 3 * (t.n - 1) < t.benchlen :=
    cube_span_le t.n t.benchlen t.combgap sat.cube_span
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
  obtain ⟨bW, hrun, hbot, hk, hmvW⟩ := curve_side_of_cube bS 2 6 x t.n t.k t.benchlen mvS
    h2H h2D h6H h6D (by decide) (by decide)
    (hheld2 h2D) (by simpa [x] using hhome2 h2H)
    (hheld6 h6D) (by simpa [x] using hhome6 h6H)
    (by rw [htier]; exact ofNat_eq_natCast _) hx hOk.n_pos hxt hmovS hfitS hoffS
    hcubeL hmulL hcubeT hmulT
  let mvW := mvS + 2 * pegCount (fieldMul t.n t.k t.benchlen x x) + 1
  have hmvWI : bW.sudo_5Board_4cost.sudo_5Costs_5moves = (mvW : Int) := by
    simpa [mvW, ofNat_eq_natCast] using hmvW
  have hleW : mvW ≤ mv0 + sideCap t.n t.benchlen :=
    close_rel mv0 mvS _ t.n t.benchlen
      (by
        have h := pegCount_le (fieldMul t.n t.k t.benchlen x x)
        rwa [hmulL] at h) hclose
  rcases sk.peak with ⟨pk, hpkS⟩
  have hpkW : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    rw [hk.peak]; exact hpkS
  rcases sk.strict with ⟨ps, hpsS⟩
  have hpsW : bW.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int) := by
    rw [hk.strict, hpsS]; exact ofNat_eq_natCast _
  rcases sk.hole with ⟨holeN, hholeS⟩
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN := by
    rw [hk.hole]; exact hholeS
  have hmkW : bW.sudo_5Board_9marker_on = false := by
    rw [hk.markerOn]; exact sk.markerOn
  have hbenchW : bW.sudo_5Board_8bench_on = false := by
    rw [hk.bench]; exact hoffS
  have hszHW : bW.sudo_5Board_4home.size = 8 := by rw [hk.szH]; exact hszH
  have hszDW : bW.sudo_5Board_4held.size = 8 := by rw [hk.szD]; exact hszD
  have h2HW : 2 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
  have h2DW : 2 < bW.sudo_5Board_4held.size := by rw [hszDW]; decide
  have h5DW : 5 < bW.sudo_5Board_4held.size := by rw [hszDW]; decide
  have h6HW : 6 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
  have h6DW : 6 < bW.sudo_5Board_4held.size := by rw [hszDW]; decide
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by rw [hszDW]; decide
  have hheldW : bW.sudo_5Board_4held[2] = true := hk.dstHeld h2DW
  have harrW : bW.sudo_5Board_4home[2] = embed side := by
    simpa [side, x] using hbot h2HW
  have upHeldW : ∀ h : 1 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[1] = false := by
    intro h
    have h1S : 1 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hk.held 1 (by decide) h1S h).trans (sk.upHeld h1S)
  have upHomeW : ∀ h : 1 < bW.sudo_5Board_4home.size,
      bW.sudo_5Board_4home[1] = (#[] : Array Int) := by
    intro h
    have h1S : 1 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (hk.home 1 (by decide) (by decide) h1S h).trans (sk.upHome h1S)
  have axHeldW : ∀ h : 0 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[0] = false := by
    intro h
    have h0S : 0 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hk.held 0 (by decide) h0S h).trans (sk.axHeld h0S)
  have axHomeW : ∀ h : 0 < bW.sudo_5Board_4home.size,
      bW.sudo_5Board_4home[0] = (#[] : Array Int) := by
    intro h
    have h0S : 0 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (hk.home 0 (by decide) (by decide) h0S h).trans (sk.axHome h0S)
  have buOffW : ∀ h : 4 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[4] = false := by
    intro h
    have h4S : 4 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hk.held 4 (by decide) h4S h).trans (sk.buOff h4S)
  have buHomeW : ∀ h : 4 < bW.sudo_5Board_4home.size,
      bW.sudo_5Board_4home[4] = (#[] : Array Int) := by
    intro h
    have h4S : 4 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (hk.home 4 (by decide) (by decide) h4S h).trans (sk.buHome h4S)
  have baseHeldW : ∀ h : 3 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[3] = true := by
    intro h
    have h3S : 3 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hk.held 3 (by decide) h3S h).trans (sk.baseHeld h3S)
  have baseHomeW : ∀ h : 3 < bW.sudo_5Board_4home.size,
      bW.sudo_5Board_4home[3] = embed (basisPeg t.n j) := by
    intro h
    have h3S : 3 < bS.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (hk.home 3 (by decide) (by decide) h3S h).trans (sk.baseHome h3S)
  have gapHeldW : ∀ h : 5 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[5] = false := by
    intro h
    have h5S : 5 < bS.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hk.held 5 (by decide) h5S h).trans (sk.gapHeld h5S)
  rcases hp.moves with ⟨mvP, hmvP, hfitM⟩
  have hmvSame : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv)
  have hbudget : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
    simpa [hmvSame] using hfitM
  rcases hp.slides with ⟨slP, hslP, hfitSl⟩
  have hslSame : slP = sl0 := Int.ofNat.inj (hslP.symm.trans hsl0)
  have hslideBudget : FitsLen (sl0 + perSlide t.n * holesLeft) := by
    simpa [hslSame] using hfitSl
  have hroom := gap_move mv0 mvW (pegCount side) t.n t.benchlen hleW hpegS
  have fit (m : Nat) (hm : m ≤ mv0 + layBound t.n t.benchlen) : FitsLen m :=
    FitsLen.of_le hbudget (rel_fit mv0 t.n t.benchlen holesLeft m hp.holesPos hm)
  have hfops : FitsLen (oA + 2) :=
    FitsLen.of_le sk.opsRoom (op_two oA t.n holesLeft hp.holesPos)
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  have hmul := mul_refines bW 5 2 2 side side t.w t.h t.r n k mvW holeN bench pk ps (oA + 1)
    hmkW hbenchW (by rw [hk.ops, sk.opsSz]; decide)
    (by
      have hsz : 0 < bW.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hk.ops, sk.opsSz]; decide
      simpa [ofNat_eq_natCast] using
        (cell_eq_of hk.ops (sk.ops0 (by rw [sk.opsSz]; decide))))
    hfops
    (by rw [hk.tier, htier]; rfl)
    h2DW h2HW hheldW harrW h2DW h2HW hheldW harrW
    h6DW h6HW (hk.spareHeld h6DW) h7W (by decide) (by decide) hOk.n_pos
    (by rw [hk.tier, htier]; exact ofNat_eq_natCast _)
    hlenS hlenS (fit n (in_lay mv0 n _ ((lay_ge n bench).2.1)))
    hmvWI hpkW hpsW
    (fit (mvW + pegCount side) hroom.1)
    sat.mul_span hsideT
    (fit (2 * (n - 1)) (in_lay mv0 _ _ (lay_ge n bench).1))
    (fit (mvW + pegCount side + n * (n + 1)) hroom.2.1)
    ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
    (by rw [hk.tier, htier]; rfl) (by rw [hk.tier, htier]; rfl)
    (by rw [hk.tier, htier]; rfl) (by rw [hk.tier, htier]; rfl)
    hholeW hsh.small hsh.n_small
    (fit bench (in_lay mv0 bench _ ((lay_ge n bench).2.2.1)))
    (fit (mvW + pegCount side + n * (n + 1) + 3 * (bench - n)) hroom.2.2.1)
  obtain ⟨bM, hokM, honM, htoM, hbenchM, htakeM, hhighM, hmovM, hpkM, hslM, htM,
      hszHM, hheldM, _h5, hhomeM, hmkM, hopsM, hstrictM, hholeM, hmarkM, hctrlM,
      hmxM, _hi, _row, _fr⟩ := hmul
  let lane := laneFold n (n - k) (school n side side (List.replicate bench 0) false)
  have hsch : (school n side side (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hlenL : lane.length = bench := by
    dsimp [lane]
    rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hnle), hsch]
  have hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
    intro i hi hlt
    have hbi : i < bench := by rwa [hlenL] at hlt
    have hc := hhighM i hi hbi
    rw [← coeff_eq_get lane i hlt]
    simpa [lane] using hc
  have h5HM : 5 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
  have h5DM : 5 < bM.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set, hszDW]; decide
  have h7M : 7 ≤ bM.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set, hszDW]; decide
  have hgapE : bM.sudo_5Board_4held[5] = false := by
    have hne : (5 : Nat) ≠ 6 := by decide
    have hskip := skip6 bW.sudo_5Board_4held 5 h5DW h6DW hne
    simpa [← hheldM, gapHeldW h5DW] using hskip
  let mvM := mulMoves mvW side side n k bench
  let pkM := mulPeak bW.sudo_5Board_4held bM.sudo_5Board_4held h6DW pk
  have hpkMI : bM.sudo_5Board_4cost.sudo_5Costs_4peak = (pkM : Int) := by
    simpa [pkM, ofNat_eq_natCast] using hpkM
  have hslMI : bM.sudo_5Board_4cost.sudo_5Costs_6slides = (slS : Int) := by
    simpa [ofNat_eq_natCast] using hslM.trans (hk.slides.trans hslS)
  have hpegL : pegCount (lane.take n) ≤ n := pegCount_take_le lane n
  have hmovLe : mvM ≤ mvW + n + n * (n + 1) + 3 * (bench - n) := by
    dsimp [mvM]
    exact gap_moves_cap mvW side n k bench hlenS
  have hset := settle_refines bM 5 lane n mvM slS pkM h5HM h5DM h7M honM
    htoM hgapE (by simpa [lane] using hbenchM)
    (by rw [htM, hk.tier, htier]; exact ofNat_eq_natCast _)
    (by rw [hlenL]; exact Nat.lt_of_lt_of_le hOk.n_pos hnle)
    (by rw [hlenL]; exact hnle) hzero
    (fit n (in_lay mv0 n _ ((lay_ge n bench).2.1)))
    (fit lane.length (in_lay mv0 _ _ (by rw [hlenL]; exact (lay_ge n bench).2.2.1)))
    (by simpa [mvM, ofNat_eq_natCast] using hmovM)
    hslMI hpkMI
    (fit (2 * pegCount (lane.take n)) (two_peg_lay mv0 _ n bench hpegL))
    (fit (mvM + 2 * pegCount (lane.take n))
      (under_lay mv0 _ n bench (spent_gap mv0 mvW mvM _ n bench hleW hpegL hmovLe)))
    (FitsLen.of_le hslideBudget (slide_gap sl0 slS _ t.n holesLeft hsleS hpegL hp.holesPos))
  let b' := settleBoard bM 5 h5HM h5DM lane n mvM slS pkM
  have hsideDo :
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b0 Ecbs.base_across x
          Ecbs.curve_side b Ecbs.base_across Ecbs.bottom) = .ok bW := by
    rw [curve_from_gap b0 t.n j, hsq, ok_bind]
    simpa [show ((2 : Nat) : Int) = Ecbs.bottom from rfl,
      show ((6 : Nat) : Int) = Ecbs.spare from rfl] using hrun
  refine ⟨b', oA, oB, ?_, ?_⟩
  · rw [hsideDo, ok_bind,
      show Ecbs.gap = ((5 : Nat) : Int) from rfl,
      show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hokM, ok_bind]
    exact hset
  · exact {
      tier := by rw [settle_tier_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, htM, hk.tier]; exact htier
      markerOn := by
        rw [settle_marker_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM]
        exact hmkM
      marker := by
        rw [settle_ix_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, hmarkM, hk.marker]
        exact sk.marker
      benchOff := settle_bench_off bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
      botHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 2 := by decide
        have h2M : 2 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
        have hM := hhomeM 2 h2HW h2M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, harrW, side, x]
      botHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 2 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, hheldW]
      baseHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 3 := by decide
        have h3W : 3 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
        have h3M : 3 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
        have hM := hhomeM 3 h3W h3M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, baseHomeW, x]
      baseHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 3 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, baseHeldW]
      upHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 1 := by decide
        have h1W : 1 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
        have h1M : 1 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
        have hM := hhomeM 1 h1W h1M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, upHomeW]
      upHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 1 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, upHeldW]
      axHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 0 := by decide
        have h0W : 0 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
        have h0M : 0 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
        have hM := hhomeM 0 h0W h0M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, axHomeW]
      axHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 0 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, axHeldW]
      gapHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        simp [b', hS, Array.getElem_set, htakeM, lane, side, x]
      gapHeld := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        simp [b', hS, Array.getElem_set]
      spareOff := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 6 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM]
      buOff := by
        intro h
        have hS := settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 4 := by decide
        simp [b', hS, Array.getElem_set, hne, hheldM, buOffW]
      buHome := by
        intro h
        have hS := settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hne : (5 : Nat) ≠ 4 := by decide
        have h4W : 4 < bW.sudo_5Board_4home.size := by rw [hszHW]; decide
        have h4M : 4 < bM.sudo_5Board_4home.size := by rw [hszHM, hszHW]; decide
        have hM := hhomeM 4 h4W h4M (by decide)
        simp [b', hS, Array.getElem_set, hne, hM, buHomeW]
      szH := by
        rw [settle_home_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, Array.size_set, hszHM]
        exact hszHW
      szD := by
        rw [settle_held_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, Array.size_set, hheldM,
          Array.size_set, Array.size_set]
        exact hszDW
      ctrl := by
        rw [settle_ctrl_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, hctrlM, hk.ctrl]
        exact hctrlS
      mx := by
        rcases sk.mx with ⟨mxN, hmxS⟩
        refine ⟨mxN, ?_⟩
        rw [settle_mx_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, hmxM, hk.mx]
        exact hmxS
      opsSz := by
        rw [settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM, hopsM, Array.size_set, hk.ops]
        exact sk.opsSz
      ops0 := by
        intro h
        have hS := settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hsz : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [← hS]; exact h
        have hget := get_eq_of_array hopsM 0 hsz
        simp [Array.getElem_set, ofNat_eq_natCast] at hget
        exact cell_eq_of hS hget
      ops1 := by
        intro h
        have hS := settle_ops bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        have hsz : 1 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [← hS]; exact h
        have hget := get_eq_of_array hopsM 1 hsz
        have hne : (0 : Nat) ≠ 1 := by decide
        simp [Array.getElem_set, hne] at hget
        have h1S : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [sk.opsSz]; decide
        exact cell_eq_of hS (hget.trans (cell_eq_of hk.ops (sk.ops1 h1S)))
      opsRoom := sk.opsRoom
      ops1Room := sk.ops1Room
      moves := by
        refine ⟨mvM + 2 * pegCount (lane.take n), ?_, ?_⟩
        · dsimp [b']
          simpa [ofNat_eq_natCast] using
            settle_moves_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
        · exact spent_gap mv0 mvW mvM (pegCount (lane.take n)) n bench hleW hpegL hmovLe
      slides := by
        refine ⟨slS + 2 * pegCount (lane.take n), ?_,
          slide_out sl0 slS _ n hsleS hpegL⟩
        dsimp [b']
        simpa [ofNat_eq_natCast] using
          settle_slides_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM
      peak := by
        dsimp [b']
        exact ⟨_, settle_peak_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM hpkMI⟩
      strict := by
        dsimp [b']
        exact ⟨_, (settle_strict_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM).trans hstrictM⟩
      hole := by
        dsimp [b']
        exact ⟨_, (settle_hole_eq bM 5 ⟨h5HM, h5DM⟩ lane n mvM slS pkM).trans hholeM⟩ }

end EcbsLink2.Link2
