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

end EcbsLink2.Link2
