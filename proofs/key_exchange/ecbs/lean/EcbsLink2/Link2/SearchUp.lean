/-
  After the gap square is settled, `white0` plants a white peg in the empty up.
  That peg is `whiteHole0`, the start of the root power.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchGap
import EcbsLink2.Link2.FformOpen

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem n_le_lay (n bench : Nat) : n ≤ layBound n bench := by
  unfold layBound
  omega

private theorem gap_one (n bench : Nat) : gapCap n bench + 1 ≤ layBound n bench := by
  unfold gapCap sideCap layBound
  omega

private theorem cap_succ (mv n bench : Nat) (h : mv ≤ gapCap n bench) :
    mv + 1 ≤ gapCap n bench + 1 := by
  omega

/-- The board `white0` leaves: a white peg in the up, the curve side still in
    the bottom, its square still in the gap, and across still empty. -/
structure UpAt (b : Ecbs.Board) (t : Spec.Tier) (j : Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  markerOn : b.sudo_5Board_9marker_on = false
  marker : b.sudo_5Board_6marker = -1
  benchOff : b.sudo_5Board_8bench_on = false
  upHome : ∀ h : 1 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[1] = embed (whiteHole0 t.n)
  upHeld : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true
  botHome : ∀ h : 2 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[2] = embed (curveSide t.n t.k t.benchlen (basisPeg t.n j))
  botHeld : ∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true
  baseHome : ∀ h : 3 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[3] = embed (basisPeg t.n j)
  baseHeld : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
  gapHome : ∀ h : 5 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[5] =
      embed (fieldMul t.n t.k t.benchlen
        (curveSide t.n t.k t.benchlen (basisPeg t.n j))
        (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = true
  axHome : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = (#[] : Array Int)
  axHeld : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = false
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
    mv ≤ gapCap t.n t.benchlen + 1
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    sl ≤ 4 * t.n + 2 * t.n
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- Plant the white peg the root power starts from. -/
theorem search_up (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← (do
            let b ← (do
              let b ← Ecbs.new_board (embTier t)
              let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
              let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
              let b ← Ecbs.put b Ecbs.base_across x
              Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
            let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
            Ecbs.settle b)
          Ecbs.white0 b Ecbs.up) = .ok b' ∧
        UpAt b' t j := by
  obtain ⟨b0, hdo, g⟩ := search_gap t hOk hsh sat j hj
  rcases g.moves with ⟨mv, hmv, hmvLe⟩
  rcases g.peak with ⟨pk, hpk⟩
  have h1H : 1 < b0.sudo_5Board_4home.size := by rw [g.szH]; decide
  have h1D : 1 < b0.sudo_5Board_4held.size := by rw [g.szD]; decide
  have hfn : FitsLen t.n :=
    curveLayFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2 (n_le_lay t.n t.benchlen)
  have hfitM : FitsLen (mv + 1) :=
    curveLayFit t.n t.benchlen (mv + 1) hsh.n_small hsh.small.2.2.2
      (Nat.le_trans (cap_succ mv t.n t.benchlen hmvLe) (gap_one t.n t.benchlen))
  have hw := white0_fresh b0 1 t.n mv pk h1H h1D (g.upHeld h1D) g.benchOff
    (by rw [g.tier]; exact ofNat_eq_natCast _) hOk.n_pos hmv
    (by simpa [ofNat_eq_natCast] using hpk)
    (by rw [g.szD]; decide) hfn hfitM
  let b' := peakBoard (whitePut b0 1 h1H h1D t.n mv) pk
  refine ⟨b', ?_, ?_⟩
  · rw [hdo, ok_bind, show Ecbs.up = ((1 : Nat) : Int) from rfl]
    exact hw
  · exact {
      tier := by simp [b', peakBoard, whitePut, g.tier]
      markerOn := by simp [b', peakBoard, whitePut, g.markerOn]
      marker := by simp [b', peakBoard, whitePut, g.marker]
      benchOff := by simp [b', peakBoard, whitePut, g.benchOff]
      upHome := by
        intro h
        simp [b', peakBoard, whitePut, Array.getElem_set]
      upHeld := by
        intro h
        simp [b', peakBoard, whitePut, Array.getElem_set]
      botHome := by
        intro h
        have hne : (1 : Nat) ≠ 2 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.botHome]
      botHeld := by
        intro h
        have hne : (1 : Nat) ≠ 2 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.botHeld]
      baseHome := by
        intro h
        have hne : (1 : Nat) ≠ 3 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.baseHome]
      baseHeld := by
        intro h
        have hne : (1 : Nat) ≠ 3 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.baseHeld]
      gapHome := by
        intro h
        have hne : (1 : Nat) ≠ 5 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.gapHome]
      gapHeld := by
        intro h
        have hne : (1 : Nat) ≠ 5 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.gapHeld]
      axHome := by
        intro h
        have hne : (1 : Nat) ≠ 0 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.axHome]
      axHeld := by
        intro h
        have hne : (1 : Nat) ≠ 0 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.axHeld]
      spareOff := by
        intro h
        have hne : (1 : Nat) ≠ 6 := by decide
        simp [b', peakBoard, whitePut, Array.getElem_set, hne, g.spareOff]
      szH := by simp [b', peakBoard, whitePut, Array.size_set, g.szH]
      szD := by simp [b', peakBoard, whitePut, Array.size_set, g.szD]
      ctrl := by simp [b', peakBoard, whitePut, g.ctrl]
      mx := by simp [b', peakBoard, whitePut, g.mx]
      opsSz := by simp [b', peakBoard, whitePut, g.opsSz]
      ops0 := by
        intro h
        simpa [b', peakBoard, whitePut] using g.ops0 h
      ops1 := by
        intro h
        simpa [b', peakBoard, whitePut] using g.ops1 h
      moves := ⟨mv + 1, by simp [b', peakBoard, whitePut, ofNat_eq_natCast],
        cap_succ mv t.n t.benchlen hmvLe⟩
      slides := by
        rcases g.slides with ⟨sl, hsl, hle⟩
        exact ⟨sl, by simpa [b', peakBoard, whitePut] using hsl, hle⟩
      peak := by
        refine ⟨raisedPeak pk (countHeld (whitePut b0 1 h1H h1D t.n mv).sudo_5Board_4held 7), ?_⟩
        simp [b', peakBoard, ofNat_eq_natCast]
      strict := by
        rcases g.strict with ⟨ps, hps⟩
        exact ⟨ps, by simpa [b', peakBoard, whitePut] using hps⟩
      hole := by
        rcases g.hole with ⟨holeN, hhole⟩
        exact ⟨holeN, by simpa [b', peakBoard, whitePut] using hhole⟩ }

end EcbsLink2.Link2
