/-
  The root strip, planted in the empty across home, then the marker flag.
  The strip is `rootStrip`: `rootDigits` with the unused last hole still empty.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchUp
import EcbsLink2.Link2.RootStrip
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.WalkCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The strip loop the card runs before the power. -/
def emittedStrip (n : Nat) : Except SudoRt.Trap (Array Int) :=
  SudoRt.runLoopOn (Int.ofNat 0, Array.mkArray n (0 : Int))
    (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
    (rootStripStep (Int.ofNat (n - 2)))
    (fun σ =>
      SudoRt.subI (Int.ofNat n) (2 : Int) >>= fun ix =>
        SudoRt.putL σ.2 ix (1 : Int))
    (fun r => pure r)

private theorem strip_run (n : Nat) (hn : 2 ≤ n) (hfit : FitsLen n) :
    emittedStrip n = .ok (embed (rootStrip n)) := by
  rw [emittedStrip, root_strip_loop n hn hfit, rootStrip_eq n hn]

private theorem strip_len (n : Nat) (hn : 0 < n) : (rootStrip n).length = n := by
  by_cases h2 : 2 ≤ n
  · rw [rootStrip_eq n h2]
    simp [rootDigits, List.length_append, List.length_map, List.length_range]
    omega
  · have hn1 : n = 1 := by omega
    simpa [hn1] using (by decide : (rootStrip 1).length = 1)

private theorem strip_at (n : Nat) (hn : 2 ≤ n) (hfit : FitsLen n) :
    emittedStrip n = .ok (embed (rootStrip n)) :=
  strip_run n hn hfit

private theorem put_room (mv n bench : Nat) (h : mv ≤ gapCap n bench + 1) :
    mv + n ≤ layBound n bench := by
  unfold gapCap sideCap layBound at *
  omega

private theorem n_lay (n bench : Nat) : n ≤ layBound n bench := by
  unfold layBound
  omega

private theorem spent_strip (mv peg n bench : Nat)
    (hm : mv ≤ gapCap n bench + 1) (hp : peg ≤ n) :
    mv + peg ≤ gapCap n bench + 1 + n := by
  omega

/-- Across holds the root strip and the marker flag is up. The marker value
    is still `-1`: the first power digit seats it. -/
structure StripAt (b : Ecbs.Board) (t : Spec.Tier) (j : Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  markerOn : b.sudo_5Board_9marker_on = true
  marker : b.sudo_5Board_6marker = -1
  benchOff : b.sudo_5Board_8bench_on = false
  upHome : ∀ h : 1 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[1] = embed (whiteHole0 t.n)
  upHeld : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true
  botHome : ∀ h : 2 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[2] = embed (curveSide t.n t.k t.benchlen (basisPeg t.n j))
  botHeld : ∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true
  gapHome : ∀ h : 5 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[5] =
      embed (fieldMul t.n t.k t.benchlen
        (curveSide t.n t.k t.benchlen (basisPeg t.n j))
        (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
  gapHeld : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = true
  axHome : ∀ h : 0 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[0] = embed (rootStrip t.n)
  axHeld : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = true
  baseHome : ∀ h : 3 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[3] = embed (basisPeg t.n j)
  baseHeld : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
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
    mv ≤ gapCap t.n t.benchlen + 1 + t.n
  slides : ∃ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    sl ≤ 4 * t.n + 2 * t.n
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- Paint the root strip into across and raise the marker flag. -/
theorem search_strip (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← (do
            let b ← (do
              let b ← (do
                let b ← Ecbs.new_board (embTier t)
                let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
                let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
                let b ← Ecbs.put b Ecbs.base_across x
                Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
              let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
              Ecbs.settle b)
            Ecbs.white0 b Ecbs.up)
          let strip ← emittedStrip t.n
          let b ← Ecbs.put b Ecbs.across strip
          pure ({ b with sudo_5Board_9marker_on := true })) = .ok b' ∧
        StripAt b' t j := by
  have hn2 : 2 ≤ t.n := by omega
  obtain ⟨b0, hdo, u⟩ := search_up t hOk hsh sat j hj
  rcases u.moves with ⟨mv, hmv, hmvLe⟩
  rcases u.peak with ⟨pk, hpk⟩
  have hlenS : (rootStrip t.n).length = t.n := strip_len t.n hOk.n_pos
  have hpeg : pegCount (rootStrip t.n) ≤ t.n := by
    have h := pegCount_le (rootStrip t.n)
    rwa [hlenS] at h
  have hfn : FitsLen t.n :=
    curveLayFit t.n t.benchlen t.n hsh.n_small hsh.small.2.2.2 (n_lay t.n t.benchlen)
  have hfitP : FitsLen (mv + pegCount (rootStrip t.n)) :=
    curveLayFit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2
      (Nat.le_trans (spent_strip mv _ t.n t.benchlen hmvLe hpeg)
        (put_room (gapCap t.n t.benchlen + 1) t.n t.benchlen (Nat.le_refl _)))
  have h0H : 0 < b0.sudo_5Board_4home.size := by rw [u.szH]; decide
  have h0D : 0 < b0.sudo_5Board_4held.size := by rw [u.szD]; decide
  have hpkI : b0.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) := by
    simpa [ofNat_eq_natCast] using hpk
  have hstrip := strip_at t.n hn2 hfn
  have hput := put_refines b0 0 (rootStrip t.n) mv pk h0H h0D
    (by rw [u.szD]; decide) (u.axHeld h0D)
    (by rw [u.tier, hlenS]; exact ofNat_eq_natCast _)
    (by rw [hlenS]; exact hfn) hmv hpkI hfitP
  let bP := placeBoard b0 0 h0H h0D (rootStrip t.n) mv pk
  let b' := { bP with sudo_5Board_9marker_on := true }
  refine ⟨b', ?_, ?_⟩
  · rw [hdo, ok_bind, hstrip, ok_bind, show Ecbs.across = ((0 : Nat) : Int) from rfl,
      hput, ok_bind, pure_eq_ok]
  · exact {
      tier := by simpa [b', bP, u.tier] using place_tier_eq b0 0 h0H h0D (rootStrip t.n) mv pk
      markerOn := by simp [b']
      marker := by simpa [b', bP, u.marker] using place_marker_eq b0 0 h0H h0D (rootStrip t.n) mv pk
      benchOff := by
        simp [b', bP, placeBoard, u.benchOff]
        split <;> rfl
      upHome := by
        intro h
        have hH := place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 1 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.upHome]
      upHeld := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 1 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.upHeld]
      botHome := by
        intro h
        have hH := place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 2 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.botHome]
      botHeld := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 2 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.botHeld]
      gapHome := by
        intro h
        have hH := place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 5 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.gapHome]
      gapHeld := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 5 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.gapHeld]
      axHome := by
        intro h
        have hH := place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        simp [b', bP, hH, Array.getElem_set]
      axHeld := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        simp [b', bP, hH, Array.getElem_set]
      baseHome := by
        intro h
        have hH := place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 3 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.baseHome]
      baseHeld := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 3 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.baseHeld]
      spareOff := by
        intro h
        have hH := place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        have hne : (0 : Nat) ≠ 6 := by decide
        simp [b', bP, hH, Array.getElem_set, hne, u.spareOff]
      szH := by
        simp [b', bP, place_home_eq b0 0 h0H h0D (rootStrip t.n) mv pk, Array.size_set, u.szH]
      szD := by
        simp [b', bP, place_held_eq b0 0 h0H h0D (rootStrip t.n) mv pk, Array.size_set, u.szD]
      ctrl := by simpa [b', bP, u.ctrl] using place_ctrl_eq b0 0 h0H h0D (rootStrip t.n) mv pk
      mx := by simpa [b', bP, u.mx] using place_mx_eq b0 0 h0H h0D (rootStrip t.n) mv pk
      opsSz := by
        have hO := place_ops_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        simpa [b', bP, hO] using u.opsSz
      ops0 := by
        intro h
        have hO := place_ops_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        simpa [b', bP, hO] using u.ops0 (by rw [← hO]; exact h)
      ops1 := by
        intro h
        have hO := place_ops_eq b0 0 h0H h0D (rootStrip t.n) mv pk
        simpa [b', bP, hO] using u.ops1 (by rw [← hO]; exact h)
      moves := ⟨mv + pegCount (rootStrip t.n),
        by simpa [b', bP, ofNat_eq_natCast] using place_moves_eq b0 0 h0H h0D (rootStrip t.n) mv pk,
        spent_strip mv _ t.n t.benchlen hmvLe hpeg⟩
      slides := by
        rcases u.slides with ⟨sl, hsl, hle⟩
        exact ⟨sl, by simpa [b', bP] using (place_slides_eq b0 0 h0H h0D (rootStrip t.n) mv pk).trans hsl,
          hle⟩
      peak := by
        simpa [b', bP] using
          ⟨_, place_peak_nat b0 0 h0H h0D (rootStrip t.n) mv pk hpkI⟩
      strict := by
        rcases u.strict with ⟨ps, hps⟩
        exact ⟨ps, by simpa [b', bP] using
          (place_strict_eq b0 0 h0H h0D (rootStrip t.n) mv pk).trans hps⟩
      hole := by
        rcases u.hole with ⟨holeN, hhole⟩
        exact ⟨holeN, by simpa [b', bP] using
          (place_hole_eq b0 0 h0H h0D (rootStrip t.n) mv pk).trans hhole⟩ }

end EcbsLink2.Link2
