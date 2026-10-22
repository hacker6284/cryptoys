/-
  Cube the copied peg on a board that is not the fresh `new_board`.
  The bench comes back holding `fieldCube` of that peg.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchOpen
import EcbsLink2.Link2.CurveTest

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem shape_of (t : Spec.Tier) (h : TierShape t) : BoardShape t.w t.h t.r t.n t.k where
  hw0 := h.w0
  hh0 := h.h0
  hrR := h.rlt
  hrP := h.r0
  hnE := h.n_eq
  hkLe := h.k_le
  hgap := h.gap

private theorem peak_if (pk occ : Nat) :
    (if pk < occ then occ else pk) = raisedPeak pk occ := by
  unfold raisedPeak
  rfl

/-- `cube bottom bottom` after the peg has been copied there. -/
theorem search_cube_on (bP : Ecbs.Board) (t : Spec.Tier) (hsh : TierShape t) (sat : TierSat t)
    (hOk : BoardOk t) (j mv pk ps holeN c1 : Nat)
    (hH : 2 < bP.sudo_5Board_4home.size) (hD : 2 < bP.sudo_5Board_4held.size)
    (hHs : 3 < bP.sudo_5Board_4home.size) (hDs : 3 < bP.sudo_5Board_4held.size)
    (h7 : 7 ≤ bP.sudo_5Board_4held.size)
    (hempty : bP.sudo_5Board_4held[2] = false)
    (hsrc : bP.sudo_5Board_4held[3] = true)
    (harr : bP.sudo_5Board_4home[3] = embed (basisPeg t.n j))
    (hmv : bP.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hpk : bP.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int))
    (hstrict : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps)
    (hhole : bP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN)
    (hflag : bP.sudo_5Board_9marker_on = false)
    (hbench : bP.sudo_5Board_8bench_on = false)
    (htier : bP.sudo_5Board_1t = embTier t)
    (hops : 1 < bP.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : bP.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (c1 : Int))
    (hfops : FitsLen (c1 + 1))
    (hfn : FitsLen t.n) (h3 : FitsLen (3 * (t.n - 1))) (hfitB : FitsLen t.benchlen)
    (hfm : FitsLen (mv + pegCount (basisPeg t.n j) + 2 * t.n))
    (hfold : FitsLen (mv + pegCount (basisPeg t.n j) + 2 * t.n + 3 * (t.benchlen - t.n))) :
    ∃ bC bK,
      Ecbs.copy_band bP Ecbs.bottom Ecbs.base_across false = .ok bC ∧
        Ecbs.cube bC Ecbs.bottom Ecbs.bottom = .ok bK ∧
        bK.sudo_5Board_8bench_on = true ∧
        bK.sudo_5Board_5bench =
          embed (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))) ∧
        (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))).take t.n =
          fieldCube t.n t.k t.benchlen (basisPeg t.n j) := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hn : bP.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    rw [htier, hx]; simp [embTier, ofNat_eq_natCast]
  have hfx : FitsLen x.length := by rw [hx]; exact hfn
  have hcopy := copy_band_refines bP 2 3 x mv pk hH hD hHs hDs h7 hsrc harr hempty
    hn hfx hmv hpk (FitsLen.of_le hfm (Nat.le_add_right (mv + pegCount x) (2 * t.n)))
  let bC := placeBoard bP 2 hH hD x mv pk
  have hCsz : bC.sudo_5Board_4held.size = bP.sudo_5Board_4held.size := by
    rw [place_held_eq, Array.size_set]
  have hF : 2 < bC.sudo_5Board_4held.size := by rw [hCsz]; exact hD
  have hHome : 2 < bC.sudo_5Board_4home.size := by
    rw [place_home_eq, Array.size_set]; exact hH
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by rw [hCsz]; exact h7
  have hheldC : bC.sudo_5Board_4held = bP.sudo_5Board_4held.set ⟨2, hD⟩ true :=
    place_held_eq bP 2 hH hD x mv pk
  have hhomeC : bC.sudo_5Board_4home = bP.sudo_5Board_4home.set ⟨2, hH⟩ (embed x) :=
    place_home_eq bP 2 hH hD x mv pk
  have htwice := countHeld_of_eq bC.sudo_5Board_4held
      (bP.sudo_5Board_4held.set ⟨2, hD⟩ true) hheldC 2 hF 7
  have hcollapse : ((bP.sudo_5Board_4held.set ⟨2, hD⟩ true).set
      ⟨2, hheldC ▸ hF⟩ true) = bP.sudo_5Board_4held.set ⟨2, hD⟩ true := by
    apply Array.ext
    · simp [Array.size_set]
    · intro i h1 h2
      by_cases hi : i = 2
      · simp [hi, Array.getElem_set]
      · simp [Array.getElem_set, hi]
  have hcount : countHeld (bC.sudo_5Board_4held.set ⟨2, hF⟩ true) 7 =
      countHeld (bP.sudo_5Board_4held.set ⟨2, hD⟩ true) 7 := by
    rw [htwice, hcollapse]
  have hpeakC : bC.sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak pk (countHeld (bC.sudo_5Board_4held.set ⟨2, hF⟩ true) 7) : Int) := by
    have hraw := place_peak_nat bP 2 hH hD x mv pk hpk
    rw [peak_if pk (countHeld (bP.sudo_5Board_4held.set ⟨2, hD⟩ true) 7)] at hraw
    rw [← hcount] at hraw
    simpa [ofNat_eq_natCast] using hraw
  have hgetH : (bP.sudo_5Board_4held.set ⟨2, hD⟩ true)[2]'(by rw [Array.size_set]; exact hD) =
      true := by simp [Array.getElem_set]
  have hHF : bC.sudo_5Board_4held[2] = true := cell_eq_of hheldC hgetH
  have hgetA : (bP.sudo_5Board_4home.set ⟨2, hH⟩ (embed x))[2]'(by rw [Array.size_set]; exact hH) =
      embed x := by simp [Array.getElem_set]
  have hArr : bC.sudo_5Board_4home[2] = embed x := cell_eq_of hhomeC hgetA
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv + pegCount x) := place_moves_eq bP 2 hH hD x mv pk
  have hflagC : bC.sudo_5Board_9marker_on = false := by
    rw [place_flag bP 2 hH hD x mv pk]; exact hflag
  have hbenchC : bC.sudo_5Board_8bench_on = false := by
    rw [place_bench bP 2 hH hD x mv pk]; exact hbench
  have hopsEq := place_ops_eq bP 2 hH hD x mv pk
  have hopsC : 1 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq]; exact hops
  have hopC : bC.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (c1 : Int) :=
    cell_eq_of hopsEq hop1
  have htierC : bC.sudo_5Board_1t = embTier t := by
    rw [place_tier_eq]; exact htier
  have hstrictC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps := by
    rw [place_strict_eq]; exact hstrict
  have hholeC : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN := by
    rw [place_hole_eq]; exact hhole
  have hcube := curve_cube_bottom bC x t.w t.h t.r t.n t.k (mv + pegCount x) holeN
      t.benchlen pk ps c1 t.combgap
      hflagC hbenchC hopsC hopC hfops
      (by rw [htierC]; rfl) (by rw [htierC]; rfl) sat.cube_span
      hF hHome hHF hArr h7C hOk.n_pos
      (by rw [htierC]; exact ofNat_eq_natCast _) hx hfn hmvC hpeakC hstrictC hxt
      h3 hfm (shape_of t hsh)
      (by rw [htierC]; rfl) (by rw [htierC]; rfl) (by rw [htierC]; rfl) (by rw [htierC]; rfl)
      hholeC hsh.small hsh.n_small hfitB hfold
  obtain ⟨bK, hok, hon, _, hbenchK, htake, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hcube
  refine ⟨bC, bK, ?_, hok, hon, ?_, ?_⟩
  · rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
      show Ecbs.base_across = ((3 : Nat) : Int) from rfl]
    exact hcopy
  · simpa [x] using hbenchK
  · simpa [x] using htake

end EcbsLink2.Link2
