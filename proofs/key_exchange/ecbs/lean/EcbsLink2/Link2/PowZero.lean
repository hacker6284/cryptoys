/-
  One root digit whose strip hole is empty. The power loop lifts the marker,
  cubes the up, and settles that bench. Digit `0` of `powStep` is that cube.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerCube
import EcbsLink2.Link2.CurveSideClose
import EcbsLink2.Link2.CurveSideSeat

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The marker is already off the script. `marker_lift` does not move it. -/
theorem marker_lift_below (b : Ecbs.Board) (hm : b.sudo_5Board_6marker < 0) :
    Ecbs.marker_lift b = .ok b := by
  unfold Ecbs.marker_lift
  have hdec : decide (b.sudo_5Board_6marker ≥ (0 : Int)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hm hle)
  rw [hdec]
  simp [Bool.false_eq_true, if_false, pure_eq_ok]

private theorem cube_lane_len (n k bench : Nat) (xs : List Nat) (hn : n ≤ bench) :
    (laneFold n (n - k) (combStrip n bench xs)).length = bench := by
  have hsch : (combStrip n bench xs).length = bench := combStrip_length n bench xs
  rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hn)]
  exact hsch

private theorem cube_lane_zero (n k bench : Nat) (xs : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    ∀ i, n ≤ i →
      ∀ hi : i < (laneFold n (n - k) (combStrip n bench xs)).length,
        (laneFold n (n - k) (combStrip n bench xs))[i] = 0 := by
  intro i hi hlt
  have hlen := cube_lane_len n k bench xs hn
  have hltb : i < bench := by rw [← hlen]; exact hlt
  have hc := cube_off_high xs n k bench hn0 hgap0 i hi hltb
  rw [coeff_eq_get _ i hlt] at hc
  exact hc

/-- Digit `0`: `marker_lift`, `cube` of the up, `settle`. The up home is the cube,
    which is `powStep` on digit `0`. The marker enters this arm already lifted. -/
theorem pow_zero_home (b : Ecbs.Board) (up : Nat) (acc rhs : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitCtrl : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : up < b.sudo_5Board_4held.size)
    (hHome : up < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[up] = true)
    (hArr : b.sudo_5Board_4home[up] = embed acc)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : acc.length = n)
    (hfn : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList acc)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n)))
    (hpeg : FitsLen (2 * pegCount (fieldCube n k bench acc)))
    (hfitMv : FitsLen (cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc)))
    (hfitSl : FitsLen (slides + 2 * pegCount (fieldCube n k bench acc))) :
    ∃ bS,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.cube b ((up : Nat) : Int) ((up : Nat) : Int)
          Ecbs.settle b) = .ok bS ∧
        (bS.sudo_5Board_4home[up]?) = some (embed (powStep n k bench rhs acc 0)) ∧
        bS.sudo_5Board_8bench_on = false ∧
        (bS.sudo_5Board_4held[up]?) = some true ∧
        bS.sudo_5Board_6marker = 0 ∧
        bS.sudo_5Board_9marker_on = true ∧
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc)) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_6slides =
          Int.ofNat (slides + 2 * pegCount (fieldCube n k bench acc)) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
          Int.ofNat (raisedHole hole (topIdx (combStrip n bench acc))) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1) ∧
        (∃ pk, bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
        (∃ ps, bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps) ∧
        (∀ i, i ≠ up → (bS.sudo_5Board_4home[i]?) = (b.sudo_5Board_4home[i]?)) ∧
        (∀ i, i ≠ up → (bS.sudo_5Board_4held[i]?) = (b.sudo_5Board_4held[i]?)) ∧
        bS.sudo_5Board_1t = b.sudo_5Board_1t ∧
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  have hlift := marker_lift_below b hm
  have hcube := cube_down_eq b up up acc w h r n k moves hole bench peak peakS cOps cg
      ctrl mx script hmk hoff hm hc hx hs hpos hfitCtrl hops hop1 hfops hF hHome hHF hArr h7
      hp hpeak hn0 hn hlenx hfn hmoves hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP hnE
      hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  let feed := markerDownFeed b ctrl mx
  let bOff := cubeOffBoard feed up up acc n k moves hole bench peak peakS cOps hops hF hHome
  let bC := { bOff with sudo_5Board_9marker_on := true }
  have hbC : Ecbs.cube b ((up : Nat) : Int) ((up : Nat) : Int) = .ok bC := by
    simpa [bC, bOff, feed] using hcube
  let lane := laneFold n (n - k) (combStrip n bench acc)
  have hnbench : n ≤ bench := by omega
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hlen := cube_lane_len n k bench acc hnbench
  have hposL : 0 < lane.length := by rw [hlen]; omega
  have hnle : n ≤ lane.length := by rw [hlen]; exact hnbench
  have hzero := cube_lane_zero n k bench acc hn0 hgap0 hnbench
  have hfitL : FitsLen lane.length := by rw [hlen]; exact hfitB
  have htake : lane.take n = fieldCube n k bench acc := cube_off_prefix n k bench acc
  have hfeedH : feed.sudo_5Board_4held = b.sudo_5Board_4held := by simp [feed, markerDownFeed]
  have hfeedS : feed.sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by simp [feed, markerDownFeed]
  have hfeedT : feed.sudo_5Board_1t = b.sudo_5Board_1t := by simp [feed, markerDownFeed]
  have hheldEq := cube_off_held feed up up acc n k moves hole bench peak peakS cOps hops hF hHome
  have hflagH : bC.sudo_5Board_4held = bOff.sudo_5Board_4held := by simp [bC]
  have hFf : up < feed.sudo_5Board_4held.size := by
    rw [hfeedH]
    exact hF
  have hDC : up < bC.sudo_5Board_4held.size := by
    rw [hflagH, hheldEq, Array.size_set]
    exact hFf
  have hempty : bC.sudo_5Board_4held[up] = false := by
    have h? : bC.sudo_5Board_4held[up]? = some false := by
      rw [hflagH, hheldEq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hFf)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem hDC] at h?
    injection h?
  have hflagHome : bC.sudo_5Board_4home = bOff.sudo_5Board_4home := by simp [bC]
  have hHomeF : up < feed.sudo_5Board_4home.size := by
    have hfeedHome : feed.sudo_5Board_4home = b.sudo_5Board_4home := by simp [feed, markerDownFeed]
    rw [hfeedHome]
    exact hHome
  have hHC : up < bC.sudo_5Board_4home.size := by
    rw [hflagHome, cube_off_home feed up up acc n k moves hole bench peak peakS cOps hops hF hHome,
      Array.size_set]
    exact hHomeF
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    rw [hflagH, hheldEq, Array.size_set, hfeedH]
    exact h7
  have hon : bC.sudo_5Board_8bench_on = true := by
    simp [bC, bOff, cube_off_on feed up up acc n k moves hole bench peak peakS cOps hops hF hHome]
  have hto : bC.sudo_5Board_8bench_to = (up : Int) := by
    simpa [bC, bOff] using
      cube_off_to feed up up acc n k moves hole bench peak peakS cOps hops hF hHome
  have hbench : bC.sudo_5Board_5bench = embed lane := by
    simpa [bC, bOff, lane] using
      cube_off_bench feed up up acc n k moves hole bench peak peakS cOps hops hF hHome
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    have hflagT : bC.sudo_5Board_1t = bOff.sudo_5Board_1t := by simp [bC]
    have hoffT : bOff.sudo_5Board_1t = feed.sudo_5Board_1t := by simp [bOff, cubeOffBoard]
    rw [hflagT, hoffT, hfeedT]
    exact hn
  let mvC := cubeMoves moves acc n k bench
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bC, bOff] using
      cube_off_moves feed up up acc n k moves hole bench peak peakS cOps hops hF hHome
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    have hflagSl : bC.sudo_5Board_4cost.sudo_5Costs_6slides =
        bOff.sudo_5Board_4cost.sudo_5Costs_6slides := by simp [bC]
    rw [hflagSl, cube_off_slides feed up up acc n k moves hole bench peak peakS cOps hops hF hHome,
      hfeedS]
    exact hslides
  let pkC := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hF⟩ false) 7)
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkC := by
    have hflagPk : bC.sudo_5Board_4cost.sudo_5Costs_4peak =
        bOff.sudo_5Board_4cost.sudo_5Costs_4peak := by simp [bC]
    rw [hflagPk, cube_off_peak feed up up acc n k moves hole bench peak peakS cOps hops hF hHome]
    simp [pkC, feed, markerDownFeed]
  have hpegL : FitsLen (2 * pegCount (lane.take n)) := by rw [htake]; exact hpeg
  have hfitM : FitsLen (mvC + 2 * pegCount (lane.take n)) := by rw [htake]; exact hfitMv
  have hfitS : FitsLen (slides + 2 * pegCount (lane.take n)) := by rw [htake]; exact hfitSl
  obtain ⟨bS, hset, hoffS, hheldS, hhome⟩ := cube_bench_settles bC up lane acc n k bench mvC slides pkC
    hHC hDC h7C hon hto hempty hbench hnC hposL hnle hzero hfn hfitL hmvC hslC hpkC
    hpegL hfitM hfitS htake
  have hpow : powStep n k bench rhs acc 0 = fieldCube n k bench acc := by
    rw [powStep_branch]
    simp
  have hsetR := settle_refines bC up lane n mvC slides pkC hHC hDC h7C hon hto hempty
    hbench hnC hposL hnle hzero hfn hfitL hmvC hslC hpkC hpegL hfitM hfitS
  have hEq : settleBoard bC up hHC hDC lane n mvC slides pkC = bS := by
    rw [hsetR] at hset
    injection hset with hEq
  have hmark : bS.sudo_5Board_6marker = 0 := by
    rw [← hEq, settle_ix_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [bC, bOff, cube_off_ix, feed, markerDownFeed]
  have hflagS : bS.sudo_5Board_9marker_on = true := by
    rw [← hEq, settle_marker_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
  have hctrlS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1) := by
    rw [← hEq, settle_ctrl_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp only [bC, bOff, cube_off_ctrl, feed, markerDownFeed]
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc)) := by
    rw [← hEq, settle_moves_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [mvC, htake]
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (fieldCube n k bench acc)) := by
    rw [← hEq, settle_slides_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [htake]
  have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := by
    rw [← hEq, settle_ops bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [bC, bOff, cube_off_ops, feed, markerDownFeed]
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx (combStrip n bench acc))) := by
    rw [← hEq, settle_hole_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [bC, bOff, cube_off_hole, feed, markerDownFeed, hhole]
  have hmxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1) := by
    rw [← hEq, settle_mx_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [bC, bOff, cube_off_mx, feed, markerDownFeed]
  have hpkS : ∃ pk, bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
    rw [← hEq]
    exact ⟨raisedPeak pkC (countHeld (bC.sudo_5Board_4held.set ⟨up, hDC⟩ true) 7),
      settle_peak_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC hpkC⟩
  have hpsS : ∃ ps, bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps := by
    rw [← hEq, settle_strict_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    refine ⟨raisedPeak peakS (countHeld b.sudo_5Board_4held 7), ?_⟩
    simp [bC, bOff, cube_off_strict, feed, markerDownFeed]
  have hhomeK : ∀ i, i ≠ up → (bS.sudo_5Board_4home[i]?) = (b.sudo_5Board_4home[i]?) := by
    intro i hiu
    rw [← hEq, settle_home_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    rw [Array.getElem?_set_ne _ ⟨up, hHC⟩ _ hiu.symm]
    simp only [bC, bOff, cube_off_home, feed, markerDownFeed]
    rw [Array.getElem?_set_ne _ ⟨up, hHome⟩ _ hiu.symm]
  have hheldK : ∀ i, i ≠ up → (bS.sudo_5Board_4held[i]?) = (b.sudo_5Board_4held[i]?) := by
    intro i hiu
    rw [← hEq, settle_held_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    rw [Array.getElem?_set_ne _ ⟨up, hDC⟩ _ hiu.symm]
    simp only [bC, bOff, cube_off_held, feed, markerDownFeed]
    rw [Array.getElem?_set_ne _ ⟨up, hF⟩ _ hiu.symm]
  have htierS : bS.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [← hEq, settle_tier_eq bC up ⟨hHC, hDC⟩ lane n mvC slides pkC]
    simp [bC, bOff, cube_off_tier, feed, markerDownFeed]
  have hszS : bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsS, Array.size_set]
  refine ⟨bS, ?_, ?_, hoffS, hheldS, hmark, hflagS, hctrlS, hmvS, hslS, hopsS, hholeS,
      hmxS, hpkS, hpsS, hhomeK, hheldK, htierS, hszS⟩
  · rw [hlift, ok_bind, hbC, ok_bind, hset]
  · rw [hhome, hpow]

end EcbsLink2.Link2
