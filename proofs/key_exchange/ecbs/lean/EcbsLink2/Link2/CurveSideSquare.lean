/-
  The square inside `curve_side`. `cube` leaves `x³` on the bench. `mul` with
  `onto = false` settles that bench into the destination, then lays `x²` on a
  fresh bench aimed at the spare. The following `settle` writes `x²` into the
  spare and leaves `x³` in the destination. The curve-side tail is
  `curve_side_of_cube`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MulSettle
import EcbsLink2.Link2.CurveSideClose
import EcbsLink2.Link2.CurveSideSeat

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem lane_len (n k bench : Nat) (x : List Nat) (hn : n ≤ bench) :
    (laneFold n (n - k) (school n x x (List.replicate bench 0) false)).length = bench := by
  have hsch : (school n x x (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hn)]
  exact hsch

private theorem prod_len (n k bench : Nat) (x : List Nat) (hn : n ≤ bench) :
    (fieldMul n k bench x x).length = n := by
  unfold fieldMul
  rw [List.length_take]
  have hsch : (school n x x (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hfold := laneFold_length n (n - k)
      (school n x x (List.replicate bench 0) false) (by rw [hsch]; exact hn)
  rw [laneFold] at hfold
  rw [hfold, hsch, Nat.min_eq_left hn]

private theorem lane_zero (n k bench : Nat) (x : List Nat) (hn : n ≤ bench)
    (hcoeff : ∀ i, n ≤ i → i < bench →
      coeff (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) i = 0) :
    ∀ i, n ≤ i →
      ∀ hi : i < (laneFold n (n - k) (school n x x (List.replicate bench 0) false)).length,
        (laneFold n (n - k) (school n x x (List.replicate bench 0) false))[i] = 0 := by
  intro i hi hlt
  have hlen := lane_len n k bench x hn
  have hltb : i < bench := by rw [← hlen]; exact hlt
  have hc : coeff (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) i = 0 :=
    hcoeff i hi hltb
  rw [coeff_eq_get _ i hlt] at hc
  exact hc

private theorem away_home (b : Ecbs.Board) (home i : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) (arr : Array Int)
    (hi : i < b.sudo_5Board_4home.size) (hne : home ≠ i)
    (h : b.sudo_5Board_4home[i] = arr) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4home[i]? =
      some arr := by
  rw [settle_home_eq b home hin xs n moves slides peak]
  rw [Array.getElem?_set_ne _ ⟨home, hin.hH⟩ (embed (xs.take n)) hne]
  rw [Array.getElem?_eq_getElem hi, h]

private theorem away_held (b : Ecbs.Board) (home i : Nat) (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) (v : Bool)
    (hi : i < b.sudo_5Board_4held.size) (hne : home ≠ i)
    (h : b.sudo_5Board_4held[i] = v) :
    (settleBoard b home hin.hH hin.hD xs n moves slides peak).sudo_5Board_4held[i]? =
      some v := by
  rw [settle_held_eq b home hin xs n moves slides peak]
  rw [Array.getElem?_set_ne _ ⟨home, hin.hD⟩ true hne]
  rw [Array.getElem?_eq_getElem hi, h]

private theorem of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : i < a.size) (hs : a[i]? = some v) : a[i] = v := by
  rw [Array.getElem?_eq_getElem h] at hs
  injection hs with hs

private theorem lt_of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (hs : a[i]? = some v) : i < a.size := by
  by_cases h : i < a.size
  · exact h
  · rw [Array.getElem?_ge a (by omega : a.size ≤ i)] at hs
    cases hs

/-- `mul` of a square, on the board whose bench still holds the cube.
    The multiply settles the cube into `cubeDst` and leaves `x²` on the bench
    aimed at the spare. `cubeDst` is not the spare, so that home stays the cube. -/
theorem square_mul (b : Ecbs.Board) (cubeDst src : Nat) (lane x : List Nat)
    (w h r n k moves slides peak peakS hole bench cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (cubeDst : Int))
    (hH : cubeDst < b.sudo_5Board_4home.size)
    (hD : cubeDst < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[cubeDst] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (htake : lane.take n = fieldCube n k bench x)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHeld : src < b.sudo_5Board_4held.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed x)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hsrc6 : src ≠ 6) (hsrcD : src ≠ cubeDst) (hdst6 : cubeDst ≠ 6)
    (hn0 : 0 < n) (hlenx : x.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitC : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList x)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x + n * (n + 1) +
        3 * (bench - n))) :
    ∃ bM,
      Ecbs.mul b ((6 : Nat) : Int) ((src : Nat) : Int) ((src : Nat) : Int) true false false =
        .ok bM ∧
      bM.sudo_5Board_8bench_on = true ∧
      bM.sudo_5Board_8bench_to = ((6 : Nat) : Int) ∧
      bM.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) ∧
      (laneFold n (n - k) (school n x x (List.replicate bench 0) false)).take n =
        fieldMul n k bench x x ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) i = 0) ∧
      bM.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mulMoves (moves + 2 * pegCount (lane.take n)) x x n k bench) ∧
      bM.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n)) ∧
      (∃ pk, bM.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
      bM.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) ∧
      bM.sudo_5Board_9marker_on = false ∧
      6 < bM.sudo_5Board_4home.size ∧
      6 < bM.sudo_5Board_4held.size ∧
      7 ≤ bM.sudo_5Board_4held.size ∧
      (∀ h6 : 6 < bM.sudo_5Board_4held.size, bM.sudo_5Board_4held[6] = false) ∧
      bM.sudo_5Board_4home[cubeDst]? = some (embed (fieldCube n k bench x)) ∧
      bM.sudo_5Board_4held[cubeDst]? = some true := by
  let bS := settleBoard b cubeDst hH hD lane n moves slides peak
  let hin : HomeIn b cubeDst := ⟨hH, hD⟩
  have hset := settle_refines b cubeDst lane n moves slides peak
    hH hD h7 hon hto hempty hbench hn hposL hnle hzero hf hfitL
    hmoves hslides hpeak hpeg hfitM hfitS
  obtain ⟨bSeat, hsetC, _, _, hhomeC⟩ := cube_bench_settles b cubeDst lane x n k bench
    moves slides peak hH hD h7 hon hto hempty hbench hn hposL hnle hzero hf hfitL
    hmoves hslides hpeak hpeg hfitM hfitS htake
  have hSeat : bSeat = bS := Except.ok.inj (hsetC.symm.trans hset)
  have hbridge := mul_settles_first b ((6 : Nat) : Int) ((src : Nat) : Int) ((src : Nat) : Int)
    true cubeDst lane n moves slides peak cOps hmk hon hto hH hD h7 hempty hbench hn
    hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS hops hop0 hfops
  have hmulEq :
      Ecbs.mul b ((6 : Nat) : Int) ((src : Nat) : Int) ((src : Nat) : Int) true false false =
        Ecbs.mul bS ((6 : Nat) : Int) ((src : Nat) : Int) ((src : Nat) : Int) true false false := by
    rw [hbridge.1, hset, ok_bind]
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b cubeDst hin lane n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    rw [settle_marker_eq b cubeDst hin lane n moves slides peak]
    exact hmk
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 cubeDst hops hin lane n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    have hget := get_eq_of_array
      (settle_ops b cubeDst hin lane n moves slides peak) 0 hopsS
    exact hget.trans hop0
  have htierS := settle_tier_eq b cubeDst hin lane n moves slides peak
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [htierS]; exact hn
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS]; exact hbl
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htierS]; exact hwF
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htierS]; exact hhF
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htierS]; exact hrF
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htierS]; exact hkF
  have hsrcH : src < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hHome
  have hsrcDsz : src < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hHeld
  have hsrcA? := away_home b cubeDst src hin lane n moves slides peak (embed x)
    hHome hsrcD.symm hArr
  have hsrcA : bS.sudo_5Board_4home[src] = embed x :=
    of_some _ _ _ hsrcH hsrcA?
  have hsrcT? := away_held b cubeDst src hin lane n moves slides peak true
    hHeld hsrcD.symm hHF
  have hsrcT : bS.sudo_5Board_4held[src] = true :=
    of_some _ _ _ hsrcDsz hsrcT?
  have h6H : 6 < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hSpHome
  have h6D : 6 < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hSpH
  have h6E? := away_held b cubeDst 6 hin lane n moves slides peak false hSpH hdst6 hSpE
  have h6E : bS.sudo_5Board_4held[6] = false := of_some _ _ _ h6D h6E?
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact h7
  let mvS := moves + 2 * pegCount (lane.take n)
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [settle_moves_eq b cubeDst hin lane n moves slides peak]
    exact (ofNat_eq_natCast mvS).symm
  let pkS := if peak < countHeld (b.sudo_5Board_4held.set ⟨cubeDst, hD⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨cubeDst, hD⟩ true) 7 else peak
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    rw [settle_peak_eq b cubeDst hin lane n moves slides peak hpeak]
    exact (ofNat_eq_natCast pkS).symm
  have hstS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [settle_strict_eq b cubeDst hin lane n moves slides peak]
    exact hpeakS
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [settle_hole_eq b cubeDst hin lane n moves slides peak]
    exact hHole
  have hslS : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (lane.take n)) :=
    settle_slides_eq b cubeDst hin lane n moves slides peak
  obtain ⟨bM, hmulM, honM, htoM, hbenchM, htakeM, hzeroM, hmovM, hpkM, hslM, htM, hszM,
      hheldM, _h5, hpresM, hmkM, _⟩ :=
    mul_refines bS 6 src src x x w h r n k mvS hole bench pkS peakS cOps
      hmkS hoffS hopsS hop0S hfops hblS hsrcDsz hsrcH hsrcT hsrcA hsrcDsz hsrcH hsrcT hsrcA
      h6D h6H h6E h7S hsrc6 hsrc6 hn0 hnS hlenx hlenx hf hmvS hpkS hstS hfitC hspan hxsT
      hfi hfm shape hwS hhS hrS hkS hholeS hsm hnsm hfitB hfold
  have hcubeH : cubeDst < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hH
  have hcubeH' : cubeDst < bM.sudo_5Board_4home.size := by rw [hszM]; exact hcubeH
  have hcubeD : cubeDst < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b cubeDst hin lane n moves slides peak, Array.size_set]
    exact hD
  have hszHeld : bM.sudo_5Board_4held.size = bS.sudo_5Board_4held.size := by
    rw [hheldM, Array.size_set, Array.size_set]
  have hcubeD' : cubeDst < bM.sudo_5Board_4held.size := by rw [hszHeld]; exact hcubeD
  have hhomeS : bS.sudo_5Board_4home[cubeDst]? = some (embed (fieldCube n k bench x)) := by
    rw [← hSeat]
    exact hhomeC
  have hheldS : bS.sudo_5Board_4held[cubeDst]? = some true := by
    rw [settle_held_eq b cubeDst hin lane n moves slides peak,
      Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  refine ⟨bM, ?_, honM, htoM, hbenchM, htakeM, hzeroM, ?_, ?_, ?_, ?_, hmkM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmulEq]; exact hmulM
  · exact hmovM
  · rw [hslM, hslS]
  · exact ⟨mulPeak bS.sudo_5Board_4held bM.sudo_5Board_4held h6D pkS, hpkM⟩
  · rw [htM]; exact hnS
  · rw [hszM]; exact h6H
  · rw [hszHeld]; exact h6D
  · rw [hszHeld]; exact h7S
  · intro h6
    have h? : bM.sudo_5Board_4held[6]? = some false := by
      rw [hheldM, Array.getElem?_eq_getElem (by rw [Array.size_set, Array.size_set]; exact h6D)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem h6] at h?
    injection h?
  · have hget : bM.sudo_5Board_4home[cubeDst] = embed (fieldCube n k bench x) := by
      rw [hpresM cubeDst hcubeH hcubeH' hdst6]
      exact of_some _ _ _ hcubeH hhomeS
    rw [Array.getElem?_eq_getElem hcubeH', hget]
  · rw [hheldM]
    rw [Array.getElem?_set_ne _ ⟨6, by rw [Array.size_set]; exact h6D⟩ false hdst6.symm]
    rw [Array.getElem?_set_ne _ ⟨6, h6D⟩ true hdst6.symm]
    exact hheldS

/-- Settle the square into the spare. The cube home is a different band, so it stays. -/
theorem square_settle (b : Ecbs.Board) (cubeDst : Nat) (lane : List Nat)
    (x : List Nat) (n k bench moves slides peak : Nat)
    (h6H : 6 < b.sudo_5Board_4home.size)
    (h6D : 6 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = ((6 : Nat) : Int))
    (hempty : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (htake : lane.take n = fieldMul n k bench x x)
    (_hcubeH : cubeDst < b.sudo_5Board_4home.size)
    (_hcubeD : cubeDst < b.sudo_5Board_4held.size)
    (hne : cubeDst ≠ 6)
    (hcube : b.sudo_5Board_4home[cubeDst]? = some (embed (fieldCube n k bench x)))
    (hheldC : b.sudo_5Board_4held[cubeDst]? = some true) :
    ∃ bS,
      Ecbs.settle b = .ok bS ∧
      bS.sudo_5Board_8bench_on = false ∧
      (∀ h : 6 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[6] = true) ∧
      (∀ h : 6 < bS.sudo_5Board_4home.size,
        bS.sudo_5Board_4home[6] = embed (fieldMul n k bench x x)) ∧
      (∀ h : cubeDst < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[cubeDst] = true) ∧
      (∀ h : cubeDst < bS.sudo_5Board_4home.size,
        bS.sudo_5Board_4home[cubeDst] = embed (fieldCube n k bench x)) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + 2 * pegCount (lane.take n)) ∧
      bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
  have hempty6 : b.sudo_5Board_4held[6] = false := hempty h6D
  have hset := settle_refines b 6 lane n moves slides peak h6H h6D h7 hon hto hempty6
    hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let hin6 : HomeIn b 6 := ⟨h6H, h6D⟩
  let bS := settleBoard b 6 h6H h6D lane n moves slides peak
  have hhome := settle_home_eq b 6 hin6 lane n moves slides peak
  have hheld := settle_held_eq b 6 hin6 lane n moves slides peak
  have hoff := settle_bench_off b 6 hin6 lane n moves slides peak
  have hmv := settle_moves_eq b 6 hin6 lane n moves slides peak
  have htier := settle_tier_eq b 6 hin6 lane n moves slides peak
  refine ⟨bS, hset, hoff, ?_, ?_, ?_, ?_, hmv, ?_⟩
  · intro h
    have h? : bS.sudo_5Board_4held[6]? = some true := by
      rw [hheld, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h6D)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem h] at h?
    injection h?
  · intro h
    have h? : bS.sudo_5Board_4home[6]? = some (embed (fieldMul n k bench x x)) := by
      rw [hhome, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h6H)]
      simp [Array.getElem_set, htake]
    rw [Array.getElem?_eq_getElem h] at h?
    injection h?
  · intro h
    have h? : bS.sudo_5Board_4held[cubeDst]? = some true := by
      rw [hheld, Array.getElem?_set_ne _ ⟨6, h6D⟩ true hne.symm]
      exact hheldC
    rw [Array.getElem?_eq_getElem h] at h?
    injection h?
  · intro h
    have h? : bS.sudo_5Board_4home[cubeDst]? = some (embed (fieldCube n k bench x)) := by
      rw [hhome, Array.getElem?_set_ne _ ⟨6, h6H⟩ (embed (lane.take n)) hne.symm]
      exact hcube
    rw [Array.getElem?_eq_getElem h] at h?
    injection h?
  · rw [htier]; exact hn

/-- Square the seated cube and close. The destination home is `curveSide`. -/
theorem curve_side_square (b : Ecbs.Board) (cubeDst src : Nat) (lane x : List Nat)
    (w h r n k moves slides peak peakS hole bench cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (cubeDst : Int))
    (hH : cubeDst < b.sudo_5Board_4home.size)
    (hD : cubeDst < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[cubeDst] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (htake : lane.take n = fieldCube n k bench x)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHeld : src < b.sudo_5Board_4held.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed x)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hsrc6 : src ≠ 6) (hsrcD : src ≠ cubeDst) (hdst6 : cubeDst ≠ 6)
    (hn0 : 0 < n) (hlenx : x.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitC : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList x)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x + n * (n + 1)))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount x + n * (n + 1) +
        3 * (bench - n)))
    (hpeg2 : FitsLen (2 * pegCount (fieldMul n k bench x x)))
    (hfitM2 : FitsLen (mulMoves (moves + 2 * pegCount (lane.take n)) x x n k bench +
        2 * pegCount (fieldMul n k bench x x)))
    (hfitS2 : FitsLen ((slides + 2 * pegCount (lane.take n)) +
        2 * pegCount (fieldMul n k bench x x)))
    (hfitClose : FitsLen (mulMoves (moves + 2 * pegCount (lane.take n)) x x n k bench +
        2 * pegCount (fieldMul n k bench x x) + 2 * n + 1))
    (hcubeLen : (fieldCube n k bench x).length = n)
    (htC : allTritList (fieldCube n k bench x))
    (htM : allTritList (fieldMul n k bench x x)) :
    ∃ bW,
      (do
          let b ← Ecbs.mul b ((6 : Nat) : Int) ((src : Nat) : Int) ((src : Nat) : Int)
            true false false
          let b ← Ecbs.settle b
          let b ← add b (cubeDst : Int) ((6 : Nat) : Int) true
          let b ← clear b ((6 : Nat) : Int)
          white0 b (cubeDst : Int)) = .ok bW ∧
        (∀ h : cubeDst < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[cubeDst] = embed (curveSide n k bench x)) := by
  obtain ⟨bM, hmul, honM, htoM, hbenchM, htakeM, hzeroM, hmovM, hslM, ⟨pk, hpkM⟩, hnM, _hmk,
      h6H, h6D, h7M, hemptyM, hcubeM, hheldM⟩ :=
    square_mul b cubeDst src lane x w h r n k moves slides peak peakS hole bench cOps
      hmk hon hto hH hD h7 hempty hbench hn hposL hnle hzero hf hfitL hmoves hslides hpeak
      hpeg hfitM hfitS htake hops hop0 hfops hbl hHome hHeld hHF hArr hSpH hSpHome hSpE
      hsrc6 hsrcD hdst6 hn0 hlenx hpeakS hfitC hspan hxsT hfi hfm shape hwF hhF hrF hkF
      hHole hsm hnsm hfitB hfold
  have hnbench : n ≤ bench := by omega
  let laneM := laneFold n (n - k) (school n x x (List.replicate bench 0) false)
  have hlenM : laneM.length = bench := lane_len n k bench x hnbench
  have hposM : 0 < laneM.length := by rw [hlenM]; omega
  have hnleM : n ≤ laneM.length := by rw [hlenM]; exact hnbench
  have hzeroL := lane_zero n k bench x hnbench hzeroM
  have hfitLM : FitsLen laneM.length := by rw [hlenM]; exact hfitB
  have htakeP : laneM.take n = fieldMul n k bench x x := htakeM
  have hpegP : FitsLen (2 * pegCount (laneM.take n)) := by rw [htakeP]; exact hpeg2
  let mvM := mulMoves (moves + 2 * pegCount (lane.take n)) x x n k bench
  let slM := slides + 2 * pegCount (lane.take n)
  have hmovN : bM.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvM := hmovM
  have hfitMP : FitsLen (mvM + 2 * pegCount (laneM.take n)) := by rw [htakeP]; exact hfitM2
  have hfitSP : FitsLen (slM + 2 * pegCount (laneM.take n)) := by rw [htakeP]; exact hfitS2
  have hcubeHM : cubeDst < bM.sudo_5Board_4home.size := lt_of_some _ _ _ hcubeM
  have hcubeDM : cubeDst < bM.sudo_5Board_4held.size := lt_of_some _ _ _ hheldM
  obtain ⟨bS, hset, hoffS, hheld6, hhome6, hheldC, hhomeC, hmvS, hnS⟩ :=
    square_settle bM cubeDst laneM x n k bench mvM slM pk
      h6H h6D h7M honM htoM hemptyM hbenchM hnM hposM hnleM hzeroL hf hfitLM
      hmovN hslM hpkM hpegP hfitMP hfitSP htakeP hcubeHM hcubeDM hdst6 hcubeM hheldM
  have hsetR := settle_refines bM 6 laneM n mvM slM pk h6H h6D h7M honM htoM (hemptyM h6D)
    hbenchM hnM hposM hnleM hzeroL hf hfitLM hmovN hslM hpkM hpegP hfitMP hfitSP
  have hSB : bS = settleBoard bM 6 h6H h6D laneM n mvM slM pk :=
    Except.ok.inj (hset.symm.trans hsetR)
  have h6Hs : 6 < bS.sudo_5Board_4home.size := by
    rw [hSB]
    exact settle_home_lt bM 6 ⟨h6H, h6D⟩ laneM n mvM slM pk
  have h6Ds : 6 < bS.sudo_5Board_4held.size := by
    rw [hSB]
    exact settle_held_lt bM 6 ⟨h6H, h6D⟩ laneM n mvM slM pk
  have hdstH : cubeDst < bS.sudo_5Board_4home.size := by
    rw [hSB, settle_home_eq bM 6 ⟨h6H, h6D⟩ laneM n mvM slM pk, Array.size_set]
    exact hcubeHM
  have hdstD : cubeDst < bS.sudo_5Board_4held.size := by
    rw [hSB, settle_held_eq bM 6 ⟨h6H, h6D⟩ laneM n mvM slM pk, Array.size_set]
    exact hcubeDM
  let mvC := mvM + 2 * pegCount (fieldMul n k bench x x)
  have hmC : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) := by
    rw [hmvS, htakeP]
    exact (ofNat_eq_natCast mvC).symm
  have hmulLen : (fieldMul n k bench x x).length = n := prod_len n k bench x hnbench
  obtain ⟨bW, hclose, hside, _, _⟩ := curve_side_of_cube bS cubeDst 6 x n k bench mvC
    hdstH hdstD h6Hs h6Ds hdst6.symm hdst6
    (hheldC hdstD) (hhomeC hdstH) (hheld6 h6Ds) (hhome6 h6Hs)
    hnS hlenx hn0 hxsT hmC hfitClose hoffS hcubeLen hmulLen htC htM
  refine ⟨bW, ?_, hside⟩
  · rw [hmul, ok_bind, hset, ok_bind]
    exact hclose

end EcbsLink2.Link2
