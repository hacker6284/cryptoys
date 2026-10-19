/-
  A nonzero root digit: the live multiply, then clear the cubed up home,
  then settle the product bench. The up home becomes `powStep`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowMul
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem powMulOff_on (bReady : Ecbs.Board) (spare peakS : Nat)
    (hS : spare < bReady.sudo_5Board_4held.size)
    (hHomeS : spare < bReady.sudo_5Board_4home.size)
    (dst mvW bench : Nat) :
    (powMulOff bReady spare peakS hS hHomeS dst mvW bench).sudo_5Board_8bench_on = true := by
  unfold powMulOff withMoves mulPrep strictBoard mulAimed
  rfl

theorem powMulOff_to (bReady : Ecbs.Board) (spare peakS : Nat)
    (hS : spare < bReady.sudo_5Board_4held.size)
    (hHomeS : spare < bReady.sudo_5Board_4home.size)
    (dst mvW bench : Nat) :
    (powMulOff bReady spare peakS hS hHomeS dst mvW bench).sudo_5Board_8bench_to =
      (dst : Int) := by
  unfold powMulOff withMoves mulPrep strictBoard mulAimed
  rfl

theorem powMulOff_slides (bReady : Ecbs.Board) (spare peakS : Nat)
    (hS : spare < bReady.sudo_5Board_4held.size)
    (hHomeS : spare < bReady.sudo_5Board_4home.size)
    (dst mvW bench : Nat) :
    (powMulOff bReady spare peakS hS hHomeS dst mvW bench).sudo_5Board_4cost.sudo_5Costs_6slides =
      bReady.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold powMulOff withMoves mulPrep strictBoard mulAimed
  rfl

theorem powLive_moves (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (powLiveBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv + foldCharge n (n - k) sch) := by
  unfold powLiveBoard ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem powLive_slides (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (powLiveBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold powLiveBoard ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem powLive_peak (b : Ecbs.Board) (sch : List Nat) (n k mv pk : Nat) :
    (powLiveBoard b sch n k mv pk).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pk (countHeld (ontoFoldBoard b sch n k mv pk).sudo_5Board_4held 7)) := by
  unfold powLiveBoard ontoFoldBoard peakBoard
  rfl

theorem powLive_bench (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (powLiveBoard b sch n k mv peak).sudo_5Board_5bench =
      embed (laneFold n (n - k) sch) := by
  simp only [powLiveBoard, ontoFoldBoard_bench]

theorem powLive_on (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (powLiveBoard b sch n k mv peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  simp only [powLiveBoard, ontoFoldBoard_on]

theorem powLive_to (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (powLiveBoard b sch n k mv peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to := by
  simp only [powLiveBoard, ontoFoldBoard_to]

theorem markerSeat_slides (b : Ecbs.Board) (m ctrl mx : Nat) :
    (markerSeat b m ctrl mx).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold markerSeat
  rfl

theorem bump_slides (b : Ecbs.Board) (i cOps : Nat)
    (hops : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    (bumpOp b i cOps hops).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold bumpOp
  rfl

private theorem lt_of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (hs : a[i]? = some v) : i < a.size := by
  by_cases h : i < a.size
  · exact h
  · rw [Array.getElem?_ge a (by omega : a.size ≤ i)] at hs
    cases hs

private theorem of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : i < a.size) (hs : a[i]? = some v) : a[i] = v := by
  rw [Array.getElem?_eq_getElem h] at hs
  injection hs

/-- After the live multiply the up home is still the cube, and it is held. -/
theorem powLive_up (bReady : Ecbs.Board) (spare peakS up mvW bench : Nat)
    (hS : spare < bReady.sudo_5Board_4held.size)
    (hHomeS : spare < bReady.sudo_5Board_4home.size)
    (cube : List Nat) (sch : List Nat) (n k mv peak : Nat)
    (hne : up ≠ spare)
    (hHome : bReady.sudo_5Board_4home[up]? = some (embed cube))
    (hHeld : bReady.sudo_5Board_4held[up]? = some true) :
    (powLiveBoard (powMulOff bReady spare peakS hS hHomeS up mvW bench) sch n k mv peak).sudo_5Board_4home[up]? =
      some (embed cube) ∧
    (powLiveBoard (powMulOff bReady spare peakS hS hHomeS up mvW bench) sch n k mv peak).sudo_5Board_4held[up]? =
      some true := by
  simp only [powLiveBoard, ontoFoldBoard_home, ontoFoldBoard_held, powMulOff, withMoves,
    mulPrep, strictBoard, mulAimed]
  refine ⟨?_, ?_⟩
  · rw [Array.getElem?_set_ne _ ⟨spare, hHomeS⟩ (#[] : Array Int) hne.symm]
    exact hHome
  · rw [Array.getElem?_set_ne _ ⟨spare, hS⟩ false hne.symm]
    exact hHeld

/-- A nonzero digit. `pow_mul_live` leaves the product on the bench; `clear`
    drops the cubed up home; `settle` writes the product there. That home is
    `powStep`. -/
theorem pow_digit_home (b : Ecbs.Board) (up spare : Nat) (lane cube factor acc rhs : List Nat)
    (d w h r n k moves slides peak peakS cOps m ctrl mx script bench hole : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (up : Int))
    (hH : up < b.sudo_5Board_4home.size)
    (hD : up < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[up] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitMv : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitSl : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hS : spare < b.sudo_5Board_4held.size)
    (hHomeS : spare < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[spare] = true)
    (hYs : b.sudo_5Board_4home[spare] = embed factor)
    (hne : up ≠ spare)
    (hn0 : 0 < n)
    (htake : lane.take n = cube)
    (hfacLen : factor.length = n)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hcubeT : allTritList cube)
    (hfi : FitsLen (2 * (n - 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * pegCount (lane.take n) + n * (n + 1) + 3 * (bench - n)))
    (hcube : cube = fieldCube n k bench acc)
    (hbranch : (d = 2 ∧ factor = fieldMul n k bench rhs rhs) ∨ (d = 1 ∧ factor = rhs))
    (hfitClear : FitsLen (moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n +
        foldCharge n (n - k) (school n cube factor (List.replicate bench 0) false) + pegCount cube))
    (hpegP : FitsLen (2 * pegCount (fieldMul n k bench cube factor)))
    (hfitSet : FitsLen (moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n +
        foldCharge n (n - k) (school n cube factor (List.replicate bench 0) false) + pegCount cube +
        2 * pegCount (fieldMul n k bench cube factor)))
    (hfitSl2 : FitsLen (slides + 2 * pegCount (lane.take n) +
        2 * pegCount (fieldMul n k bench cube factor))) :
    ∃ bS,
      (do
        let b1 ← Ecbs.mul b ((up : Nat) : Int) ((up : Nat) : Int) ((spare : Nat) : Int)
            false false false
        let b2 ← Ecbs.clear b1 ((up : Nat) : Int)
        Ecbs.settle b2) = .ok bS ∧
      (bS.sudo_5Board_4home[up]?) = some (embed (powStep n k bench rhs acc d)) ∧
      bS.sudo_5Board_8bench_on = false ∧
      (bS.sudo_5Board_4held[up]?) = some true ∧
      bS.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      bS.sudo_5Board_9marker_on = true ∧
      bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      (∀ i, i ≠ up → i ≠ spare → (bS.sudo_5Board_4home[i]?) = (b.sudo_5Board_4home[i]?)) ∧
      (∀ i, i ≠ up → i ≠ spare → (bS.sudo_5Board_4held[i]?) = (b.sudo_5Board_4held[i]?)) ∧
      (bS.sudo_5Board_4held[spare]?) = some false ∧
      bS.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n +
          foldCharge n (n - k) (school n cube factor (List.replicate bench 0) false) +
          pegCount cube + 2 * pegCount (fieldMul n k bench cube factor)) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n) +
          2 * pegCount (fieldMul n k bench cube factor)) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) := by
  have hmul := pow_mul_live b up spare lane cube factor w h r n k moves slides peak peakS cOps
      m ctrl mx script bench hole hmk hon hto hH hD h7 hempty hbench hn hpos hnle hzero hf hfitL
      hmoves hslides hpeak hpeg hfitMv hfitSl hops hop0 hfops hm hc hx hscript hbound hfitMk hfitC
      hfit2 hS hHomeS hHS hYs hne hn0 htake hfacLen hbl hpeakS hspan hcubeT hfi hhole hw0 hh0 hrR
      hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  let bReady := markerSeat (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
      (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)) m ctrl mx
  let hSready := ready_spare_held b up spare hH hD hS lane n moves slides peak cOps hops m ctrl mx
  let hHready := ready_spare_home b up spare hH hD hHomeS lane n moves slides peak cOps hops m ctrl mx
  let mvW := moves + 2 * pegCount (lane.take n) + schoolMoves cube factor n n
  let sch := school n cube factor (List.replicate bench 0) false
  let pk := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hD⟩ true) 7)
  let bOff := powMulOff bReady spare peakS hSready hHready up mvW bench
  let bLive := powLiveBoard bOff sch n k mvW pk
  rw [hmul, ok_bind]
  have hUpR : bReady.sudo_5Board_4home[up]? = some (embed cube) := by
    rw [show bReady.sudo_5Board_4home =
        (settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4home by
      simp [bReady, markerSeat, bumpOp]]
    rw [settle_home_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set, htake]
  have hHeldR : bReady.sudo_5Board_4held[up]? = some true := by
    rw [show bReady.sudo_5Board_4held =
        (settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4held by
      simp [bReady, markerSeat, bumpOp]]
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  have hboth := powLive_up bReady spare peakS up mvW bench hSready hHready cube sch n k mvW pk
      hne hUpR hHeldR
  have hHl : up < bLive.sudo_5Board_4home.size := lt_of_some _ _ _ hboth.1
  have hDl : up < bLive.sudo_5Board_4held.size := lt_of_some _ _ _ hboth.2
  have hheldL : bLive.sudo_5Board_4held[up] = true := of_some _ _ _ hDl hboth.2
  have harrL : bLive.sudo_5Board_4home[up] = embed cube := of_some _ _ _ hHl hboth.1
  have hmvL : bLive.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mvW + foldCharge n (n - k) sch) := by
    rw [powLive_moves]
  have hcf := clear_held_refines bLive up cube (mvW + foldCharge n (n - k) sch)
      hHl hDl hheldL harrL hmvL
      (by
        have hlen : cube.length = n := by
          rw [← htake, List.length_take, Nat.min_eq_left hnle]
        simpa [hlen] using hf)
      hfitClear
  rw [hcf, ok_bind]
  let mvC := mvW + foldCharge n (n - k) sch + pegCount cube
  let bC := { bLive with
    sudo_5Board_4home := bLive.sudo_5Board_4home.set ⟨up, hHl⟩ #[]
    sudo_5Board_4held := bLive.sudo_5Board_4held.set ⟨up, hDl⟩ false
    sudo_5Board_4cost := { bLive.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mvC } }
  let prod := laneFold n (n - k) sch
  have hsch : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length cube factor (List.replicate bench 0) false n
  have hnb : n ≤ bench := by omega
  have hprodL : prod.length = bench := by
    simpa [prod, hsch] using laneFold_length n (n - k) sch (by rw [hsch]; exact hnb)
  have hgap0 : 0 < n - k := by
    rw [hgap]
    exact Nat.mul_pos hw0 hrP
  have hzeroP : ∀ i, n ≤ i → ∀ hi : i < prod.length, prod[i] = 0 := by
    intro i hi hlt
    have hltS : i < sch.length := by
      rw [hsch, ← hprodL]
      exact hlt
    have hc := laneFold_high n (n - k) sch i hn0 hgap0 (by rw [hsch]; exact hnb) hi hltS
    rw [coeff_eq_get _ i hlt] at hc
    exact hc
  have honC : bC.sudo_5Board_8bench_on = true := by
    have h1 : bC.sudo_5Board_8bench_on = bLive.sudo_5Board_8bench_on := rfl
    rw [h1, show bLive.sudo_5Board_8bench_on = bOff.sudo_5Board_8bench_on from powLive_on _ _ _ _ _ _,
      powMulOff_on]
  have htoC : bC.sudo_5Board_8bench_to = (up : Int) := by
    have h1 : bC.sudo_5Board_8bench_to = bLive.sudo_5Board_8bench_to := rfl
    rw [h1, show bLive.sudo_5Board_8bench_to = bOff.sudo_5Board_8bench_to from powLive_to _ _ _ _ _ _,
      powMulOff_to]
  have hbenchC : bC.sudo_5Board_5bench = embed prod := by
    have h1 : bC.sudo_5Board_5bench = bLive.sudo_5Board_5bench := rfl
    rw [h1, powLive_bench]
  have hemptyC : bC.sudo_5Board_4held[up]'(by simpa [bC, Array.size_set] using hDl) = false := by
    simp [bC, Array.getElem_set]
  have hHn : up < bC.sudo_5Board_4home.size := by
    simpa [bC, Array.size_set] using hHl
  have hDn : up < bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set] using hDl
  have h7L : 7 ≤ bLive.sudo_5Board_4held.size := by
    rw [show bLive.sudo_5Board_4held.size = bOff.sudo_5Board_4held.size from by
      simp [bLive, powLiveBoard, ontoFoldBoard_held]]
    rw [show bOff.sudo_5Board_4held.size = bReady.sudo_5Board_4held.size from by
      simp [bOff, powMulOff, withMoves, mulPrep, strictBoard, mulAimed, Array.size_set]]
    rw [show bReady.sudo_5Board_4held.size =
        (settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4held.size from by
      simp [bReady, markerSeat, bumpOp]]
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak, Array.size_set]
    exact h7
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    simp [bC, Array.size_set]
    exact h7L
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simp [bC]
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (lane.take n)) := by
    have h1 : bC.sudo_5Board_4cost.sudo_5Costs_6slides =
        bLive.sudo_5Board_4cost.sudo_5Costs_6slides := rfl
    rw [h1, powLive_slides, powMulOff_slides, show bReady.sudo_5Board_4cost.sudo_5Costs_6slides =
        (bumpOp (settleBoard b up hH hD lane n moves slides peak) 0 cOps
          (settle_ops_lt b 0 up hops ⟨hH, hD⟩ lane n moves slides peak)).sudo_5Board_4cost.sudo_5Costs_6slides from
        by simp [bReady, markerSeat_slides], bump_slides,
      settle_slides_eq b up ⟨hH, hD⟩ lane n moves slides peak]
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7)) := by
    have h1 : bC.sudo_5Board_4cost.sudo_5Costs_4peak =
        bLive.sudo_5Board_4cost.sudo_5Costs_4peak := rfl
    rw [h1, powLive_peak]
    simp [bLive, powLiveBoard]
  have hprodTake : prod.take n = fieldMul n k bench cube factor := by
    simpa [prod, sch] using mul_no_prefix n k bench cube factor
  have hpegTake : FitsLen (2 * pegCount (prod.take n)) := by
    simpa [hprodTake] using hpegP
  have hfitM2 : FitsLen (mvC + 2 * pegCount (prod.take n)) := by
    simpa [mvC, hprodTake, mvW, sch] using hfitSet
  have hfitS2 : FitsLen (slides + 2 * pegCount (lane.take n) + 2 * pegCount (prod.take n)) := by
    simpa [hprodTake] using hfitSl2
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp only [bC, bLive, powLiveBoard, ontoFoldBoard_tier, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed, bReady, markerSeat, bumpOp]
    rw [settle_tier_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    exact hn
  have hset := settle_refines bC up prod n mvC (slides + 2 * pegCount (lane.take n))
      (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7)) hHn hDn h7C honC htoC hemptyC
      hbenchC hnC (by rw [hprodL]; omega) (by rw [hprodL]; exact hnb) hzeroP hf
      (by simpa [hprodL] using hfitB)
      hmvC hslC hpkC hpegTake hfitM2 hfitS2
  rw [hset]
  let bS := settleBoard bC up hHn hDn prod n mvC (slides + 2 * pegCount (lane.take n))
      (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))
  refine ⟨bS, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show bS.sudo_5Board_4home =
        bC.sudo_5Board_4home.set ⟨up, hHn⟩ (embed (prod.take n)) from
      settle_home_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hHn)]
    simp [Array.getElem_set, hprodTake]
    rw [hcube]
    rcases hbranch with ⟨hd, hf⟩ | ⟨hd, hf⟩
    · rw [hf, hd, powStep]
      simp
    · rw [hf, hd, powStep]
      simp
  · exact settle_bench_off bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
      (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))
  · rw [settle_held_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hDn)]
    simp [Array.getElem_set]
  · rw [settle_ix_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp [bC, bLive, powLiveBoard, ontoFoldBoard_mark, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed, bReady, markerSeat]
  · rw [settle_marker_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp [bC, bLive, powLiveBoard]
  · rw [settle_ctrl_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp [bC, bLive, powLiveBoard, ontoFoldBoard_ctrl, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed, bReady, markerSeat]
  · intro i hiu his
    rw [show bS.sudo_5Board_4home =
        bC.sudo_5Board_4home.set ⟨up, hHn⟩ (embed (prod.take n)) from
      settle_home_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    rw [Array.getElem?_set_ne _ ⟨up, hHn⟩ (embed (prod.take n)) hiu.symm]
    have hlive : bC.sudo_5Board_4home = bLive.sudo_5Board_4home.set ⟨up, hHl⟩ #[] := by
      simp [bC]
    rw [hlive, Array.getElem?_set_ne _ ⟨up, hHl⟩ (#[] : Array Int) hiu.symm]
    simp only [bLive, powLiveBoard, ontoFoldBoard_home, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed]
    rw [Array.getElem?_set_ne _ ⟨spare, hHready⟩ (#[] : Array Int) his.symm]
    rw [show bReady.sudo_5Board_4home =
        (settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4home by
      simp [bReady, markerSeat, bumpOp]]
    rw [settle_home_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_set_ne _ ⟨up, hH⟩ (embed (lane.take n)) hiu.symm]
  · intro i hiu his
    rw [settle_held_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    rw [Array.getElem?_set_ne _ ⟨up, hDn⟩ true hiu.symm]
    have hlive : bC.sudo_5Board_4held = bLive.sudo_5Board_4held.set ⟨up, hDl⟩ false := by
      simp [bC]
    rw [hlive, Array.getElem?_set_ne _ ⟨up, hDl⟩ false hiu.symm]
    simp only [bLive, powLiveBoard, ontoFoldBoard_held, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed]
    rw [Array.getElem?_set_ne _ ⟨spare, hSready⟩ false his.symm]
    rw [show bReady.sudo_5Board_4held =
        (settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4held by
      simp [bReady, markerSeat, bumpOp]]
    rw [settle_held_eq b up ⟨hH, hD⟩ lane n moves slides peak]
    rw [Array.getElem?_set_ne _ ⟨up, hD⟩ true hiu.symm]
  · rw [settle_held_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    rw [Array.getElem?_set_ne _ ⟨up, hDn⟩ true hne]
    have hlive : bC.sudo_5Board_4held = bLive.sudo_5Board_4held.set ⟨up, hDl⟩ false := by
      simp [bC]
    rw [hlive, Array.getElem?_set_ne _ ⟨up, hDl⟩ false hne]
    simp only [bLive, powLiveBoard, ontoFoldBoard_held, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hSready)]
    simp [Array.getElem_set]
  · rw [settle_moves_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp [mvC, mvW, sch, hprodTake]
  · rw [settle_slides_eq bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp [hprodTake]
  · rw [settle_ops bC up ⟨hHn, hDn⟩ prod n mvC (slides + 2 * pegCount (lane.take n))
        (raisedPeak pk (countHeld bLive.sudo_5Board_4held 7))]
    simp only [bC, bLive, powLiveBoard, ontoFoldBoard_ops, bOff, powMulOff, withMoves, mulPrep,
      strictBoard, mulAimed, bReady, markerSeat, bumpOp]
    have harr := settle_ops b up ⟨hH, hD⟩ lane n moves slides peak
    apply Array.ext
    · rw [Array.size_set, Array.size_set, harr]
    · intro i hi hi'
      have h? : ((settleBoard b up hH hD lane n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops.set
          ⟨0, by rw [harr]; exact hops⟩ (Int.ofNat (cOps + 1)))[i]? =
          (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)))[i]? := by
        by_cases h0 : i = 0
        · rw [h0, Array.getElem?_set_eq, Array.getElem?_set_eq]
        · rw [Array.getElem?_set_ne _ ⟨0, by rw [harr]; exact hops⟩ _
              (by intro h; exact h0 h.symm),
            Array.getElem?_set_ne _ ⟨0, hops⟩ _ (by intro h; exact h0 h.symm), harr]
      rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] at h?
      injection h?

end EcbsLink2.Link2
