/-
  After `chord_gap_clear`, `settle` slides the bench into the gap. The length-`n`
  prefix is `fieldMul` of the inverse by the rise, which is the spec slope.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordClear
import EcbsLink2.Link2.Settle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The product sitting on the bench after gap times spare. -/
def gapProduct (n k bench : Nat) (inv rise : List Nat) : List Nat :=
  laneFold n (n - k) (school n inv rise (List.replicate bench 0) false)

theorem gapMul_slides (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_peak (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨6, hS⟩ false) 7)) := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

theorem gapMul_tier (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size)
    (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  rfl

private theorem gapProduct_len (n k bench : Nat) (inv rise : List Nat) (hn : n ≤ bench) :
    (gapProduct n k bench inv rise).length = bench := by
  have hs : (school n inv rise (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using
      school_length inv rise (List.replicate bench 0) false n
  have hfold := laneFold_length n (n - k) (school n inv rise (List.replicate bench 0) false)
    (by rw [hs]; exact hn)
  simpa [gapProduct, hfold, hs] using hfold

private theorem gapProduct_zero (n k bench : Nat) (inv rise : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    ∀ i, n ≤ i → ∀ hi : i < (gapProduct n k bench inv rise).length,
      (gapProduct n k bench inv rise)[i] = 0 := by
  intro i hlo hi
  have hlen := gapProduct_len n k bench inv rise hn
  have hiB : i < bench := by rw [hlen] at hi; exact hi
  have hc := mul_no_high inv rise n k bench hn0 hgap0 i hlo hiB
  have hcoe : coeff (gapProduct n k bench inv rise) i =
      (gapProduct n k bench inv rise)[i] := coeff_eq_get _ i hi
  rw [← hcoe]
  simpa [gapProduct] using hc

/-- Slide the bench into the gap. The gap becomes the spec slope `fieldMul rise inv`,
    the bench turns off, and the marker flag stays on. SPEC.md §3 R7 line 156. -/
theorem chord_gap_settle (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : 5 < b.sudo_5Board_4held.size) (hHome : 5 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[5] = true)
    (hArr : b.sudo_5Board_4home[5] = embed inv)
    (hS : 6 < b.sudo_5Board_4held.size) (hHomeS : 6 < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[6] = true)
    (hYs : b.sudo_5Board_4home[6] = embed rise)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : inv.length = n) (hleny : rise.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList inv) (hrT : allTritList rise)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hfitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv))
    (hpeg : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
        2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n))) :
    let bM := gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
    let mv := mulMovesNo moves inv rise n k bench + pegCount inv
    let xs := gapProduct n k bench inv rise
    let peakC := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨6, hS⟩ false) 7)
    ∃ (bC : Ecbs.Board) (hH : 5 < bC.sudo_5Board_4home.size)
      (hD : 5 < bC.sudo_5Board_4held.size) (bS : Ecbs.Board),
      (do
        let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
        let b ← Ecbs.clear b Ecbs.gap
        Ecbs.settle b) = .ok bS ∧
      bS = settleBoard bC 5 hH hD xs n mv slides peakC ∧
      bS.sudo_5Board_4home = bC.sudo_5Board_4home.set ⟨5, hH⟩
        (embed (fieldMul n k bench rise inv)) ∧
      bS.sudo_5Board_8bench_on = false ∧
      bS.sudo_5Board_9marker_on = true := by
  intro bM mv xs peakC
  have hmul := chord_gap_mul b inv rise w h r n k moves hole bench peak peakS cOps m ctrl mx
    script hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hops hop0 hfops hbl hF hHome hHF
    hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm
    hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  have h5 : 5 < bM.sudo_5Board_4home.size := by
    rw [gapMul_home, Array.size_set]
    exact hHome
  have h5D : 5 < bM.sudo_5Board_4held.size := by
    rw [gapMul_held, Array.size_set]
    exact hF
  have harr5 : bM.sudo_5Board_4home[5] = embed inv := by
    have hEq := gapMul_home (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[]).size := by
      rw [Array.size_set]; exact hHome
    have htrans : bM.sudo_5Board_4home[5] =
        (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[])[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hArr]
  have hheld5 : bM.sudo_5Board_4held[5] = true := by
    have hEq := gapMul_held (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4held.set ⟨6, hS⟩ false).size := by
      rw [Array.size_set]; exact hF
    have htrans : bM.sudo_5Board_4held[5] =
        (b.sudo_5Board_4held.set ⟨6, hS⟩ false)[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hHF]
  have hmvM : bM.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((mulMovesNo moves inv rise n k bench) : Int) := by
    rw [gapMul_moves, ofNat_eq_natCast]
  have hfI : FitsLen inv.length := by rw [hlenx]; exact hf
  have hclear := clear_held_refines bM 5 inv (mulMovesNo moves inv rise n k bench)
    h5 h5D hheld5 harr5 hmvM hfI hfitClear
  let bC := { bM with
    sudo_5Board_4home := bM.sudo_5Board_4home.set ⟨5, h5⟩ #[]
    sudo_5Board_4held := bM.sudo_5Board_4held.set ⟨5, h5D⟩ false
    sudo_5Board_4cost := { bM.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (mulMovesNo moves inv rise n k bench + pegCount inv) } }
  have hmulEq : Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false = .ok bM := by
    simpa [bM, gapMulBoard] using hmul.1
  have hclearEq : Ecbs.clear bM Ecbs.gap = .ok bC := by
    simpa [bC, ofNat_eq_natCast, show Ecbs.gap = ((5 : Nat) : Int) from rfl] using hclear
  have hnB : n ≤ bench := by omega
  have hlen : xs.length = bench := gapProduct_len n k bench inv rise hnB
  have hpos : 0 < xs.length := by rw [hlen]; omega
  have hnle : n ≤ xs.length := by rw [hlen]; exact hnB
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hzero := gapProduct_zero n k bench inv rise hn0 hgap0 hnB
  have hfitL : FitsLen xs.length := by rw [hlen]; exact hfitB
  have hH : 5 < bC.sudo_5Board_4home.size := by
    simp only [bC, Array.size_set]
    exact h5
  have hD : 5 < bC.sudo_5Board_4held.size := by
    simp only [bC, Array.size_set]
    exact h5D
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    simp only [bC, Array.size_set]
    rw [gapMul_held, Array.size_set]
    exact h7
  have hempty : bC.sudo_5Board_4held[5] = false := by
    simp only [bC, Array.getElem_set, if_true]
  have hon : bC.sudo_5Board_8bench_on = true := by
    simp only [bC]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.1
  have hto : bC.sudo_5Board_8bench_to = (5 : Int) := by
    simp only [bC]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.2.1
  have hbench : bC.sudo_5Board_5bench = embed xs := by
    simp only [bC, xs, gapProduct]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).1
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp only [bC]
    rw [gapMul_tier, hn]
  have hmovesC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
    simp only [bC, mv]
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp only [bC]
    rw [gapMul_slides, hslides]
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simp only [bC, peakC]
    exact gapMul_peak b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
  have hset := settle_refines bC 5 xs n mv slides peakC hH hD h7C hon hto hempty hbench
    hnC hpos hnle hzero hf hfitL hmovesC hslC hpkC hpeg hfitSM hfitSS
  let bS := settleBoard bC 5 hH hD xs n mv slides peakC
  refine ⟨bC, hH, hD, bS, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hmulEq, ok_bind, hclearEq, ok_bind]
    simpa [bS, show Ecbs.gap = ((5 : Nat) : Int) from rfl] using hset
  · have hhome := settle_home_eq bC 5 hH hD xs n mv slides peakC
    have htake : xs.take n = fieldMul n k bench rise inv := by
      have hpre : xs.take n = fieldMul n k bench inv rise := by
        simpa [xs, gapProduct] using mul_no_prefix n k bench inv rise
      rw [hpre]
      exact (slope_mul_swap n k bench rise inv hrT hxsT).symm
    simpa [bS, htake] using hhome
  · simpa [bS] using settle_bench_off bC 5 hH hD xs n mv slides peakC
  · have hflag : bC.sudo_5Board_9marker_on = true := by
      simp only [bC]
      exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.2.2
    simpa [bS, hflag] using settle_marker_eq bC 5 hH hD xs n mv slides peakC
