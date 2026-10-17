/-
  A live white or red cell with a nonempty run. The emitted chord tail is
  obtained from the square, the across/bottom settle, the take and the mirror,
  the onto multiply, and the slide. Each board is abstract.
  SPEC.md §3 R7 line 156.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordCell

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem ix {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- A write at slot 0 leaves every other ops slot. -/
private theorem ops_set0_skip {a b : Array Int} {hi : (0 : Nat) < a.size} {v : Int}
    (h : b = a.set ⟨0, hi⟩ v) (j : Nat) (hne : (0 : Nat) ≠ j)
    (hj : j < a.size) (hj' : j < b.size) :
    b[j]'hj' = a[j]'hj := by
  have hv := Array.getElem_set_ne a ⟨0, hi⟩ v (by rw [← h]; exact hj') hne
  exact (cell_eq_of (ha := hj') h hv).trans idx_irrel

/-- The square, keeping the homes the settle reads. Gap 5 is the slope.
    Homes other than the gap and the spare stay. -/
theorem square_kept (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2))
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
    (hfitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfmS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1)))
    (hfoldS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n)))
    (hfitW : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench)) :
    let slope := fieldMul n k bench rise inv
    ∃ bW benchL,
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          Ecbs.bench_white0 b) = .ok bW ∧
      bW.sudo_5Board_5bench = embed benchL ∧
      benchL.take n = fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n) ∧
      benchL.length = bench ∧
      (∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0) ∧
      bW.sudo_5Board_8bench_on = true ∧
      bW.sudo_5Board_8bench_to = Ecbs.bottom ∧
      bW.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      bW.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      bW.sudo_5Board_9marker_on = true ∧
      bW.sudo_5Board_6marker = Int.ofNat (m + 2) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max mx (m + 2)) (m + 3)) ∧
      bW.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bW.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mvSq (mvGap moves inv rise n k bench) slope n k bench) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slGap slides inv rise n k bench) ∧
      (∀ i, i ≠ 5 → i ≠ 6 → ∀ hi : i < b.sudo_5Board_4home.size,
        ∀ hi' : i < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      (∀ h : 5 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[5] = embed slope) ∧
      (∀ h : 5 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[5] = true) ∧
      (∀ i, i ≠ 6 → ∀ hi : i < b.sudo_5Board_4held.size,
        ∀ hi' : i < bW.sudo_5Board_4held.size,
          bW.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      (∃ peakW strictW holeW,
        bW.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakW ∧
        bW.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictW ∧
        bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeW ∧
        (∃ occ1 occ2, occ1 ≤ 7 ∧ occ2 ≤ 7 ∧
          strictW = raisedPeak (raisedPeak peakS occ1) occ2) ∧
        (∃ top1 top2, top1 ≤ bench ∧ top2 ≤ bench ∧
          holeW = raisedHole (raisedHole hole top1) top2) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ h : 0 < bW.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        bW.sudo_5Board_4cost.sudo_5Costs_3ops[0] = Int.ofNat (cOps + 2))) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      bW.sudo_5Board_3row = b.sudo_5Board_3row ∧
      TailStay b bW ∧
      (∀ h : 6 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[6] = false) ∧
      (∀ j, j ≠ 0 → ∀ (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hj' : j < bW.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          bW.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj' =
            b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj) := by
  intro slope
  obtain ⟨bS, hdo, _hmkS, hoffS, hmS, hcS, hxS, htS, hmvS, hslS, hszHs, hszDs, h5a, h5t,
      h6e, hhome, hheld, hopsEq, hpeak⟩ :=
    gap_settle_lay b inv rise w h r n k moves hole bench slides peak peakS cOps m ctrl mx
      script hmk hoff hm hc hx hscript (by omega) hfitM hfitC hfit2 hops hop0 hfops hbl
      hF hHome hHF hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hslides hpeak
      hpeakS hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm
      hnsm hfitB hfold hfitClear hpeg hfitSM hfitSS
  obtain ⟨hp, hhiS, hrowS, hstayS⟩ := hpeak
  obtain ⟨peakG, strictG, holeG, hpk, hst, hho, hstG, hhoG⟩ := hp
  have hlenS : slope.length = n := by
    simp only [slope]
    rw [← mul_no_prefix n k bench rise inv]
    have hs : (school n rise inv (List.replicate bench 0) false).length = bench := by
      simpa [List.length_replicate] using school_length rise inv (List.replicate bench 0) false n
    have hnB : n ≤ bench := by omega
    have hlenF := laneFold_length n (n - k) (school n rise inv (List.replicate bench 0) false)
      (by rw [hs]; exact hnB)
    simp [List.length_take, hlenF, hs]
    omega
  have htriS : allTritList slope := by
    simp only [slope]
    exact fieldMul_span_trits n k bench rise inv hspan (by omega)
  have h5hS : 5 < bS.sudo_5Board_4home.size := by rw [hszHs]; exact hHome
  have h5dS : 5 < bS.sudo_5Board_4held.size := by rw [hszDs]; exact hF
  have h6hS : 6 < bS.sudo_5Board_4home.size := by rw [hszHs]; exact hHomeS
  have h6dS : 6 < bS.sudo_5Board_4held.size := by rw [hszDs]; exact hS
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by rw [hszDs]; exact h7
  have hscriptS : bS.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by rw [htS]; exact hscript
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htS]; exact hw
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htS]; exact hh
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htS]; exact hr
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htS]; exact hk
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [htS]; exact hn
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [htS]; exact hbl
  have hopsSz : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq, Array.size_set]; exact hops
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((cOps + 1 : Nat) : Int) := by
    have hidx : 0 < (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1))).size := by
      rw [Array.size_set]; exact hops
    have hget : (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)))[0] =
        Int.ofNat (cOps + 1) := by simp [Array.getElem_set]
    simpa [hopsEq] using hget
  have hfitP : FitsLen (mvGap moves inv rise n k bench + pegCount slope) := by
    simp only [slope]
    exact FitsLen.of_le hfmS (by omega)
  obtain ⟨bW, benchL, hW, _hmkW, honW, htoW, hmW, hcW, hxW, htW, hmvW, hslW,
      hszW, hheldW, hbenchW, hpreW, hlenW, hzeroW, hhomeW, hheldIW, _h6W, _hopsW,
      hrest⟩ :=
    square_white_lay bS slope w h r n k (mvGap moves inv rise n k bench) holeG bench
      peakG strictG (cOps + 1) (m + 1) (ctrl + 2) (max mx (m + 2)) script
      _hmkS hoffS hmS hcS hxS hscriptS hbound hfit2 hfitC4 hfit3 hopsSz hop0S hfops2 hblS
      h5dS h5hS (h5t h5dS) (h5a h5hS) h6dS h6hS (h6e h6dS) h7S hn0 hnS hlenS hf hmvS
      hpk hst hspan htriS hfi hfmS hfitP hho hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS
      hsm hnsm hfitB hfoldS hfitW
  obtain ⟨hp, _hhiW, hrowW, hstayW⟩ := hrest
  obtain ⟨pk, st, ho, hpkW, hstW, hhoW, hstS, hhoS⟩ := hp
  refine ⟨bW, benchL, ?_, hbenchW, hpreW, hlenW, hzeroW, honW, htoW, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hassoc :
        (do
            let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
            let b ← Ecbs.clear b Ecbs.gap
            let b ← Ecbs.settle b
            let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
            Ecbs.bench_white0 b) =
        (do
            let b ←
              (do
                let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
                let b ← Ecbs.clear b Ecbs.gap
                Ecbs.settle b)
            let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
            Ecbs.bench_white0 b) := by
      simp only [except_pull]
    rw [hassoc, hdo, ok_bind, hW]
  · exact hszW.trans hszHs
  · exact hheldW.trans hszDs
  · exact _hmkW
  · exact hmW
  · exact hcW
  · exact hxW
  · exact htW.trans htS
  · exact hmvW
  · exact hslW.trans hslS
  · intro i hne5 hne6 hi hi'
    have hiS : i < bS.sudo_5Board_4home.size := by rw [hszHs]; exact hi
    have hW5 := hhomeW i hne6 hiS hi'
    have hS5 := hhome i hne5 hne6 hi hiS
    exact hW5.trans hS5
  · intro h5
    have hiS : 5 < bS.sudo_5Board_4home.size := by rw [hszW] at h5; exact h5
    have hne : (5 : Nat) ≠ 6 := by decide
    exact (hhomeW 5 hne hiS h5).trans (h5a hiS)
  · intro h5
    have hiS : 5 < bS.sudo_5Board_4held.size := by rw [hheldW] at h5; exact h5
    have hne : (5 : Nat) ≠ 6 := by decide
    exact (hheldIW 5 hne hiS h5).trans (h5t hiS)
  · intro i hne hi hi'
    have hiS : i < bS.sudo_5Board_4held.size := by rw [hszDs]; exact hi
    by_cases h5i : i = 5
    · subst h5i
      have hne5 : (5 : Nat) ≠ 6 := by decide
      exact (hheldIW 5 hne5 hiS hi').trans ((h5t hiS).trans hHF.symm)
    · exact (hheldIW i hne hiS hi').trans (hheld i h5i hne hi hiS)
  · have hstComb : ∃ occ1 occ2, occ1 ≤ 7 ∧ occ2 ≤ 7 ∧
        st = raisedPeak (raisedPeak peakS occ1) occ2 := by
      obtain ⟨occ1, h1, heq1⟩ := hstG
      obtain ⟨occ2, h2, heq2⟩ := hstS
      refine ⟨occ1, occ2, h1, h2, ?_⟩
      rw [heq2, heq1]
    have hhoComb : ∃ top1 top2, top1 ≤ bench ∧ top2 ≤ bench ∧
        ho = raisedHole (raisedHole hole top1) top2 := by
      obtain ⟨top1, h1, heq1⟩ := hhoG
      obtain ⟨top2, h2, heq2⟩ := hhoS
      refine ⟨top1, top2, h1, h2, ?_⟩
      rw [heq2, heq1]
    refine ⟨pk, st, ho, hpkW, hstW, hhoW, hstComb, hhoComb, ?_, ?_⟩
    · have hszS : bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hopsEq, Array.size_set]
      rw [_hopsW, Array.size_set]
      exact hszS
    · intro h0
      have hget := ix _hopsW 0 h0
      simpa [Array.getElem_set] using hget
  · exact _hhiW.trans hhiS
  · exact hrowW.trans hrowS
  · exact TailStay.trans hstayS hstayW
  · exact _h6W
  · intro j hne hj hj'
    have hne0 : (0 : Nat) ≠ j := fun h => hne h.symm
    have hjS : j < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [_hopsW, Array.size_set] at hj'
      exact hj'
    exact (ops_set0_skip _hopsW j hne0 hjS hj').trans (ops_set0_skip hopsEq j hne0 hj hjS)

/-- The square, then the two bench adds and the settle. The bottom is
    slope² + 1 + across − run. Across, up, and the gap stay. -/
theorem bottom_lay (b : Ecbs.Board) (inv rise accX run : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hHF : b.sudo_5Board_4held[5]'(by rw [hszD]; decide) = true)
    (hArr : b.sudo_5Board_4home[5]'(by rw [hszH]; decide) = embed inv)
    (hHS : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = true)
    (hYs : b.sudo_5Board_4home[6]'(by rw [hszH]; decide) = embed rise)
    (h0a : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed accX)
    (h0t : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (h2t : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (h2a : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed run)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : inv.length = n) (hleny : rise.length = n)
    (hxLen : accX.length = n) (hrun : run.length = n)
    (htriX : allTritList accX) (htriR : allTritList run)
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
    (hpegG : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
        2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfmS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1)))
    (hfoldS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n)))
    (hfitW : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench))
    (hfit1 : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench + n))
    (hfitA : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench + pegCount accX + n))
    (hfitRun : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench + pegCount accX + pegCount run + pegCount run))
    (hpegX : FitsLen (2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hfitMX : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench + pegCount accX + pegCount run + pegCount run +
        2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hfitSX : FitsLen (slGap slides inv rise n k bench +
        2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))) :
    let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    ∃ bX,
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          let b ← Ecbs.bench_white0 b
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          Ecbs.settle b) = .ok bX ∧
      bX.sudo_5Board_8bench_on = false ∧
      (∀ h : 2 < bX.sudo_5Board_4home.size, bX.sudo_5Board_4home[2] = embed x3) ∧
      (∀ h : 0 < bX.sudo_5Board_4home.size, bX.sudo_5Board_4home[0] = embed accX) ∧
      (∀ h : 0 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[0] = true) ∧
      (∀ h : 5 < bX.sudo_5Board_4home.size, bX.sudo_5Board_4home[5] = embed slope) ∧
      (∀ h : 5 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[5] = true) ∧
      bX.sudo_5Board_9marker_on = true ∧
      bX.sudo_5Board_4home.size = 8 ∧
      bX.sudo_5Board_4held.size = 8 ∧
      bX.sudo_5Board_6marker = Int.ofNat (m + 2) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max (max mx (m + 2)) (m + 3)) ∧
      bX.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bX.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mvSq (mvGap moves inv rise n k bench) slope n k bench +
          pegCount accX + pegCount run + pegCount run + 2 * pegCount x3) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slGap slides inv rise n k bench + 2 * pegCount x3) ∧
      (∀ h : 2 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[2] = true) ∧
      (∀ h : 1 < bX.sudo_5Board_4home.size, bX.sudo_5Board_4home[1] = b.sudo_5Board_4home[1]) ∧
      (∀ h : 1 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[1] = b.sudo_5Board_4held[1]) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_3ops.size = b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      (∀ h : 0 < bX.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        bX.sudo_5Board_4cost.sudo_5Costs_3ops[0] = Int.ofNat (cOps + 2)) ∧
      (∃ peakX strictX holeX,
        bX.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakX ∧
        bX.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictX ∧
        bX.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeX) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      bX.sudo_5Board_3row = b.sudo_5Board_3row ∧
      TailStay b bX ∧
      (∀ h : 6 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[6] = false) ∧
      (∀ j, j ≠ 0 → ∀ (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hj' : j < bX.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          bX.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj' =
            b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj) := by
  intro slope x3
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hF : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hHome : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have hS : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hHomeS : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  obtain ⟨bW, benchL, hsq, hbench, hpre, hlen, hzero, hon, hto, hszHW, hszDW, hmkW, hmW,
      hcW, hxW, htW, hmvW, hslW, hkeep, h5a, h5t, hheldK, htail⟩ :=
    square_kept b inv rise w h r n k moves hole bench slides peak peakS cOps m ctrl mx script
      hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hfitC4 hfit3 hops hop0 hfops hfops2 hbl
      hF hHome hHF hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hslides hpeak hpeakS
      hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB
      hfold hfitClear hpegG hfitSM hfitSS hfmS hfoldS hfitW
  obtain ⟨hpW, _hhiW, hrowW, hstaySq, h6W, hopSq⟩ := htail
  obtain ⟨peakW, strictW, holeW, hpkW, hstW, hhoW, _hstR, _hhoR, opsSz, hop0W⟩ := hpW
  have hnb : n ≤ bench := by omega
  have htriB : allTritList (benchL.take n) := by
    rw [hpre]
    exact fieldAdd_span_trits _ _ _
  have h0H : 0 < bW.sudo_5Board_4home.size := by rw [hszHW, hszH]; decide
  have h2H : 2 < bW.sudo_5Board_4home.size := by rw [hszHW, hszH]; decide
  have h2D : 2 < bW.sudo_5Board_4held.size := by rw [hszDW, hszD]; decide
  have hto2 : bW.sudo_5Board_8bench_to = (2 : Int) := by simpa [Ecbs.bottom] using hto
  have hmvI : bW.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((mvSq (mvGap moves inv rise n k bench) slope n k bench : Nat) : Int) := by
    rw [hmvW, ofNat_eq_natCast]
  have hslI : bW.sudo_5Board_4cost.sudo_5Costs_6slides =
      ((slGap slides inv rise n k bench : Nat) : Int) := by
    rw [hslW, ofNat_eq_natCast]
  have hpkI : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (peakW : Int) := by
    rw [hpkW, ofNat_eq_natCast]
  have h0aW : bW.sudo_5Board_4home[0]'h0H = embed accX :=
    (hkeep 0 (by decide) (by decide) (by rw [hszH]; decide) h0H).trans h0a
  have h2tW : bW.sudo_5Board_4held[2]'h2D = true :=
    (hheldK 2 (by decide) (by rw [hszD]; decide) h2D).trans h2t
  have h2aW : bW.sudo_5Board_4home[2]'h2H = embed run :=
    (hkeep 2 (by decide) (by decide) (by rw [hszH]; decide) h2H).trans h2a
  obtain ⟨bX, hx3do, hoffX, h2x, hmX, htX, hmvX, hslX, hszX, hszDX, hflagX, h2tX, hkeepX,
      hheldX, hcX, hxX, hopX, hstX, hhoX, hpkRest⟩ :=
    x3_settle_lay bW accX run benchL n k bench
      (mvSq (mvGap moves inv rise n k bench) slope n k bench)
      (slGap slides inv rise n k bench) peakW slope
      (by rw [hszHW]; exact hszH) (by rw [hszDW]; exact hszD) hon hto2 hbench
      h0aW h2tW h2aW
      (by rw [htW]; exact hn) hxLen hrun hn0 hlen hnb htriX htriR htriB hzero hpre hf hfitB
      hmvI hslI hpkI hfit1 hfitA hfitRun hpegX hfitMX hfitSX
  obtain ⟨⟨peakXN, hpkX⟩, hhiX, hrowX, hstayX⟩ := hpkRest
  refine ⟨bX, ?_, hoffX, h2x, ?_, ?_, ?_, ?_, hflagX.trans hmkW,
      hszX.trans (hszHW.trans hszH), hszDX.trans (hszDW.trans hszD),
      hmX.trans hmW, hcX.trans hcW, hxX.trans hxW, htX.trans htW,
      hmvX, hslX, h2tX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hassoc :
        (do
            let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
            let b ← Ecbs.clear b Ecbs.gap
            let b ← Ecbs.settle b
            let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
            let b ← Ecbs.bench_white0 b
            let b ← Ecbs.bench_add b Ecbs.across false
            let b ← Ecbs.bench_add b Ecbs.bottom true
            let b ← Ecbs.clear b Ecbs.bottom
            Ecbs.settle b) =
        (do
            let b ←
              (do
                let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
                let b ← Ecbs.clear b Ecbs.gap
                let b ← Ecbs.settle b
                let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
                Ecbs.bench_white0 b)
            let b ← Ecbs.bench_add b Ecbs.across false
            let b ← Ecbs.bench_add b Ecbs.bottom true
            let b ← Ecbs.clear b Ecbs.bottom
            Ecbs.settle b) := by
      simp only [except_pull]
    rw [hassoc, hsq, ok_bind, hx3do]
  · intro h0
    have h0W : 0 < bW.sudo_5Board_4home.size := by rw [hszX] at h0; exact h0
    exact (hkeepX 0 (by decide) h0W h0).trans h0aW
  · intro h0
    have h0W : 0 < bW.sudo_5Board_4held.size := by rw [hszDX] at h0; exact h0
    have h0b : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hheldX 0 (by decide) h0W h0).trans ((hheldK 0 (by decide) h0b h0W).trans h0t)
  · intro h5
    have h5W : 5 < bW.sudo_5Board_4home.size := by rw [hszX] at h5; exact h5
    exact (hkeepX 5 (by decide) h5W h5).trans (h5a h5W)
  · intro h5
    have h5W : 5 < bW.sudo_5Board_4held.size := by rw [hszDX] at h5; exact h5
    exact (hheldX 5 (by decide) h5W h5).trans (h5t h5W)
  · intro h1
    have h1W : 1 < bW.sudo_5Board_4home.size := by rw [hszX] at h1; exact h1
    have h1b : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
    exact (hkeepX 1 (by decide) h1W h1).trans
      (hkeep 1 (by decide) (by decide) h1b h1W)
  · intro h1
    have h1W : 1 < bW.sudo_5Board_4held.size := by rw [hszDX] at h1; exact h1
    have h1b : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
    exact (hheldX 1 (by decide) h1W h1).trans (hheldK 1 (by decide) h1b h1W)
  · rw [hopX, opsSz]
  · intro h0
    have hget := ix hopX 0 h0
    exact hget.trans (hop0W (hopX ▸ h0))
  · exact ⟨peakXN, strictW, holeW, hpkX, hstX.trans hstW, hhoX.trans hhoW⟩
  · exact hhiX.trans _hhiW
  · exact hrowX.trans hrowW
  · exact TailStay.trans hstaySq hstayX
  · intro h
    have hW : 6 < bW.sudo_5Board_4held.size := by
      rw [hszDX] at h
      exact h
    exact (hheldX 6 (by decide) hW h).trans (h6W hW)
  · intro j hne hj hj'
    have hjW : j < bW.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopX] at hj'
      exact hj'
    exact (ix hopX j hj').trans (hopSq j hne hj hjW)

/-- The lane fold's holes from `n` up are empty. One fact for the settle's tail. -/
theorem fold_tail (n gap : Nat) (strip : List Nat)
    (hn0 : 0 < n) (hg : 0 < gap) (hn : n ≤ strip.length) :
    ∀ i, n ≤ i → ∀ hi : i < (laneFold n gap strip).length, (laneFold n gap strip)[i] = 0 := by
  intro i hlo hi
  have hlen := laneFold_length n gap strip hn
  have hiS : i < strip.length := by rwa [hlen] at hi
  rw [← coeff_eq_get _ _ hi]
  exact laneFold_high n gap strip i hn0 hg hn hlo hiS

/-- Clear the gap, settle the bench into the up, and move the bottom into the
    across. Homes are 1, 0, 2, 5 on a board of eight. The up is the bench
    prefix and the across is the bottom's list. One move room and one slide
    room cover the settle and the move: a length-`n` home has at most `n` pegs.
    Those two rooms are what a later budget supplies. -/
theorem slide_point (b : Ecbs.Board) (slope x3 benchL : List Nat)
    (n moves slides peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h5t : b.sudo_5Board_4held[5]'(by rw [hszD]; decide) = true)
    (h5a : b.sudo_5Board_4home[5]'(by rw [hszH]; decide) = embed slope)
    (h1e : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h0e : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h2t : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (h2a : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed x3)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (1 : Int))
    (hbench : b.sudo_5Board_5bench = embed benchL)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenS : slope.length = n) (hlenX : x3.length = n)
    (hpos : 0 < benchL.length) (hnle : n ≤ benchL.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen benchL.length)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hRoomM : FitsLen (moves + 5 * n)) (hRoomS : FitsLen (slides + 4 * n))
    (h6e : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false) :
    ∃ b',
      (do
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          Ecbs.move_band b Ecbs.across Ecbs.bottom) = .ok b' ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[1] = embed (benchL.take n)) ∧
      b'.sudo_5Board_8bench_on = false ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
      TailStay b b' ∧
      (∀ h : 2 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[2] = (#[] : Array Int)) ∧
      (∀ h : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2] = false) ∧
      (∀ h : 5 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[5] = (#[] : Array Int)) ∧
      (∀ h : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5] = false) ∧
      (∀ h : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6] = false) ∧
      b'.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      (∃ pk', b'.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk') ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount slope + 2 * pegCount (benchL.take n) + 2 * pegCount x3) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (benchL.take n) + 2 * pegCount x3) ∧
      (∀ h : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) ∧
      (∀ h : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1] = true) ∧
      b'.sudo_5Board_4home.size = 8 ∧
      b'.sudo_5Board_4held.size = 8 := by
  have hpegY : pegCount (benchL.take n) ≤ n := by
    have hlen : (benchL.take n).length = n := by
      simp [List.length_take, Nat.min_eq_left hnle]
    simpa [hlen] using pegCount_le (benchL.take n)
  have hpegX : pegCount x3 ≤ n := by
    simpa [hlenX] using pegCount_le x3
  have hpegS : pegCount slope ≤ n := by
    simpa [hlenS] using pegCount_le slope
  have hfitClear : FitsLen (moves + pegCount slope) :=
    FitsLen.of_le hRoomM (by omega)
  have hpeg : FitsLen (2 * pegCount (benchL.take n)) :=
    FitsLen.of_le hRoomM (by omega)
  have hfitSM : FitsLen (moves + pegCount slope + 2 * pegCount (benchL.take n)) :=
    FitsLen.of_le hRoomM (by omega)
  have hfitSS : FitsLen (slides + 2 * pegCount (benchL.take n)) :=
    FitsLen.of_le hRoomS (by omega)
  have hfit2 : FitsLen (2 * pegCount x3) :=
    FitsLen.of_le hRoomM (by omega)
  have hfitMM : FitsLen (moves + pegCount slope + 2 * pegCount (benchL.take n) +
      2 * pegCount x3) := FitsLen.of_le hRoomM (by omega)
  have hfitMS : FitsLen (slides + 2 * pegCount (benchL.take n) + 2 * pegCount x3) :=
    FitsLen.of_le hRoomS (by omega)
  obtain ⟨b', hdo, hUp, h1t, hAc, h0t, h2e, h2f, h5e, h5f, hoff, hflag, _, hszH', hszD',
      hmv, hsl, hhi, hrow, hstay, h6f, hmark, hmx, hctrl, hops, hstrict, hhole, hpk⟩ :=
    chord_up_slide b 1 0 2 5 slope x3 benchL n moves slides peak
      (by rw [hszH]; decide) (by rw [hszD]; decide)
      (by rw [hszH]; decide) (by rw [hszD]; decide)
      (by rw [hszH]; decide) (by rw [hszD]; decide)
      (by rw [hszH]; decide) (by rw [hszD]; decide)
      (by rw [hszD]; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h5t h5a h1e h0e h2t h2a hon hto hbench hn hlenS hlenX hpos hnle hzero
      hf hfitL hmv hsl hpk hfitClear hpeg hfitSM hfitSS hfit2 hfitMM hfitMS
      (by decide) (by decide)
      (by rw [hszD]; decide) h6e (by decide)
  refine ⟨b', ?_, ?_, ?_, hoff, hflag, hhi, hrow, hstay, h2e, h2f, h5e, h5f, h6f,
      hmark, hmx, hctrl, hops, hstrict, hhole, hpk, hmv, hsl, h0t, h1t, ?_, ?_⟩
  · exact hdo
  · intro h0
    exact hAc h0
  · intro h1
    exact hUp h1
  · rw [hszH']; exact hszH
  · rw [hszD']; exact hszD

/-- Take the bottom from the across, mirror the up, lay the slope times that
    difference onto the up, and slide the new x across. SPEC.md §3 R7 line 156.
    The board is the one `bottom_lay` leaves. -/
theorem point_from_bottom (b : Ecbs.Board) (accX accY x3 slope : List Nat)
    (w h r n k bench moves slides peak peakS hole cOps m ctrl mx script : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h0t : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (h0a : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed accX)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY)
    (h2t : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (h2a : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed x3)
    (h5t : b.sudo_5Board_4held[5]'(by rw [hszD]; decide) = true)
    (h5a : b.sudo_5Board_4home[5]'(by rw [hszH]; decide) = embed slope)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hxA : accX.length = n) (hyA : accY.length = n) (hx3 : x3.length = n)
    (hslope : slope.length = n) (hn0 : 0 < n) (hnb : n ≤ bench)
    (htriX : allTritList accX) (htriY : allTritList accY) (htri3 : allTritList x3)
    (htriS : allTritList slope)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hstrict : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hfit : FitsLen (moves + 2 * n)) (hf : FitsLen n)
    (hspan : 2 * (n - 1) < bench) (hfi : FitsLen (2 * (n - 1)))
    (hfitMo : FitsLen (moves + pegCount x3 + pegCount accY + 2 * n))
    (hfitSo : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + pegCount x3 + pegCount accY + 2 * n + n * (n + 1)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
        3 * (bench - n)))
    (hTailM : FitsLen (moves + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
        3 * (bench - n) + 5 * n))
    (hTailS : FitsLen (slides + 6 * n))
    (h6e : b.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false) :
    let dx := fieldSub n accX x3
    let yMir := mirrorTrits accY
    let y3 := chordY3 n k bench slope dx accY
    let benchL := laneFold n (n - k) (school n slope dx (pref yMir bench n) false)
    ∃ bM b',
      (do
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) =
        .ok (markerOn bM) ∧
      (markerOn bM).sudo_5Board_5bench = embed benchL ∧
      benchL.take n = y3 ∧
      (markerOn bM).sudo_5Board_4home.size = 8 ∧
      (markerOn bM).sudo_5Board_4held.size = 8 ∧
      (∀ h : 0 < (markerOn bM).sudo_5Board_4held.size,
        (markerOn bM).sudo_5Board_4held[0] = false) ∧
      (∀ h : 0 < (markerOn bM).sudo_5Board_4home.size,
        (markerOn bM).sudo_5Board_4home[0] = (#[] : Array Int)) ∧
      (∀ h : 1 < (markerOn bM).sudo_5Board_4held.size,
        (markerOn bM).sudo_5Board_4held[1] = false) ∧
      (∀ h : 1 < (markerOn bM).sudo_5Board_4home.size,
        (markerOn bM).sudo_5Board_4home[1] = (#[] : Array Int)) ∧
      (∀ h : 2 < (markerOn bM).sudo_5Board_4held.size,
        (markerOn bM).sudo_5Board_4held[2] = true) ∧
      (∀ h : 2 < (markerOn bM).sudo_5Board_4home.size,
        (markerOn bM).sudo_5Board_4home[2] = embed x3) ∧
      (∀ h : 5 < (markerOn bM).sudo_5Board_4held.size,
        (markerOn bM).sudo_5Board_4held[5] = true) ∧
      (∀ h : 5 < (markerOn bM).sudo_5Board_4home.size,
        (markerOn bM).sudo_5Board_4home[5] = embed slope) ∧
      (markerOn bM).sudo_5Board_8bench_on = true ∧
      (markerOn bM).sudo_5Board_8bench_to = (1 : Int) ∧
      (do
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          Ecbs.move_band b Ecbs.across Ecbs.bottom) = .ok b' ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row ∧
      TailStay b b' ∧
      (∀ h : 2 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[2] = (#[] : Array Int)) ∧
      (∀ h : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2] = false) ∧
      (∀ h : 5 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[5] = (#[] : Array Int)) ∧
      (∀ h : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5] = false) ∧
      (∀ h : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6] = false) ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx (m + 2)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount x3 + pegCount accY + 2 * pegCount yMir +
          schoolMoves slope dx n n +
          foldCharge n (n - k) (school n slope dx (pref yMir bench n) false) +
          pegCount slope + 2 * pegCount (benchL.take n) + 2 * pegCount x3) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount yMir + 2 * pegCount (benchL.take n) +
          2 * pegCount x3) ∧
      (∃ pk', b'.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk') ∧
      (∃ st, b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat st) ∧
      (∃ ho, b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat ho) ∧
      (∀ h : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) ∧
      (∀ h : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1] = true) ∧
      b'.sudo_5Board_4home.size = 8 ∧
      b'.sudo_5Board_4held.size = 8 ∧
      b'.sudo_5Board_8bench_on = false ∧
      (∀ j, j ≠ 0 → ∀ (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
        (hj' : j < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size),
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj' =
            b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj) := by
  intro dx yMir y3 benchL
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h5H : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h5D : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  obtain ⟨bT, h0s, h1s, htDo, h0dx, h1m, hheldT, hszT, honT, _htoT, _hbenchT, hmT, hflagT,
      htT, hslT, hcT, hxT, hopT, hstT, hhoT, hpkT, hmvT, hkeepT, hhiT, hrowT, hstayT⟩ :=
    chord_take_mirror b accX x3 accY n moves h0H h0D h0t h0a h2H h2D h2t h2a h1H h1D h1t h1a
      hn hxA hx3 hyA hn0 htriX htri3 htriY hmv hfit
  have hmvN : moves + pegCount x3 + pegCount accY =
      moves + pegCount x3 + pegCount accY := rfl
  have h0HT : 0 < bT.sudo_5Board_4home.size := by rw [hszT]; exact h0H
  have h1HT : 1 < bT.sudo_5Board_4home.size := by rw [hszT]; exact h1H
  have h2HT : 2 < bT.sudo_5Board_4home.size := by rw [hszT]; exact h2H
  have h5HT : 5 < bT.sudo_5Board_4home.size := by rw [hszT]; exact h5H
  have h5DT : 5 < bT.sudo_5Board_4held.size := by rw [hheldT]; exact h5D
  have h2DT : 2 < bT.sudo_5Board_4held.size := by rw [hheldT]; exact h2D
  have h0DT : 0 < bT.sudo_5Board_4held.size := by rw [hheldT]; exact h0D
  have h1DT : 1 < bT.sudo_5Board_4held.size := by rw [hheldT]; exact h1D
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7T : 7 ≤ bT.sudo_5Board_4held.size := by rw [hheldT]; exact h7
  have hyM : yMir.length = n := by simp [yMir, mirror_length, hyA]
  have hdx : dx.length = n := fieldSub_length n accX x3
  have htriM : allTritList yMir := mirrorTrits_allTrit htriY
  have htriD : allTritList dx := by
    simpa [dx, fieldSub] using fieldAdd_span_trits n accX (mirrorTrits x3)
  have hflagM : bT.sudo_5Board_9marker_on = true := hflagT.trans hmk
  have hoffM : bT.sudo_5Board_8bench_on = false := honT.trans hoff
  have hmM : bT.sudo_5Board_6marker = Int.ofNat m := hmT.trans hm
  have hcM : bT.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := hcT.trans hc
  have hxM : bT.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := hxT.trans hx
  have hslM : bT.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) := hslT.trans hsl
  have hpkM : bT.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := hpkT.trans hpk
  have hstM : bT.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := hstT.trans hstrict
  have hhoM : bT.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := hhoT.trans hhole
  have hmvM : bT.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount x3 + pegCount accY : Nat) : Int) := by
    rw [hmvT, ofNat_eq_natCast]
  have h5aT : bT.sudo_5Board_4home[5]'h5HT = embed slope :=
    (hkeepT 5 (by decide) (by decide) h5H h5HT).trans h5a
  have h1b : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h5b : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0b : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1tT : bT.sudo_5Board_4held[1]'(hheldT.symm ▸ h1b) = true :=
    (ix hheldT.symm 1 h1b).symm.trans h1t
  have h5tT : bT.sudo_5Board_4held[5]'(hheldT.symm ▸ h5b) = true :=
    (ix hheldT.symm 5 h5b).symm.trans h5t
  have h0tT : bT.sudo_5Board_4held[0]'(hheldT.symm ▸ h0b) = true :=
    (ix hheldT.symm 0 h0b).symm.trans h0t
  have hnT : bT.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    conv => lhs; rw [htT]
    exact hn
  have hscriptT : bT.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    conv => lhs; rw [htT]
    exact hscript
  have hblT : bT.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    conv => lhs; rw [htT]
    exact hbl
  have hwT : bT.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    conv => lhs; rw [htT]
    exact hw
  have hhT : bT.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    conv => lhs; rw [htT]
    exact hh
  have hrT : bT.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    conv => lhs; rw [htT]
    exact hr
  have hkT : bT.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    conv => lhs; rw [htT]
    exact hk
  obtain ⟨bM, hmul, hbenchM, hpreM, hlay, hhiM, hrowM, hstayM, hopsM, hstM', hhoM'⟩ :=
    mul_onto_up_prefix bT 1 5 0 yMir slope dx w h r n k
      (moves + pegCount x3 + pegCount accY) slides hole peak peakS bench cOps m ctrl mx script
      hflagM hoffM hmM hcM hxM hscriptT hbound hfitMk hfitC hfit2
      (by rw [hopT]; exact hops) (by simpa [hopT] using hop0) hfops
      hblT
      (hheldT.symm ▸ h1b) h1s h1tT h1m
      (hheldT.symm ▸ h5b) h5HT h5tT h5aT
      (hheldT.symm ▸ h0b) h0s h0tT h0dx
      h7T (by decide) (by decide) (by decide) hn0 hnb hnT
      hyM hslope hdx hf hmvM hslM hpkM hstM hspan htriM htriS hfi
      hfitMo hfitSo hfm hhoM
      hw0 hh0 hrR hrP hnE hkLe hgap hwT hhT hrT hkT hsm hnsm hfitB hfold
      (by decide) (by decide)
  let sch := school n slope dx (pref yMir bench n) false
  have hbenchL : benchL = laneFold n (n - k) sch := rfl
  have hpreY : benchL.take n = y3 := by
    have hswap : fieldAdd n yMir (fieldMul n k bench slope dx) =
        fieldAdd n (mirrorTrits accY) (fieldMul n k bench slope dx) := rfl
    rw [show benchL.take n = fieldAdd n yMir (fieldMul n k bench slope dx) from hpreM, hswap]
    simpa [y3, yMir, dx, chordY3, fieldSub] using
      (card_y3 n k bench slope dx accY)
  let bU := markerOn bM
  have hszMH : bM.sudo_5Board_4home.size = 8 := by
    rw [hlay.szH]
    simp [bumpOp, markerUpFeed, hszT, hszH]
  have hszMD : bM.sudo_5Board_4held.size = 8 := by
    rw [hlay.szD]
    have hs : bT.sudo_5Board_4held.size = 8 := by rw [hheldT, hszD]
    simpa [bumpOp, markerUpFeed] using hs
  have hszU : bU.sudo_5Board_4home.size = 8 ∧ bU.sudo_5Board_4held.size = 8 := by
    simp [bU, markerOn, hszMH, hszMD]
  have h0eU : bU.sudo_5Board_4held[0]'(by rw [hszU.2]; decide) = false := by
    simpa [bU, markerOn_held] using hlay.heldS (by rw [hszMD]; decide)
  have h0aU : bU.sudo_5Board_4home[0]'(by rw [hszU.1]; decide) = (#[] : Array Int) := by
    simpa [bU, markerOn_home] using hlay.homeS (by rw [hszMH]; decide)
  have h1eU : bU.sudo_5Board_4held[1]'(by rw [hszU.2]; decide) = false := by
    simpa [bU, markerOn_held] using hlay.heldD (by rw [hszMD]; decide)
  have h1aU : bU.sudo_5Board_4home[1]'(by rw [hszU.1]; decide) = (#[] : Array Int) := by
    simpa [bU, markerOn_home] using hlay.homeD (by rw [hszMH]; decide)
  have h2tU : bU.sudo_5Board_4held[2]'(by rw [hszU.2]; decide) = true := by
    have hkeep := hlay.heldK 2 (by decide) (by decide)
      (by rw [← hlay.szD, hszMD]; decide) (by rw [hszMD]; decide)
    simpa [bU, markerOn_held, bumpOp, markerUpFeed, hheldT, h2t] using hkeep
  have h2aU : bU.sudo_5Board_4home[2]'(by rw [hszU.1]; decide) = embed x3 := by
    have hkeep := hlay.homeK 2 (by decide) (by decide)
      (by rw [← hlay.szH, hszMH]; decide) (by rw [hszMH]; decide)
    have hbt := (hkeepT 2 (by decide) (by decide) h2H h2HT).trans h2a
    simpa [bU, markerOn_home, bumpOp, markerUpFeed, hbt] using hkeep
  have h5tU : bU.sudo_5Board_4held[5]'(by rw [hszU.2]; decide) = true := by
    have hkeep := hlay.heldK 5 (by decide) (by decide)
      (by rw [← hlay.szD, hszMD]; decide) (by rw [hszMD]; decide)
    simpa [bU, markerOn_held, bumpOp, markerUpFeed, hheldT, h5t] using hkeep
  have h5aU : bU.sudo_5Board_4home[5]'(by rw [hszU.1]; decide) = embed slope := by
    have hkeep := hlay.homeK 5 (by decide) (by decide)
      (by rw [← hlay.szH, hszMH]; decide) (by rw [hszMH]; decide)
    simpa [bU, markerOn_home, bumpOp, markerUpFeed, h5aT] using hkeep
  have honU : bU.sudo_5Board_8bench_on = true := by
    simpa [bU, markerOn_on] using hlay.on
  have htoU : bU.sudo_5Board_8bench_to = (1 : Int) := by
    simpa [bU, markerOn] using hlay.to_
  have hbenchU : bU.sudo_5Board_5bench = embed benchL := by
    simpa [bU, markerOn] using hbenchM
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    have ht : bU.sudo_5Board_1t = bT.sudo_5Board_1t := by
      rw [show bU.sudo_5Board_1t = bM.sudo_5Board_1t from by simp [bU, markerOn], hlay.tier]
      simp [bumpOp, markerUpFeed]
    simpa [ht] using hnT
  let mvF := (moves + pegCount x3 + pegCount accY + 2 * pegCount yMir +
      schoolMoves slope dx n n) + foldCharge n (n - k) sch
  let slF := slides + 2 * pegCount yMir
  have hmvU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mvF : Int) := by
    rw [show bU.sudo_5Board_4cost.sudo_5Costs_5moves = bM.sudo_5Board_4cost.sudo_5Costs_5moves from
      by simp [bU, markerOn], hlay.moves, ofNat_eq_natCast]
  have hslU : bU.sudo_5Board_4cost.sudo_5Costs_6slides = (slF : Int) := by
    rw [show bU.sudo_5Board_4cost.sudo_5Costs_6slides = bM.sudo_5Board_4cost.sudo_5Costs_6slides from
      by simp [bU, markerOn], hlay.slides, ofNat_eq_natCast]
  obtain ⟨pkU, hpkU⟩ := hlay.peak
  have hpkB : bU.sudo_5Board_4cost.sudo_5Costs_4peak = (pkU : Int) := by
    rw [show bU.sudo_5Board_4cost.sudo_5Costs_4peak = bM.sudo_5Board_4cost.sudo_5Costs_4peak from
      by simp [bU, markerOn], hpkU, ofNat_eq_natCast]
  have hlenB : benchL.length = bench := by
    have hpref : (pref yMir bench n).length = bench := pref_length hnb (by rw [hyM]; exact Nat.le_refl _)
    have hschLen : sch.length = bench := by
      simpa [sch, hpref] using school_length slope dx (pref yMir bench n) false n
    have hfoldLen := laneFold_length n (n - k) sch (by rw [hschLen]; exact hnb)
    simpa [hbenchL, hfoldLen, hschLen]
  have hzero : ∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0 := by
    intro i hlo hi
    have hg : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
    have hstrip : n ≤ sch.length := by
      have hpref : (pref yMir bench n).length = bench := pref_length hnb (by rw [hyM]; exact Nat.le_refl _)
      have hschLen : sch.length = bench := by
        simpa [sch, hpref] using school_length slope dx (pref yMir bench n) false n
      rw [hschLen]; exact hnb
    have htail := fold_tail n (n - k) sch hn0 hg hstrip i hlo
    simpa [hbenchL] using htail (by simpa [hbenchL] using hi)
  have hpx : pegCount x3 ≤ n := by simpa [hx3] using pegCount_le x3
  have hpy : pegCount accY ≤ n := by simpa [hyA] using pegCount_le accY
  have hpym : pegCount yMir ≤ n := by simpa [hyM] using pegCount_le yMir
  have hschB : schoolMoves slope dx n n ≤ n * (n + 1) := schoolMoves_bound slope dx n
  have hfoldB : foldCharge n (n - k) sch ≤ 3 * (bench - n) := by
    have hle := foldCharge_bound n (n - k) sch
    have hpref : (pref yMir bench n).length = bench := pref_length hnb (by rw [hyM]; exact Nat.le_refl _)
    have hlenS : sch.length = bench := by
      simpa [sch, hpref] using school_length slope dx (pref yMir bench n) false n
    simpa [hlenS] using hle
  have hmvLe : mvF + 5 * n ≤
      moves + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n) + 5 * n := by
    dsimp [mvF]
    omega
  have hslLe : slF + 4 * n ≤ slides + 6 * n := by
    dsimp [slF]
    omega
  have h6eU : bU.sudo_5Board_4held[6]'(by rw [hszU.2]; decide) = false := by
    have h6T : 6 < bT.sudo_5Board_4held.size := by rw [hheldT]; rw [hszD]; decide
    have h6eT : bT.sudo_5Board_4held[6]'h6T = false := by
      have hEq : bT.sudo_5Board_4held = b.sudo_5Board_4held := hheldT
      exact cell_eq_of hEq h6e
    have h6M : 6 < bM.sudo_5Board_4held.size := by
      rw [hszMD]; decide
    have h6eM : bM.sudo_5Board_4held[6]'h6M = false :=
      (hlay.heldK 6 (by decide) (by decide) h6T h6M).trans h6eT
    have hEq : bU.sudo_5Board_4held = bM.sudo_5Board_4held := by simp [bU, markerOn_held]
    exact cell_eq_of hEq h6eM
  obtain ⟨b', hslide, hAc, hUp, hoffS, _, hhiS, hrowS, hstayS, h2e, h2f, h5e, h5f, h6f,
      hmarkS, hmxS, hctrlS, hopsS, hstrictS, hholeS, hpkS, hmvS, hslS, h0tS, h1tS,
      hszHS, hszDS⟩ :=
    slide_point bU slope x3 benchL n mvF slF pkU
      hszU.1 hszU.2 h5tU h5aU h1eU h0eU h2tU h2aU honU htoU hbenchU hnU
      hslope hx3 (by rw [hlenB]; omega) (by rw [hlenB]; exact hnb) hzero
      hf (by simpa [hlenB] using hfitB) hmvU hslU hpkB
      (FitsLen.of_le hTailM hmvLe) (FitsLen.of_le hTailS hslLe) h6eU
  have hmarkOut : b'.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    have hU : bU.sudo_5Board_6marker = bM.sudo_5Board_6marker := by simp [bU, markerOn]
    have hM : bM.sudo_5Board_6marker = Int.ofNat (m + 1) := by
      simpa [bumpOp, markerUpFeed] using hlay.marker
    exact hmarkS.trans (hU.trans hM)
  have hctrlOut : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = bM.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
      simp [bU, markerOn]
    have hM : bM.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
      simpa [bumpOp, markerUpFeed] using hlay.ctrl
    exact hctrlS.trans (hU.trans hM)
  have hmxOut : b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        bM.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by simp [bU, markerOn]
    have hM : bM.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) := by
      simpa [bumpOp, markerUpFeed] using hlay.mx
    exact hmxS.trans (hU.trans hM)
  have hopsOut : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) := by
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_3ops = bM.sudo_5Board_4cost.sudo_5Costs_3ops := by
      simp [bU, markerOn]
    have hstep := hopsS.trans (hU.trans hopsM)
    rw [hstep]
    apply Array.ext
    · rw [Array.size_set, Array.size_set]
      exact congrArg Array.size hopT
    · intro i hi1 hi2
      by_cases h0 : i = 0
      · subst h0
        simp [Array.getElem_set]
      · have hne : ¬ (0 = i) := fun h => h0 h.symm
        simp [Array.getElem_set, hne]
        have hiT : i < bT.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rwa [Array.size_set] at hi1
        exact ix hopT i hiT
  have hmvOut : b'.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount x3 + pegCount accY + 2 * pegCount yMir +
        schoolMoves slope dx n n +
        foldCharge n (n - k) (school n slope dx (pref yMir bench n) false) +
        pegCount slope + 2 * pegCount (benchL.take n) + 2 * pegCount x3) := by
    exact hmvS
  have hslOut : b'.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount yMir + 2 * pegCount (benchL.take n) +
        2 * pegCount x3) := by
    exact hslS
  have hstOut : ∃ st, b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat st := by
    obtain ⟨st, hst⟩ := hstM'
    refine ⟨st, ?_⟩
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        bM.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by simp [bU, markerOn]
    exact hstrictS.trans (hU.trans hst)
  have hhoOut : ∃ ho, b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat ho := by
    obtain ⟨ho, hho⟩ := hhoM'
    refine ⟨ho, ?_⟩
    have hU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bM.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by simp [bU, markerOn]
    exact hholeS.trans (hU.trans hho)
  refine ⟨bM, b', ?_, ?_, hpreY, hszU.1, hszU.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, honU, htoU,
      ?_, hAc, ?_, ?_, ?_, ?_, h2e, h2f, h5e, h5f, h6f, hmarkOut, hctrlOut, hmxOut, hopsOut,
      hmvOut, hslOut, hpkS, hstOut, hhoOut, h0tS, h1tS, hszHS, hszDS, hoffS, ?_⟩
  · have hassoc :
        (do
            let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
            let b ← Ecbs.mirror b Ecbs.up
            Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) =
        (do
            let b ←
              (do
                let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
                Ecbs.mirror b Ecbs.up)
            Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) := by
      simp only [except_pull]
    rw [hassoc, htDo, ok_bind]
    exact hmul
  · simpa [bU] using hbenchU
  · intro h0
    simpa [bU] using h0eU
  · intro h0
    simpa [bU] using h0aU
  · intro h1
    simpa [bU] using h1eU
  · intro h1
    simpa [bU] using h1aU
  · intro h2
    simpa [bU] using h2tU
  · intro h2
    simpa [bU] using h2aU
  · intro h5
    simpa [bU] using h5tU
  · intro h5
    simpa [bU] using h5aU
  · have hassoc :
        (do
            let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
            let b ← Ecbs.mirror b Ecbs.up
            let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
            let b ← Ecbs.clear b Ecbs.gap
            let b ← Ecbs.settle b
            Ecbs.move_band b Ecbs.across Ecbs.bottom) =
        (do
            let b ←
              (do
                let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
                let b ← Ecbs.mirror b Ecbs.up
                Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false)
            let b ← Ecbs.clear b Ecbs.gap
            let b ← Ecbs.settle b
            Ecbs.move_band b Ecbs.across Ecbs.bottom) := by
      simp only [except_pull]
    rw [hassoc]
    have hmulDo :
        (do
            let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
            let b ← Ecbs.mirror b Ecbs.up
            Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) =
          .ok bU := by
      have hassoc2 :
          (do
              let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
              let b ← Ecbs.mirror b Ecbs.up
              Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) =
          (do
              let b ←
                (do
                  let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
                  Ecbs.mirror b Ecbs.up)
              Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) := by
        simp only [except_pull]
      rw [hassoc2, htDo, ok_bind]
      simpa [bU] using hmul
    rw [hmulDo, ok_bind]
    exact hslide
  · intro h1
    simpa [hpreY] using hUp h1
  · have hhiU : bU.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bM.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
      simp [bU, markerOn]
    exact hhiS.trans (hhiU.trans (hhiM.trans hhiT))
  · have hrowU : bU.sudo_5Board_3row = bM.sudo_5Board_3row := by
      simp [bU, markerOn_row]
    exact hrowS.trans (hrowU.trans (hrowM.trans hrowT))
  · have hstayU : TailStay bM bU := by
      refine TailStay.of_eq (by simp [bU, markerOn]) (by simp [bU, markerOn])
        (by simp [bU, markerOn]) (by simp [bU, markerOn]) (by simp [bU, markerOn])
        (by simp [bU, markerOn]) (by simp [bU, markerOn]) (by simp [bU, markerOn])
        (by simp [bU, markerOn]) (by simp [bU, markerOn])
        (by simp [homeD, bU, markerOn]) (by simp [heldD, bU, markerOn])
        (by simp [homeD, bU, markerOn]) (by simp [heldD, bU, markerOn])
    exact TailStay.trans hstayT (TailStay.trans hstayM (TailStay.trans hstayU hstayS))
  · intro j hne hj hj'
    exact ops_set0_skip hopsOut j (fun h => hne h.symm) hj hj'


/-- The emitted chord tail is the square-and-settle prefix, then the slide,
    then the generated `pure`. -/
theorem chord_do_join (b bX b' : Ecbs.Board)
    (hpre :
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          let b ← Ecbs.bench_white0 b
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          Ecbs.settle b) = .ok bX)
    (hpost :
      (do
          let b ← Ecbs.add bX Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          Ecbs.move_band b Ecbs.across Ecbs.bottom) = .ok b') :
    (do
        let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
        let b ← Ecbs.clear b Ecbs.gap
        let b ← Ecbs.settle b
        let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
        let b ← Ecbs.bench_white0 b
        let b ← Ecbs.bench_add b Ecbs.across false
        let b ← Ecbs.bench_add b Ecbs.bottom true
        let b ← Ecbs.clear b Ecbs.bottom
        let b ← Ecbs.settle b
        let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
        let b ← Ecbs.mirror b Ecbs.up
        let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
        let b ← Ecbs.clear b Ecbs.gap
        let b ← Ecbs.settle b
        let b ← Ecbs.move_band b Ecbs.across Ecbs.bottom
        pure b) = .ok b' := by
  have hassoc :
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          let b ← Ecbs.bench_white0 b
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          let b ← Ecbs.settle b
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.move_band b Ecbs.across Ecbs.bottom
          pure b) =
      (do
          let b ←
            (do
              let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
              let b ← Ecbs.clear b Ecbs.gap
              let b ← Ecbs.settle b
              let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
              let b ← Ecbs.bench_white0 b
              let b ← Ecbs.bench_add b Ecbs.across false
              let b ← Ecbs.bench_add b Ecbs.bottom true
              let b ← Ecbs.clear b Ecbs.bottom
              Ecbs.settle b)
          let b ←
            (do
              let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
              let b ← Ecbs.mirror b Ecbs.up
              let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
              let b ← Ecbs.clear b Ecbs.gap
              let b ← Ecbs.settle b
              Ecbs.move_band b Ecbs.across Ecbs.bottom)
          pure b) := by
    simp only [except_pull]
  rw [hassoc, hpre, ok_bind, hpost, ok_bind, pure_eq_ok]

/-- The generated `chord_tail` on the across and the up is that do. -/
theorem chord_tail_across_up (b : Ecbs.Board) :
    Ecbs.chord_tail b Ecbs.across Ecbs.up =
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          let b ← Ecbs.bench_white0 b
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          let b ← Ecbs.settle b
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          let b ← Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.move_band b Ecbs.across Ecbs.bottom
          pure b) := by
  rfl

end EcbsLink2.Link2
