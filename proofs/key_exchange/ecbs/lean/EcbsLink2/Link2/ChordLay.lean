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

end EcbsLink2.Link2
