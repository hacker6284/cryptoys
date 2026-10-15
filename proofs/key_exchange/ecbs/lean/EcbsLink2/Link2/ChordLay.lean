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
      ∃ peakW strictW holeW,
        bW.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakW ∧
        bW.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictW ∧
        bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeW := by
  intro slope
  obtain ⟨bS, hdo, _hmkS, hoffS, hmS, hcS, hxS, htS, hmvS, hslS, hszHs, hszDs, h5a, h5t,
      h6e, hhome, hheld, hopsEq, peakG, strictG, holeG, hpk, hst, hho⟩ :=
    gap_settle_lay b inv rise w h r n k moves hole bench slides peak peakS cOps m ctrl mx
      script hmk hoff hm hc hx hscript (by omega) hfitM hfitC hfit2 hops hop0 hfops hbl
      hF hHome hHF hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hslides hpeak
      hpeakS hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm
      hnsm hfitB hfold hfitClear hpeg hfitSM hfitSS
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
      pk, st, ho, hpkW, hstW, hhoW⟩ :=
    square_white_lay bS slope w h r n k (mvGap moves inv rise n k bench) holeG bench
      peakG strictG (cOps + 1) (m + 1) (ctrl + 2) (max mx (m + 2)) script
      _hmkS hoffS hmS hcS hxS hscriptS hbound hfit2 hfitC4 hfit3 hopsSz hop0S hfops2 hblS
      h5dS h5hS (h5t h5dS) (h5a h5hS) h6dS h6hS (h6e h6dS) h7S hn0 hnS hlenS hf hmvS
      hpk hst hspan htriS hfi hfmS hfitP hho hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS
      hsm hnsm hfitB hfoldS hfitW
  refine ⟨bW, benchL, ?_, hbenchW, hpreW, hlenW, hzeroW, honW, htoW, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact ⟨pk, st, ho, hpkW, hstW, hhoW⟩

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
      bX.sudo_5Board_4held.size = 8 := by
  intro slope x3
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hF : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hHome : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have hS : 6 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hHomeS : 6 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  obtain ⟨bW, benchL, hsq, hbench, hpre, hlen, hzero, hon, hto, hszHW, hszDW, _hmkW, _hmW,
      _hcW, _hxW, htW, hmvW, hslW, hkeep, h5a, h5t, hheldK, peakW, _strictW, _holeW, _hpk, _hst, _hho⟩ :=
    square_kept b inv rise w h r n k moves hole bench slides peak peakS cOps m ctrl mx script
      hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hfitC4 hfit3 hops hop0 hfops hfops2 hbl
      hF hHome hHF hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hslides hpeak hpeakS
      hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB
      hfold hfitClear hpegG hfitSM hfitSS hfmS hfoldS hfitW
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
    rw [_hpk, ofNat_eq_natCast]
  have h0aW : bW.sudo_5Board_4home[0]'h0H = embed accX :=
    (hkeep 0 (by decide) (by decide) (by rw [hszH]; decide) h0H).trans h0a
  have h2tW : bW.sudo_5Board_4held[2]'h2D = true :=
    (hheldK 2 (by decide) (by rw [hszD]; decide) h2D).trans h2t
  have h2aW : bW.sudo_5Board_4home[2]'h2H = embed run :=
    (hkeep 2 (by decide) (by decide) (by rw [hszH]; decide) h2H).trans h2a
  obtain ⟨bX, hx3do, hoffX, h2x, _hmX, _htX, _hmvX, _hslX, hszX, hszDX, hflagX, _h2tX, hkeepX,
      hheldX, _hcX, _hxX, _hopX, _hstX, _hhoX, _peakX, _hpkX⟩ :=
    x3_settle_lay bW accX run benchL n k bench
      (mvSq (mvGap moves inv rise n k bench) slope n k bench)
      (slGap slides inv rise n k bench) peakW slope
      (by rw [hszHW]; exact hszH) (by rw [hszDW]; exact hszD) hon hto2 hbench
      h0aW h2tW h2aW
      (by rw [htW]; exact hn) hxLen hrun hn0 hlen hnb htriX htriR htriB hzero hpre hf hfitB
      hmvI hslI hpkI hfit1 hfitA hfitRun hpegX hfitMX hfitSX
  refine ⟨bX, ?_, hoffX, h2x, ?_, ?_, ?_, ?_, hflagX.trans _hmkW,
      hszX.trans (hszHW.trans hszH), hszDX.trans (hszDW.trans hszD)⟩
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
        3 * (bench - n))) :
    let dx := fieldSub n accX x3
    let yMir := mirrorTrits accY
    let y3 := chordY3 n k bench slope dx accY
    ∃ bM,
      (do
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          let b ← Ecbs.mirror b Ecbs.up
          Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.across false true false) =
        .ok (markerOn bM) ∧
      bM.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n slope dx (pref yMir bench n) false)) ∧
      (laneFold n (n - k) (school n slope dx (pref yMir bench n) false)).take n = y3 := by
  intro dx yMir y3
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h5H : 5 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h5D : 5 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  obtain ⟨bT, h0s, h1s, htDo, h0dx, h1m, hheldT, hszT, honT, _htoT, _hbenchT, hmT, hflagT,
      htT, hslT, hcT, hxT, hopT, hstT, hhoT, hpkT, hmvT, hkeepT⟩ :=
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
  obtain ⟨bM, hmul, hbenchM, hpreM, hlay⟩ :=
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
  let sch := school n slope dx (pref yMir bench n) false
  let benchL := laneFold n (n - k) sch
  have hpreY : benchL.take n = y3 := by
    have hswap : fieldAdd n yMir (fieldMul n k bench slope dx) =
        fieldAdd n (mirrorTrits accY) (fieldMul n k bench slope dx) := rfl
    rw [show benchL.take n = fieldAdd n yMir (fieldMul n k bench slope dx) from hpreM, hswap]
    simpa [y3, yMir, dx, chordY3, fieldSub] using
      (card_y3 n k bench slope dx accY)
  refine ⟨bM, ?_, hbenchM, hpreY⟩
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

end EcbsLink2.Link2
