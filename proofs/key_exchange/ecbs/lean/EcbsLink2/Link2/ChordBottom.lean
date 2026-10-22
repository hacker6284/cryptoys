/-
  The bottom settle of the chord tail. Split from `ChordLay` so the strict
  and hole formula is not elaborated in the square file.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem ix {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

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
        bX.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeX ∧
        (∃ occ1 occ2, occ1 ≤ 7 ∧ occ2 ≤ 7 ∧
          strictX = raisedPeak (raisedPeak peakS occ1) occ2) ∧
        (∃ top1 top2, top1 ≤ bench ∧ top2 ≤ bench ∧
          holeX = raisedHole (raisedHole hole top1) top2)) ∧
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
  obtain ⟨peakW, strictW, holeW, hpkW, hstW, hhoW, hstR, hhoR, opsSz, hop0W⟩ := hpW
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
  · exact ⟨peakXN, strictW, holeW, hpkX, hstX.trans hstW, hhoX.trans hhoW, hstR, hhoR⟩
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

end EcbsLink2.Link2
