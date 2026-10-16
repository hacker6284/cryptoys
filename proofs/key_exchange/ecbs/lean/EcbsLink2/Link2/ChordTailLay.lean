/-
  The bottom half of the chord tail: `bottom_lay` and the counters the slide
  reads off that board. Split from `chord_tail_point` so the two obtains are
  not elaborated in one process.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

structure TailBottom (b : Ecbs.Board) (inv rise accX accY run : List Nat)
    (w h r n k moves hole bench slides cOps m ctrl mx script : Nat) where
  bX : Ecbs.Board
  slope : List Nat
  x3 : List Nat
  mvX : Nat
  slX : Nat
  peakXN : Nat
  strictW : Nat
  holeW : Nat
  cOpsX : Nat
  mX : Nat
  ctrlX : Nat
  mxX : Nat
  hpre :
    (do
        let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
        let b ← Ecbs.clear b Ecbs.gap
        let b ← Ecbs.settle b
        let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
        let b ← Ecbs.bench_white0 b
        let b ← Ecbs.bench_add b Ecbs.across false
        let b ← Ecbs.bench_add b Ecbs.bottom true
        let b ← Ecbs.clear b Ecbs.bottom
        Ecbs.settle b) = .ok bX
  hoffX : bX.sudo_5Board_8bench_on = false
  hflagN : bX.sudo_5Board_9marker_on = true
  hszH8 : bX.sudo_5Board_4home.size = 8
  hszD8 : bX.sudo_5Board_4held.size = 8
  hmN : bX.sudo_5Board_6marker = Int.ofNat mX
  hcN : bX.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrlX
  hxN : bX.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mxX
  hscriptX : bX.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script
  hmvN : bX.sudo_5Board_4cost.sudo_5Costs_5moves = (mvX : Int)
  hslN : bX.sudo_5Board_4cost.sudo_5Costs_6slides = (slX : Int)
  hpkN : bX.sudo_5Board_4cost.sudo_5Costs_4peak = (peakXN : Int)
  hstN : bX.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (strictW : Int)
  hhoX : bX.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeW
  hopsX : 0 < bX.sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop0X : bX.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsX = ((cOpsX : Nat) : Int)
  hblX : bX.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench
  hnX : bX.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  hwX : bX.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hhX : bX.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  hrX : bX.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  hkX : bX.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k
  h0aX : bX.sudo_5Board_4home[0]'(by rw [hszH8]; decide) = embed accX
  h0tX : bX.sudo_5Board_4held[0]'(by rw [hszD8]; decide) = true
  h1aX : bX.sudo_5Board_4home[1]'(by rw [hszH8]; decide) = embed accY
  h1tX : bX.sudo_5Board_4held[1]'(by rw [hszD8]; decide) = true
  h2aX : bX.sudo_5Board_4home[2]'(by rw [hszH8]; decide) = embed x3
  h2tX : bX.sudo_5Board_4held[2]'(by rw [hszD8]; decide) = true
  h5aX : bX.sudo_5Board_4home[5]'(by rw [hszH8]; decide) = embed slope
  h5tX : bX.sudo_5Board_4held[5]'(by rw [hszD8]; decide) = true
  hnb : n ≤ bench
  htriS : allTritList slope
  htri3 : allTritList x3
  hslope : slope.length = n
  hx3len : x3.length = n
  hhiX : bX.sudo_5Board_4cost.sudo_5Costs_15control_highest =
    b.sudo_5Board_4cost.sudo_5Costs_15control_highest
  hrowX : bX.sudo_5Board_3row = b.sudo_5Board_3row
  hstayB : TailStay b bX
  h6X : ∀ h : 6 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[6]'h = false
  hopX : ∀ j, j ≠ 0 → ∀ (hj : j < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
      (hj' : j < bX.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      bX.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj' =
        b.sudo_5Board_4cost.sudo_5Costs_3ops[j]'hj
  /-- The counters are the formulas `point_from_bottom` and the move bound
      simplify. A projection out of this structure is not that formula. -/
  slopeEq : slope = fieldMul n k bench rise inv
  x3Eq : x3 = chordX3 n k bench slope accX run
  mvEq : mvX = mvSq (mvGap moves inv rise n k bench) slope n k bench +
    pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
  slEq : slX = slGap slides inv rise n k bench + 2 * pegCount x3
  mEq : mX = m + 2
  ctrlEq : ctrlX = ctrl + 4
  mxEq : mxX = max (max mx (m + 2)) (m + 3)
  cOpsEq : cOpsX = cOps + 2

/-- `bottom_lay` plus the counters `point_from_bottom` reads. -/
theorem tail_bottom (b : Ecbs.Board) (inv rise accX accY run : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script)
    (hfitM : FitsLen (m + 1))
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
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
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
    Nonempty (TailBottom b inv rise accX accY run w h r n k moves hole bench slides cOps m
      ctrl mx script) := by

  let slope := fieldMul n k bench rise inv
  let x3 := chordX3 n k bench slope accX run
  obtain ⟨bX, hpre, hoffX, h2x, h0aF, h0tF, h5aF, h5tF, hflagN, hszH8, hszD8,
      hmN, hcN, hxN, htAll, hmvRaw, hslRaw, h2tF, h1home, h1held, opsSz, hop0F,
      htail⟩ :=
    bottom_lay b inv rise accX run w h r n k moves hole bench slides peak peakS
      cOps m ctrl mx script
      hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hfitC4 hfit3
      hops hop0 hfops hfops2 hbl hszH hszD hHF hArr hHS hYs h0a h0t h2t h2a
      hn0 hn hlenx hleny hxLen hrun htriX htriR hf hmoves hslides hpeak hpeakS
      hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk
      hsm hnsm hfitB hfold hfitClear hpegG hfitSM hfitSS hfmS hfoldS hfitW
      hfit1 hfitA hfitRun hpegX hfitMX hfitSX
  obtain ⟨⟨peakXN, strictW, holeW, hpkX, hstX, hhoX⟩, hhiX, hrowX, hstayB, h6X, hopX⟩ := htail
  have _hbottomHigh := hhiX
  let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
    pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
  let slX := slGap slides inv rise n k bench + 2 * pegCount x3
  let mX := m + 2
  let ctrlX := ctrl + 4
  let mxX := max (max mx (m + 2)) (m + 3)
  let cOpsX := cOps + 2
  have hmvN : bX.sudo_5Board_4cost.sudo_5Costs_5moves = (mvX : Int) := by
    rw [hmvRaw, ofNat_eq_natCast]
  have hslN : bX.sudo_5Board_4cost.sudo_5Costs_6slides = (slX : Int) := by
    rw [hslRaw, ofNat_eq_natCast]
  have hpkN : bX.sudo_5Board_4cost.sudo_5Costs_4peak = (peakXN : Int) := by
    rw [hpkX, ofNat_eq_natCast]
  have hstN : bX.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (strictW : Int) := by
    rw [hstX, ofNat_eq_natCast]
  have hnX : bX.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    conv => lhs; rw [htAll]
    exact hn
  have hscriptX : bX.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    conv => lhs; rw [htAll]
    exact hscript
  have hblX : bX.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    conv => lhs; rw [htAll]
    exact hbl
  have hwX : bX.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    conv => lhs; rw [htAll]
    exact hw
  have hhX : bX.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    conv => lhs; rw [htAll]
    exact hh
  have hrX : bX.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    conv => lhs; rw [htAll]
    exact hr
  have hkX : bX.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    conv => lhs; rw [htAll]
    exact hk
  have hopsX : 0 < bX.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [opsSz]; exact hops
  have hop0X : bX.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsX = ((cOpsX : Nat) : Int) :=
    (hop0F hopsX).trans (ofNat_eq_natCast (cOps + 2))
  have h0HX : 0 < bX.sudo_5Board_4home.size := by rw [hszH8]; decide
  have h1HX : 1 < bX.sudo_5Board_4home.size := by rw [hszH8]; decide
  have h2HX : 2 < bX.sudo_5Board_4home.size := by rw [hszH8]; decide
  have h5HX : 5 < bX.sudo_5Board_4home.size := by rw [hszH8]; decide
  have h0DX : 0 < bX.sudo_5Board_4held.size := by rw [hszD8]; decide
  have h1DX : 1 < bX.sudo_5Board_4held.size := by rw [hszD8]; decide
  have h2DX : 2 < bX.sudo_5Board_4held.size := by rw [hszD8]; decide
  have h5DX : 5 < bX.sudo_5Board_4held.size := by rw [hszD8]; decide
  have h0aX : bX.sudo_5Board_4home[0]'h0HX = embed accX := h0aF h0HX
  have h0tX : bX.sudo_5Board_4held[0]'h0DX = true := h0tF h0DX
  have h1aX : bX.sudo_5Board_4home[1]'h1HX = embed accY := (h1home h1HX).trans h1a
  have h1tX : bX.sudo_5Board_4held[1]'h1DX = true := (h1held h1DX).trans h1t
  have h2aX : bX.sudo_5Board_4home[2]'h2HX = embed x3 := h2x h2HX
  have h2tX : bX.sudo_5Board_4held[2]'h2DX = true := h2tF h2DX
  have h5aX : bX.sudo_5Board_4home[5]'h5HX = embed slope := h5aF h5HX
  have h5tX : bX.sudo_5Board_4held[5]'h5DX = true := h5tF h5DX
  have hnb : n ≤ bench := by omega
  have htriS : allTritList slope := fieldMul_span_trits n k bench rise inv hspan hnb
  have htri3 : allTritList x3 := by
    simp only [x3, chordX3]
    exact fieldAdd_span_trits _ _ _
  have hslope : slope.length = n := by
    simpa [slope] using fieldMul_length n k bench rise inv hnb
  have hx3len : x3.length = n := by
    simp [x3, chordX3, fieldAdd, List.length_map, List.length_range]
  have slopeEq : slope = fieldMul n k bench rise inv := rfl
  have x3Eq : x3 = chordX3 n k bench slope accX run := rfl
  have mvEq : mvX = mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3 := rfl
  have slEq : slX = slGap slides inv rise n k bench + 2 * pegCount x3 := rfl
  have mEq : mX = m + 2 := rfl
  have ctrlEq : ctrlX = ctrl + 4 := rfl
  have mxEq : mxX = max (max mx (m + 2)) (m + 3) := rfl
  have cOpsEq : cOpsX = cOps + 2 := rfl

  refine Nonempty.intro ?_
  exact
    { bX := bX
      slope := slope
      x3 := x3
      mvX := mvX
      slX := slX
      peakXN := peakXN
      strictW := strictW
      holeW := holeW
      cOpsX := cOpsX
      mX := mX
      ctrlX := ctrlX
      mxX := mxX
      hpre := hpre
      hoffX := hoffX
      hflagN := hflagN
      hszH8 := hszH8
      hszD8 := hszD8
      hmN := hmN
      hcN := hcN
      hxN := hxN
      hscriptX := hscriptX
      hmvN := hmvN
      hslN := hslN
      hpkN := hpkN
      hstN := hstN
      hhoX := hhoX
      hopsX := hopsX
      hop0X := hop0X
      hblX := hblX
      hnX := hnX
      hwX := hwX
      hhX := hhX
      hrX := hrX
      hkX := hkX
      h0aX := h0aX
      h0tX := h0tX
      h1aX := h1aX
      h1tX := h1tX
      h2aX := h2aX
      h2tX := h2tX
      h5aX := h5aX
      h5tX := h5tX
      hnb := hnb
      htriS := htriS
      htri3 := htri3
      hslope := hslope
      hx3len := hx3len
      hhiX := hhiX
      hrowX := hrowX
      hstayB := hstayB
      h6X := h6X
      hopX := hopX
      slopeEq := slopeEq
      x3Eq := x3Eq
      mvEq := mvEq
      slEq := slEq
      mEq := mEq
      ctrlEq := ctrlEq
      mxEq := mxEq
      cOpsEq := cOpsEq }

end EcbsLink2.Link2
