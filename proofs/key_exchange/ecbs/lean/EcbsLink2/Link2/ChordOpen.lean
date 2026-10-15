/-
  A live white or red cell with a nonempty run. Obtain the settled bottom,
  obtain the slide, then rewrite by `chord_do_join`. The emitted `chord_tail`
  is the spec point, and `walkStep` is that point.
  SPEC.md §3 R7 line 156.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLay
import EcbsLink2.Link2.InvertWalk

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The chord tail on the rise board. `bottom_lay`, then `point_from_bottom`,
    then `chord_do_join`. Home 0 is `chordX3` and home 1 is `chordY3`. -/
theorem chord_tail_point (b : Ecbs.Board) (inv rise accX accY run : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script) (hbound3 : m + 3 < script)
    (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hfitC6 : FitsLen (ctrl + 6)) (hfit4 : FitsLen (m + 4))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2))
    (hfops3 : FitsLen (cOps + 3))
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
    (hxLen : accX.length = n) (hyA : accY.length = n) (hrun : run.length = n)
    (htriX : allTritList accX) (htriY : allTritList accY) (htriR : allTritList run)
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
        2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hTailM :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
        3 * (bench - n) + 5 * n))
    (hTailS :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let slX := slGap slides inv rise n k bench + 2 * pegCount x3
      FitsLen (slX + 6 * n))
    (hfitP :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + 2 * n))
    (hfitMo :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n))
    (hfmP :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1)))
    (hfoldP :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
        3 * (bench - n)))
    (hfitSo :
      let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let slX := slGap slides inv rise n k bench + 2 * pegCount x3
      FitsLen (slX + 2 * n)) :
    let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let y3 := chordY3 n k bench slope (fieldSub n accX x3) accY
    ∃ b',
      Ecbs.chord_tail b Ecbs.across Ecbs.up = .ok b' ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed x3) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed y3) := by
  intro slope x3 y3
  obtain ⟨bX, hpre, hoffX, h2x, h0aF, h0tF, h5aF, h5tF, hflagN, hszH8, hszD8,
      hmN, hcN, hxN, htAll, hmvRaw, hslRaw, h2tF, h1home, h1held, opsSz, hop0F,
      peakXN, strictW, holeW, hpkX, hstX, hhoX⟩ :=
    bottom_lay b inv rise accX run w h r n k moves hole bench slides peak peakS
      cOps m ctrl mx script
      hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hfitC4 hfit3
      hops hop0 hfops hfops2 hbl hszH hszD hHF hArr hHS hYs h0a h0t h2t h2a
      hn0 hn hlenx hleny hxLen hrun htriX htriR hf hmoves hslides hpeak hpeakS
      hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk
      hsm hnsm hfitB hfold hfitClear hpegG hfitSM hfitSS hfmS hfoldS hfitW
      hfit1 hfitA hfitRun hpegX hfitMX hfitSX
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
  have hbig : FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
      3 * (bench - n) + 5 * n) := hTailM
  have hbigS : FitsLen (slX + 6 * n) := hTailS
  have hfitPx : FitsLen (mvX + 2 * n) := hfitP
  have hfitMox : FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n) := hfitMo
  have hfmPx : FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1)) := hfmP
  have hfoldPx : FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
      3 * (bench - n)) := hfoldP
  have hfitSox : FitsLen (slX + 2 * n) := hfitSo
  obtain ⟨_, b', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpost, hAc, hUp⟩ :=
    point_from_bottom bX accX accY x3 slope w h r n k bench mvX slX peakXN strictW holeW
      cOpsX mX ctrlX mxX script
      hszH8 hszD8 hflagN hoffX hmN hcN hxN hscriptX
      hbound3 hfit3 hfitC6 hfit4
      hopsX hop0X hfops3 hblX
      h0tX h0aX h1tX h1aX h2tX h2aX h5tX h5aX
      hnX hxLen hyA hx3len hslope hn0 hnb
      htriX htriY htri3 htriS
      hmvN hslN hpkN hstN hhoX
      hfitPx hf hspan hfi hfitMox hfitSox hfmPx
      hw0 hh0 hrR hrP hnE hkLe hgap hwX hhX hrX hkX
      hsm hnsm hfitB hfoldPx hbig hbigS
  refine ⟨b', ?_, hAc, hUp⟩
  rw [chord_tail_across_up]
  exact chord_do_join b bX b' hpre hpost

/-- The live cell step, once the chord add has returned the new point.
    `walkStep` is that same point. -/
theorem chordStep_live_spec (cells : List Nat) (i toN c : Nat)
    (b0 b bF bA : Ecbs.Board)
    (n k bench : Nat) (baseX baseY preX preY x3 y3 : List Nat)
    (hi : i ≤ toN) (hlen : cells.length = toN + 1)
    (hcAt : cells[i]'(by omega) = c) (hc0 : c ≠ 0) (hc2 : c ≤ 2)
    (hml : Ecbs.marker_lift b0 = .ok b)
    (hfrob : Ecbs.frobenius_affine b = .ok bF)
    (hadd : Ecbs.chord_add_demo bF (SudoRt.SEq.beq (Int.ofNat c) (2 : Int)) =
      .ok (true, bA))
    (hfiti : FitsLen (i + 1))
    (hwalk : walkStep n k bench (baseX, baseY) true (preX, preY) c =
      some (true, (x3, y3))) :
    chordStep (embed cells) (Int.ofNat toN) (Int.ofNat i, (b0, true)) =
      (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bA, true)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bA, true)))) ∧
      walkStep n k bench (baseX, baseY) true (preX, preY) c =
        some (true, (x3, y3)) := by
  exact ⟨chordStep_open cells i toN c b0 b bF bA hi hlen hcAt hc0 hc2 hml hfrob hadd hfiti,
    hwalk⟩

/-- Homes and counters on the board `invert_checked` returns, with the marker
    flag put back. The inverse itself is not a field: `open_checked` supplies it. -/
structure RiseRead (b bI : Ecbs.Board) (baseY accY accX run inv : List Nat)
    (n moves0 peak0 slides peakS hole m ctrl mx script bench cOps w h r k : Nat) where
  szH : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home.size = 8
  szD : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held.size = 8
  hn : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  hmoves : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_5moves =
    (moves0 : Int)
  hpeak : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4peak =
    (peak0 : Int)
  h6e : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[6]'(by
    rw [szD]; decide) = false
  h4t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[4]'(by
    rw [szD]; decide) = true
  h4a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[4]'(by
    rw [szH]; decide) = embed baseY
  h1t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[1]'(by
    rw [szD]; decide) = true
  h1a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[1]'(by
    rw [szH]; decide) = embed accY
  h0a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[0]'(by
    rw [szH]; decide) = embed accX
  h0t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[0]'(by
    rw [szD]; decide) = true
  h2a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[2]'(by
    rw [szH]; decide) = embed run
  h2t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[2]'(by
    rw [szD]; decide) = true
  h5a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[5]'(by
    rw [szH]; decide) = embed inv
  h5t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[5]'(by
    rw [szD]; decide) = true
  hoff : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_8bench_on = false
  hm : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_6marker = Int.ofNat m
  hc : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4ctrl =
    Int.ofNat ctrl
  hx : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
    Int.ofNat mx
  hscript : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_6script =
    Int.ofNat script
  hops : 0 < (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_3ops.size
  hop0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_3ops[0]'hops =
    (cOps : Int)
  hbl : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_8benchlen =
    Int.ofNat bench
  hsl : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_6slides =
    Int.ofNat slides
  hstrict : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
    (peakS : Int)
  hhole : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
    Int.ofNat hole
  hw : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hh : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  hr : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  hk : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k

/-- The nonempty chord add, once `invert_checked` has returned. Across, bottom,
    and gap are the homes the rise keeps. `chord_tail_point` runs on that board.
    `chord_add_point` obtains the return from `open_checked`. -/
theorem chord_add_point_of_inv (b : Ecbs.Board) (red : Bool) (bI : Ecbs.Board)
    (baseY accY accX run inv rise : List Nat)
    (w h r n k moves0 moves hole bench slides peak0 peakS cOps m ctrl mx script : Nat)
    (hinv : Ecbs.invert_checked { b with sudo_5Board_9marker_on := false } Ecbs.bottom = .ok bI)
    (hszH : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home.size = 8)
    (hszD : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held.size = 8)
    (hyB : baseY.length = n) (hyA : accY.length = n) (hpos : 0 < n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hn0b : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves0 : Int))
    (hpeak0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak0 : Int))
    (hfit0 : FitsLen (moves0 + 2 * n))
    (h6e : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[6]'(by
      rw [hszD]; decide) = false)
    (h4t : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[4]'(by
      rw [hszD]; decide) = true)
    (h4a : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[4]'(by
      rw [hszH]; decide) = embed baseY)
    (h1t0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[1]'(by
      rw [hszD]; decide) = true)
    (h1a0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[1]'(by
      rw [hszH]; decide) = embed accY)
    (h0a0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[0]'(by
      rw [hszH]; decide) = embed accX)
    (h0t0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[0]'(by
      rw [hszD]; decide) = true)
    (h2a0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[2]'(by
      rw [hszH]; decide) = embed run)
    (h2t0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[2]'(by
      rw [hszD]; decide) = true)
    (h5a0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4home[5]'(by
      rw [hszH]; decide) = embed inv)
    (h5t0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4held[5]'(by
      rw [hszD]; decide) = true)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_8bench_on = false)
    (hm0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_6marker = Int.ofNat m)
    (hc0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat ctrl)
    (hx0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx)
    (hscript0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_6script =
      Int.ofNat script)
    (hbound : m + 2 < script) (hbound3 : m + 3 < script)
    (hfitM : FitsLen (m + 1)) (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hfitC6 : FitsLen (ctrl + 6)) (hfit4 : FitsLen (m + 4))
    (hops0 : 0 < (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop00 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops0) =
      (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2)) (hfops3 : FitsLen (cOps + 3))
    (hbl0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_8benchlen =
      Int.ofNat bench)
    (hsum : moves = moves0 + pegCount baseY + pegCount accY)
    (hriseL : rise = fieldSub n (if red then mirrorTrits baseY else baseY) accY)
    (hxLen : accX.length = n) (hyLen : accY.length = n) (hrunL : run.length = n)
    (hinvL : inv.length = n) (hriseN : rise.length = n)
    (htriX : allTritList accX) (htriY : allTritList accY) (htriR : allTritList run)
    (htriI : allTritList inv) (htriRise : allTritList rise)
    (hf : FitsLen n)
    (hsl0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat slides)
    (hstrict0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      (peakS : Int))
    (hhole0 : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat hole)
    (hspan : 2 * (n - 1) < bench)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hwB : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhB : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrB : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkB : (restoreMarker bI b.sudo_5Board_9marker_on).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
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
    (hfitW : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench))
    (hfit1 : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + n))
    (hfitA : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
        pegCount accX + n))
    (hfitRun : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
        pegCount accX + pegCount run + pegCount run))
    (hpegX : FitsLen (2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hfitMX : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
        pegCount accX + pegCount run + pegCount run +
        2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hfitSX : FitsLen (slGap slides inv rise n k bench +
        2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)))
    (hTailM : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
        3 * (bench - n) + 5 * n))
    (hTailS : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let slX := slGap slides inv rise n k bench + 2 * pegCount x3
      FitsLen (slX + 6 * n))
    (hfitP : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + 2 * n))
    (hfitMo : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n))
    (hfmP : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1)))
    (hfoldP : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
        pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
      FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n)))
    (hfitSo : let slope := fieldMul n k bench rise inv
      let x3 := chordX3 n k bench slope accX run
      let slX := slGap slides inv rise n k bench + 2 * pegCount x3
      FitsLen (slX + 2 * n)) :
    ∃ b',
      chordAddTail b red = .ok (true, b') ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed (chordX3 n k bench
        (fieldMul n k bench rise inv) accX run)) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed (chordY3 n k bench
        (fieldMul n k bench rise inv) (fieldSub n accX (chordX3 n k bench
          (fieldMul n k bench rise inv) accX run)) accY)) := by
  obtain ⟨bR, hadd, h6a, h6t, h1aR, h1tR, _h4a, _h4t, hszDR, hszHR, _hnR, hmv, hflag,
      h0aK, h0tK, h2aK, h2tK, h5aK, h5tK, htR, hmR, hcR, hxR, hslR, hopR, honR, _hb, _hto,
      hhoR, hstR, pk, hpk⟩ :=
    chord_tail_after_inv b red bI baseY accY n moves0 peak0 hinv hszH hszD hyB hyA hpos
      htriB htriA hn0b hmoves0 hpeak0 hfit0 h6e h4t h4a h1t0 h1a0
  have h0a : bR.sudo_5Board_4home[0]'(by rw [hszHR]; decide) = embed accX :=
    (h0aK (by rw [hszHR]; decide)).trans h0a0
  have h0t : bR.sudo_5Board_4held[0]'(by rw [hszDR]; decide) = true :=
    (h0tK (by rw [hszDR]; decide)).trans h0t0
  have h2a : bR.sudo_5Board_4home[2]'(by rw [hszHR]; decide) = embed run :=
    (h2aK (by rw [hszHR]; decide)).trans h2a0
  have h2t : bR.sudo_5Board_4held[2]'(by rw [hszDR]; decide) = true :=
    (h2tK (by rw [hszDR]; decide)).trans h2t0
  have h5a : bR.sudo_5Board_4home[5]'(by rw [hszHR]; decide) = embed inv :=
    (h5aK (by rw [hszHR]; decide)).trans h5a0
  have h5t : bR.sudo_5Board_4held[5]'(by rw [hszDR]; decide) = true :=
    (h5tK (by rw [hszDR]; decide)).trans h5t0
  have h1a : bR.sudo_5Board_4home[1]'(by rw [hszHR]; decide) = embed accY :=
    h1aR (by rw [hszHR]; decide)
  have h1t : bR.sudo_5Board_4held[1]'(by rw [hszDR]; decide) = true :=
    h1tR (by rw [hszDR]; decide)
  have h6aR : bR.sudo_5Board_4home[6]'(by rw [hszHR]; decide) = embed rise := by
    simpa [hriseL] using h6a (by rw [hszHR]; decide)
  have h6tR : bR.sudo_5Board_4held[6]'(by rw [hszDR]; decide) = true :=
    h6t (by rw [hszDR]; decide)
  have hmvN : bR.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [hsum] using hmv
  have hflagT : bR.sudo_5Board_9marker_on = true := hflag.trans hmk
  have hoffR : bR.sudo_5Board_8bench_on = false := honR.trans hoff
  have hmN : bR.sudo_5Board_6marker = Int.ofNat m := hmR.trans hm0
  have hcN : bR.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := hcR.trans hc0
  have hxN : bR.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := hxR.trans hx0
  have hslN : bR.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := hslR.trans hsl0
  have hstN : bR.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := hstR.trans hstrict0
  have hhoN : bR.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := hhoR.trans hhole0
  have hpkN : bR.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) :=
    hpk.trans (ofNat_eq_natCast pk)
  have hnR : bR.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    conv => lhs; rw [htR]
    exact hn0b
  have hscriptR : bR.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    conv => lhs; rw [htR]
    exact hscript0
  have hblR : bR.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    conv => lhs; rw [htR]
    exact hbl0
  have hwR : bR.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    conv => lhs; rw [htR]
    exact hwB
  have hhR : bR.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    conv => lhs; rw [htR]
    exact hhB
  have hrR' : bR.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    conv => lhs; rw [htR]
    exact hrB
  have hkR : bR.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    conv => lhs; rw [htR]
    exact hkB
  have hopsR : 0 < bR.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [hopR] using hops0
  have hop0R : bR.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsR = (cOps : Int) := by
    simpa [hopR] using hop00
  obtain ⟨b', hct, hAc, hUp⟩ :=
    chord_tail_point bR inv rise accX accY run w h r n k moves hole bench slides pk peakS
      cOps m ctrl mx script
      hflagT hoffR hmN hcN hxN hscriptR hbound hbound3 hfitM hfitC hfit2 hfitC4 hfit3
      hfitC6 hfit4 hopsR hop0R hfops hfops2 hfops3 hblR hszHR hszDR
      h5t h5a h6tR h6aR h0a h0t h1a h1t h2t h2a
      hpos hnR hinvL hriseN hxLen hyLen hrunL htriX htriY htriR hf hmvN hslN hpkN hstN
      hspan htriI htriRise hfi hfm hhoN hw0 hh0 hrR hrP hnE hkLe hgap hwR hhR hrR' hkR
      hsm hnsm hfitB hfold hfitClear hpegG hfitSM hfitSS hfmS hfoldS hfitW hfit1 hfitA
      hfitRun hpegX hfitMX hfitSX hTailM hTailS hfitP hfitMo hfmP hfoldP hfitSo
  refine ⟨b', ?_, ?_, ?_⟩
  · rw [hadd, hct, ok_bind, pure_eq_ok]
  · intro h
    simpa [chordX3, fieldMul] using hAc h
  · intro h
    simpa [chordY3, chordX3, fieldMul, fieldSub] using hUp h

/-- Rooms `chord_tail_point` still asks for, once the counters are the naturals
    on the board `invert_checked` returned. -/
structure TailRoom (n k bench script : Nat)
    (moves0 moves hole slides peakS cOps m ctrl : Nat)
    (inv rise accX accY run : List Nat) : Prop where
  fit0 : FitsLen (moves0 + 2 * n)
  bound : m + 2 < script
  bound3 : m + 3 < script
  fitM : FitsLen (m + 1)
  fitC : FitsLen (ctrl + 2)
  fit2 : FitsLen (m + 2)
  fitC4 : FitsLen (ctrl + 4)
  fit3 : FitsLen (m + 3)
  fitC6 : FitsLen (ctrl + 6)
  fit4 : FitsLen (m + 4)
  fops : FitsLen (cOps + 1)
  fops2 : FitsLen (cOps + 2)
  fops3 : FitsLen (cOps + 3)
  fi : FitsLen (2 * (n - 1))
  fm : FitsLen (moves + n * (n + 1))
  fitB : FitsLen bench
  fold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))
  fitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv)
  pegG : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n))
  fitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
    2 * pegCount ((gapProduct n k bench inv rise).take n))
  fitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n))
  fmS : FitsLen (mvGap moves inv rise n k bench +
    pegCount (fieldMul n k bench rise inv) + n * (n + 1))
  foldS : FitsLen (mvGap moves inv rise n k bench +
    pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n))
  fitW : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench)
  fit1 : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + n)
  fitA : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + n)
  fitRun : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run)
  pegX : FitsLen (2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  fitMX : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  fitSX : FitsLen (slGap slides inv rise n k bench +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  tailM : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
      3 * (bench - n) + 5 * n)
  tailS : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let slX := slGap slides inv rise n k bench + 2 * pegCount x3
    FitsLen (slX + 6 * n)
  fitP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + 2 * n)
  fitMo : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n)
  fmP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1))
  foldP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n))
  fitSo : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let slX := slGap slides inv rise n k bench + 2 * pegCount x3
    FitsLen (slX + 2 * n)

/-- Moves the chord tail can add after the rise, when every home has length `n`.
    Three schoolbooks, three folds, and the settles in between. -/
def tailMoveCap (n bench : Nat) : Nat :=
  3 * (n * (n + 1)) + 9 * (bench - n) + 24 * n + 1

/-- Slides the chord tail can add: the gap settle, the bottom settle, and the
    closing move of the bottom into the across. -/
def tailSlideCap (n : Nat) : Nat :=
  10 * n

private theorem spend3 {a b c a' b' c' : Nat}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    a + b + c ≤ a' + b' + c' := by
  omega

private theorem fieldAdd_len (n : Nat) (xs ys : List Nat) :
    (fieldAdd n xs ys).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem chordX3_len (n k bench : Nat) (slope accX run : List Nat) :
    (chordX3 n k bench slope accX run).length = n := by
  unfold chordX3
  rw [fieldAdd_len]

private theorem school_fold_le (xs ys : List Nat) (n k bench : Nat) :
    foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
  have hlen : (school n xs ys (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hF := foldCharge_bound n (n - k)
    (school n xs ys (List.replicate bench 0) false)
  rw [hlen] at hF
  exact hF

private theorem mulNo_le (moves : Nat) (xs ys : List Nat) (n k bench : Nat) :
    mulMovesNo moves xs ys n k bench ≤
      moves + n * (n + 1) + 3 * (bench - n) := by
  have hdef : mulMovesNo moves xs ys n k bench =
      moves + schoolMoves xs ys n n +
        foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) := rfl
  rw [hdef]
  exact Nat.add_le_add (Nat.add_le_add_left (schoolMoves_bound xs ys n) moves)
    (school_fold_le xs ys n k bench)

private theorem mulYes_le (moves : Nat) (xs ys : List Nat) (n k bench : Nat)
    (hpeg : pegCount ys ≤ n) :
    mulMoves moves xs ys n k bench ≤
      moves + n + n * (n + 1) + 3 * (bench - n) := by
  have hdef : mulMoves moves xs ys n k bench =
      moves + pegCount ys + schoolMoves xs ys n n +
        foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) := rfl
  rw [hdef]
  have hsch := schoolMoves_bound xs ys n
  have hfold := school_fold_le xs ys n k bench
  omega

private theorem le_move (moves0 moves extra n bench : Nat)
    (hmov : moves ≤ moves0 + 2 * n)
    (hextra : 2 * n + extra ≤ tailMoveCap n bench) :
    moves + extra ≤ moves0 + tailMoveCap n bench := by
  omega

private theorem fitsFrom (moves0 moves n bench goal extra : Nat)
    (hBig : FitsLen (moves0 + tailMoveCap n bench))
    (hmov : moves ≤ moves0 + 2 * n)
    (hgoal : goal ≤ moves + extra)
    (hroom : 2 * n + extra ≤ tailMoveCap n bench) :
    FitsLen goal :=
  FitsLen.of_le hBig (Nat.le_trans hgoal (le_move moves0 moves extra n bench hmov hroom))

private theorem fitsSlide (slides n goal extra : Nat)
    (hBig : FitsLen (slides + tailSlideCap n))
    (hgoal : goal ≤ slides + extra)
    (hroom : extra ≤ tailSlideCap n) :
    FitsLen goal :=
  FitsLen.of_le hBig (Nat.le_trans hgoal (Nat.add_le_add_left hroom slides))

/-- Every settle `FitsLen` in `TailRoom`, from one move room, one slide room,
    and one room each for the marker, the control counter, and ops slot 0.
    A length-`n` home has at most `n` pegs. -/
theorem tailRoom_of (n k bench script moves0 moves hole slides peakS cOps m ctrl : Nat)
    (inv rise accX accY run : List Nat)
    (hmov : moves ≤ moves0 + 2 * n)
    (hinv : inv.length = n)
    (hx : accX.length = n) (hy : accY.length = n) (hrun : run.length = n)
    (hnb : n ≤ bench)
    (hBig : FitsLen (moves0 + tailMoveCap n bench))
    (hBigS : FitsLen (slides + tailSlideCap n))
    (hMark : m + 3 < script) (hMarkF : FitsLen (m + 4))
    (hCtrl : FitsLen (ctrl + 6)) (hOps : FitsLen (cOps + 3)) :
    TailRoom n k bench script moves0 moves hole slides peakS cOps m ctrl
      inv rise accX accY run := by
  have hpegI : pegCount inv ≤ n := by rw [← hinv]; exact pegCount_le inv
  have hpegX : pegCount accX ≤ n := by rw [← hx]; exact pegCount_le accX
  have hpegY : pegCount accY ≤ n := by rw [← hy]; exact pegCount_le accY
  have hpegRun : pegCount run ≤ n := by rw [← hrun]; exact pegCount_le run
  have hprod : pegCount ((gapProduct n k bench inv rise).take n) ≤ n :=
    pegCount_take_le (gapProduct n k bench inv rise) n
  have hlenS : (fieldMul n k bench rise inv).length = n :=
    fieldMul_length n k bench rise inv hnb
  have hpegS : pegCount (fieldMul n k bench rise inv) ≤ n := by
    have h := pegCount_le (fieldMul n k bench rise inv)
    rwa [hlenS] at h
  have hlenX3 : (chordX3 n k bench (fieldMul n k bench rise inv) accX run).length = n :=
    chordX3_len n k bench _ accX run
  have hpegX3 : pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) ≤ n := by
    have h := pegCount_le (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
    rwa [hlenX3] at h
  have hno := mulNo_le moves inv rise n k bench
  have hgap : mvGap moves inv rise n k bench ≤
      moves + n * (n + 1) + 3 * (bench - n) + 3 * n := by
    have hdef : mvGap moves inv rise n k bench =
        mulMovesNo moves inv rise n k bench + pegCount inv +
          2 * pegCount ((gapProduct n k bench inv rise).take n) := rfl
    rw [hdef]
    omega
  have hsq : mvSq (mvGap moves inv rise n k bench)
      (fieldMul n k bench rise inv) n k bench ≤
      moves + 2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n + 1 := by
    have hdef : mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench =
        mulMoves (mvGap moves inv rise n k bench)
          (fieldMul n k bench rise inv) (fieldMul n k bench rise inv) n k bench + 1 := rfl
    have hmul := mulYes_le (mvGap moves inv rise n k bench)
      (fieldMul n k bench rise inv) (fieldMul n k bench rise inv) n k bench hpegS
    rw [hdef]
    omega
  let mvX := mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
  have hmvX : mvX ≤ moves + 2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 9 * n + 1 := by
    have h := hsq
    omega
  let slX := slGap slides inv rise n k bench +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
  have hslX : slX ≤ slides + 4 * n := by
    have hdef : slGap slides inv rise n k bench =
        slides + 2 * pegCount ((gapProduct n k bench inv rise).take n) := rfl
    change slGap slides inv rise n k bench +
      2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) ≤ _
    rw [hdef]
    omega
  have htailM : mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
      pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n) + 5 * n ≤
      moves0 + tailMoveCap n bench := by
    have h := hmvX
    unfold tailMoveCap at *
    generalize n * (n + 1) = S at *
    generalize bench - n = D at *
    omega
  have htailS : slX + 6 * n ≤ slides + tailSlideCap n := by
    have h := hslX
    unfold tailSlideCap
    omega
  refine
    { fit0 := FitsLen.of_le hBig (
      by
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      bound := by omega
      bound3 := hMark
      fitM := FitsLen.of_le hMarkF (by omega)
      fitC := FitsLen.of_le hCtrl (by omega)
      fit2 := FitsLen.of_le hMarkF (by omega)
      fitC4 := FitsLen.of_le hCtrl (by omega)
      fit3 := FitsLen.of_le hMarkF (by omega)
      fitC6 := hCtrl
      fit4 := hMarkF
      fops := FitsLen.of_le hOps (by omega)
      fops2 := FitsLen.of_le hOps (by omega)
      fops3 := hOps
      fi := FitsLen.of_le hBig (
      by
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fm := fitsFrom moves0 moves n bench
        (moves + n * (n + 1))
        (n * (n + 1))
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitB := FitsLen.of_le hBig (
      by
        have hcancel := Nat.sub_add_cancel hnb
        unfold tailMoveCap
        generalize n * (n + 1) = S at *
        generalize bench - n = D at *
        omega)
      fold := fitsFrom moves0 moves n bench
        (moves + n * (n + 1) + 3 * (bench - n))
        (n * (n + 1) + 3 * (bench - n))
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitClear := fitsFrom moves0 moves n bench
        (mulMovesNo moves inv rise n k bench + pegCount inv)
        (n * (n + 1) + 3 * (bench - n) + n)
        hBig hmov (by have h := Nat.add_le_add hno hpegI; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      pegG := FitsLen.of_le hBig (
      by
        have h := Nat.mul_le_mul_left 2 hprod
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fitSM := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench)
        (n * (n + 1) + 3 * (bench - n) + 3 * n)
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSS := fitsSlide slides n (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)) (2 * n) hBigS
        (by
          have h := Nat.mul_le_mul_left 2 hprod
          omega)
        (by unfold tailSlideCap; omega)
      fmS := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench + pegCount (fieldMul n k bench rise inv) + n * (n + 1))
        (2 * (n * (n + 1)) + 3 * (bench - n) + 4 * n)
        hBig hmov (by have h := hgap; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      foldS := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench + pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n))
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n)
        hBig hmov (by have h := hgap; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitW := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n + 1)
        hBig hmov (
        by
          have h := hsq
          omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fit1 := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 5 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitA := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + pegCount accX + n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 6 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitRun := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + pegCount accX + pegCount run + pegCount run)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 7 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      pegX := FitsLen.of_le hBig (
      by
        have h := Nat.mul_le_mul_left 2 hpegX3
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fitMX := fitsFrom moves0 moves n bench
        mvX
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 9 * n + 1)
        hBig hmov (
        by
          have h := hmvX
          omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSX := fitsSlide slides n slX (4 * n) hBigS hslX (by unfold tailSlideCap; omega)
      tailM :=
      by
        simpa [mvX] using (FitsLen.of_le hBig htailM)
      tailS :=
      by
        simpa [slX] using (FitsLen.of_le hBigS htailS)
      fitP := fitsFrom moves0 moves n bench
        (mvX + 2 * n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 11 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitMo := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fmP := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n + n * (n + 1))
        (3 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      foldP := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n))
        (3 * (n * (n + 1)) + 3 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSo := by
        simpa [slX] using
          (fitsSlide slides n (slX + 2 * n) (6 * n) hBigS (by
            have h := hslX
            omega) (by unfold tailSlideCap; omega)) }


/-- The nonempty chord add. `open_checked` returns the inverse and `RiseCarry`
    reads the counters, so `RiseRead` is built here. One move room and one slide
    room, plus the marker, control, and ops rooms, discharge `TailRoom`. -/
theorem chord_add_point (b : Ecbs.Board) (red : Bool) (t : Spec.Tier)
    (baseY accY accX run inv rise : List Nat)
    (lay : OpenLay { b with sudo_5Board_9marker_on := false } t run)
    (bud : ClimbBudget) (hmatch : OpenMatch lay bud)
    (hOk : BoardOk t) (sat : TierSat t) (hR : 0 < tierR t) (hsh : TierShape t)
    (hacc : fieldInv t.n t.k t.benchlen run = some inv)
    (hside4 : baseY = lay.side4) (hside1 : accY = lay.side1) (hside0 : accX = lay.side0)
    (hf4 : lay.flag4 = true) (hf1 : lay.flag1 = true) (hf0 : lay.flag0 = true)
    (hyB : baseY.length = t.n) (hyA : accY.length = t.n) (hpos : 0 < t.n)
    (htriB : allTritList baseY) (htriA : allTritList accY)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hriseL : rise = fieldSub t.n (if red then mirrorTrits baseY else baseY) accY)
    (hxLen : accX.length = t.n) (hyLen : accY.length = t.n) (hrunL : run.length = t.n)
    (hinvL : inv.length = t.n) (hriseN : rise.length = t.n)
    (htriX : allTritList accX) (htriY : allTritList accY) (htriR : allTritList run)
    (htriI : allTritList inv) (htriRise : allTritList rise)
    (hf : FitsLen t.n)
    (hspan : 2 * (t.n - 1) < t.benchlen)
    (hw0 : 0 < t.w) (hh0 : 0 < t.h) (hrR : t.r < t.h) (hrP : 0 < t.r)
    (hnE : t.n = t.w * t.h - 1) (hkLe : t.k ≤ t.n) (hgap : t.n - t.k = t.w * t.r)
    (hsm : t.w ≤ 1000000 ∧ t.h ≤ 1000000 ∧ t.r ≤ 1000000 ∧ t.benchlen ≤ 1000001)
    (hnsm : t.n ≤ 1000000)
    (hChord : FitsLen (checkMoveCap bud + tailMoveCap bud.n bud.bench))
    (hChordS : FitsLen (checkSlideCap bud + tailSlideCap bud.n))
    (hMark : lay.mark + 3 < t.script) (hMarkF : FitsLen (lay.mark + 4))
    (hCtrl : FitsLen (checkCtrlCap bud + 6))
    (hOps : FitsLen (checkOpsCap bud + 3)) :
    ∃ (bI : Ecbs.Board) (moves0 peak0 slides peakS hole ctrl cOps : Nat),
      RiseRead b bI baseY accY accX run inv t.n moves0 peak0 slides peakS hole
        lay.mark ctrl lay.mx t.script t.benchlen cOps t.w t.h t.r t.k ∧
      ∃ b',
        chordAddTail b red = .ok (true, b') ∧
        (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = embed
          (chordX3 t.n t.k t.benchlen (fieldMul t.n t.k t.benchlen rise inv) accX run)) ∧
        (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = embed
          (chordY3 t.n t.k t.benchlen (fieldMul t.n t.k t.benchlen rise inv)
            (fieldSub t.n accX (chordX3 t.n t.k t.benchlen
              (fieldMul t.n t.k t.benchlen rise inv) accX run)) accY)) := by
  obtain ⟨bI, _h5, _h5D, hinv0, h5aI, h5tI, hnT, _hlenA, h2aI, h2tI, h0aI, h0tI,
      h1aI, h1tI, h4aI, h4tI, hcarry, hbnd, hwater⟩ :=
    open_checked { b with sudo_5Board_9marker_on := false } t run inv lay hOk sat hR hsh
      bud hmatch hacc
  have _hwater := hwater
  have hinv : Ecbs.invert_checked { b with sudo_5Board_9marker_on := false } Ecbs.bottom =
      .ok bI := by simpa [Ecbs.bottom] using hinv0
  let bF := restoreMarker bI b.sudo_5Board_9marker_on
  have hhomeEq : bF.sudo_5Board_4home = bI.sudo_5Board_4home := rfl
  have hheldEq : bF.sudo_5Board_4held = bI.sudo_5Board_4held := rfl
  have hszH : bF.sudo_5Board_4home.size = 8 := by simpa [bF, restoreMarker] using hcarry.szH
  have hszD : bF.sudo_5Board_4held.size = 8 := by simpa [bF, restoreMarker] using hcarry.szD
  let moves0 := hcarry.moves.choose
  have hmoves := hcarry.moves.choose_spec
  let peak0 := hcarry.peak.choose
  have hpeak := hcarry.peak.choose_spec
  let slides := hcarry.slides.choose
  have hsl := hcarry.slides.choose_spec
  let peakS := hcarry.peakS.choose
  have hstrict := hcarry.peakS.choose_spec
  let hole := hcarry.hole.choose
  have hhole := hcarry.hole.choose_spec
  let ctrl := hcarry.ctrl.choose
  have hctrl := hcarry.ctrl.choose_spec
  let cOps := hcarry.ops0.choose
  have hop0 := hcarry.ops0.choose_spec
  have h4t : bF.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true :=
    (cell_eq_of hheldEq (h4tI (by rw [← hheldEq, hszD]; decide))).trans hf4
  have h4a : bF.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY := by
    rw [hside4]
    exact cell_eq_of hhomeEq (h4aI (by rw [← hhomeEq, hszH]; decide))
  have h1t : bF.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true :=
    (cell_eq_of hheldEq (h1tI (by rw [← hheldEq, hszD]; decide))).trans hf1
  have h1a : bF.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed accY := by
    rw [hside1]
    exact cell_eq_of hhomeEq (h1aI (by rw [← hhomeEq, hszH]; decide))
  have h0a : bF.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed accX := by
    rw [hside0]
    exact cell_eq_of hhomeEq (h0aI (by rw [← hhomeEq, hszH]; decide))
  have h0t : bF.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true :=
    (cell_eq_of hheldEq (h0tI (by rw [← hheldEq, hszD]; decide))).trans hf0
  have h2a : bF.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed run :=
    cell_eq_of hhomeEq (h2aI (by rw [← hhomeEq, hszH]; decide))
  have h2t : bF.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true :=
    cell_eq_of hheldEq (h2tI (by rw [← hheldEq, hszD]; decide))
  have h5a : bF.sudo_5Board_4home[5]'(by rw [hszH]; decide) = embed inv :=
    cell_eq_of hhomeEq h5aI
  have h5t : bF.sudo_5Board_4held[5]'(by rw [hszD]; decide) = true :=
    cell_eq_of hheldEq h5tI
  have h6e : bF.sudo_5Board_4held[6]'(by rw [hszD]; decide) = false :=
    cell_eq_of hheldEq hcarry.held6
  have hr : RiseRead b bI baseY accY accX run inv t.n moves0 peak0 slides peakS hole
      lay.mark ctrl lay.mx t.script t.benchlen cOps t.w t.h t.r t.k := by
    refine
      { szH := hszH
        szD := hszD
        hn := by simpa [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast] using hnT
        hmoves := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hmoves
        hpeak := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hpeak
        h6e := h6e
        h4t := h4t
        h4a := h4a
        h1t := h1t
        h1a := h1a
        h0a := h0a
        h0t := h0t
        h2a := h2a
        h2t := h2t
        h5a := h5a
        h5t := h5t
        hoff := by simpa [bF, restoreMarker] using hcarry.benchOff
        hm := by simpa [bF, restoreMarker] using hcarry.marker
        hc := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hctrl
        hx := by simpa [bF, restoreMarker] using hcarry.mx
        hscript := by simp [bF, restoreMarker, hcarry.tier, embTier]
        hops := by simpa [bF, restoreMarker] using hcarry.opsGt
        hop0 := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hop0
        hbl := by simp [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast]
        hsl := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hsl
        hstrict := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hstrict
        hhole := by simpa [bF, restoreMarker, ofNat_eq_natCast] using hhole
        hw := by simp [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast]
        hh := by simp [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast]
        hr := by simp [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast]
        hk := by simp [bF, restoreMarker, hcarry.tier, embTier, ofNat_eq_natCast] }
  let moves := moves0 + pegCount baseY + pegCount accY
  obtain ⟨mvC, hmvC, hmvLe⟩ := hbnd.move
  have hmv0 : moves0 = mvC := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact hmoves.symm.trans hmvC
  have hmoveFit : FitsLen (moves0 + tailMoveCap t.n t.benchlen) := by
    apply FitsLen.of_le hChord
    rw [hmatch.n, hmatch.bench, hmv0]
    omega
  obtain ⟨slC, hslC, hslLe⟩ := hbnd.slide
  have hsl0 : slides = slC := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact hsl.symm.trans hslC
  have hslideFit : FitsLen (slides + tailSlideCap t.n) := by
    apply FitsLen.of_le hChordS
    rw [hmatch.n, hsl0]
    omega
  obtain ⟨cC, hcC, hcLe⟩ := hbnd.ctrl
  have hc0 : ctrl = cC := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact hctrl.symm.trans hcC
  have hctrlFit : FitsLen (ctrl + 6) := by
    apply FitsLen.of_le hCtrl
    rw [hc0]
    omega
  obtain ⟨_gtC, opC, hopC, hopLe⟩ := hbnd.ops
  have hopEq : cOps = opC := by
    apply Int.ofNat.inj
    rw [ofNat_eq_natCast, ofNat_eq_natCast]
    exact hop0.symm.trans (idx_irrel.trans hopC)
  have hopsFit : FitsLen (cOps + 3) := by
    apply FitsLen.of_le hOps
    rw [hopEq]
    omega
  have hpegB : pegCount baseY ≤ t.n := by rw [← hyB]; exact pegCount_le baseY
  have hpegA : pegCount accY ≤ t.n := by rw [← hyA]; exact pegCount_le accY
  have hmovRise : moves ≤ moves0 + 2 * t.n := by
    rw [show moves = moves0 + pegCount baseY + pegCount accY from rfl]
    omega
  have hnb : t.n ≤ t.benchlen := by
    have hsp := hspan
    omega
  have room : TailRoom t.n t.k t.benchlen t.script moves0 moves hole slides peakS cOps
      lay.mark ctrl inv rise accX accY run :=
    tailRoom_of t.n t.k t.benchlen t.script moves0 moves hole slides peakS cOps
      lay.mark ctrl inv rise accX accY run hmovRise hinvL hxLen hyLen hrunL hnb
      hmoveFit hslideFit hMark hMarkF hctrlFit hopsFit
  refine ⟨bI, moves0, peak0, slides, peakS, hole, ctrl, cOps, hr, ?_⟩
  exact chord_add_point_of_inv b red bI baseY accY accX run inv rise
    t.w t.h t.r t.n t.k moves0 moves hole t.benchlen slides peak0 peakS cOps
    lay.mark ctrl lay.mx t.script
    hinv hszH hszD hyB hyA hpos htriB htriA hr.hn hr.hmoves hr.hpeak room.fit0
    h6e h4t h4a h1t h1a h0a h0t h2a h2t h5a h5t
    hmk hr.hoff hr.hm hr.hc hr.hx hr.hscript
    room.bound room.bound3 room.fitM room.fitC room.fit2 room.fitC4 room.fit3
    room.fitC6 room.fit4
    hr.hops hr.hop0 room.fops room.fops2 room.fops3 hr.hbl
    rfl hriseL hxLen hyLen hrunL hinvL hriseN
    htriX htriY htriR htriI htriRise hf
    hr.hsl hr.hstrict hr.hhole
    hspan room.fi room.fm hw0 hh0 hrR hrP hnE hkLe hgap
    hr.hw hr.hh hr.hr hr.hk
    hsm hnsm room.fitB room.fold room.fitClear room.pegG room.fitSM room.fitSS
    room.fmS room.foldS room.fitW room.fit1 room.fitA room.fitRun room.pegX
    room.fitMX room.fitSX room.tailM room.tailS room.fitP room.fitMo room.fmP
    room.foldP room.fitSo


/-- `chordAddTail` after the inverse is `chord_tail` on the rise board.
    A tail that returns `b'` is the pair `(true, b')`. -/
theorem chord_add_from_tail (b bR b' : Ecbs.Board) (red : Bool)
    (hadd :
      chordAddTail b red =
        (do
          let b ← Ecbs.chord_tail bR Ecbs.across Ecbs.up
          pure (true, b)))
    (htail : Ecbs.chord_tail bR Ecbs.across Ecbs.up = .ok b') :
    chordAddTail b red = .ok (true, b') := by
  rw [hadd, htail, ok_bind, pure_eq_ok]

end EcbsLink2.Link2
