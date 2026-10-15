/-
  A live white or red cell with a nonempty run. Obtain the settled bottom,
  obtain the slide, then rewrite by `chord_do_join`. The emitted `chord_tail`
  is the spec point, and `walkStep` is that point.
  SPEC.md §3 R7 line 156.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordLay

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
