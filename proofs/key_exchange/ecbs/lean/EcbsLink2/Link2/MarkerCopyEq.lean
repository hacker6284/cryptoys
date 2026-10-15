/-
  `Ecbs.mul` with `copy_second = true`, `onto = false`, and `mirror = false` does
  not read the marker except in `log_op`. With the marker on, the multiply is
  the marker-off multiply of the board `marker_step` leaves, with the flag put
  back. The square in the chord tail is that multiply of the gap by itself.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Marker on and already seated, bench off. Copying the second home, the
    schoolbook is `school_loop_refines` and the lane fold is `mulAfter_flag`. -/
theorem mul_copy_up_eq (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitPtrl : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hSpH : 6 < b.sudo_5Board_4held.size) (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneS : second ≠ 6) (hneF : first ≠ 6)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitP : FitsLen (moves + pegCount ys))
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
    (hfold : FitsLen (moves + pegCount ys + n * (n + 1) + 3 * (bench - n))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false false =
      (do
        let r ← Ecbs.mul (markerUpFeed b m ctrl mx) ((dst : Nat) : Int)
          ((first : Nat) : Int) ((second : Nat) : Int) true false false
        pure { r with sudo_5Board_9marker_on := true }) := by
  let bFeed := bumpOp (markerUpFeed b m ctrl mx) 0 cOps (by simpa [markerUpFeed] using hops)
  let strip := embed (List.replicate bench 0)
  have hH : 6 < (mulAimed (copyUpBoard b m ctrl mx cOps hops) ((dst : Nat) : Int)
      strip).sudo_5Board_4home.size := by
    simpa [copyUpBoard, mulAimed, strip] using hSpHome
  have hD : 6 < (mulAimed (copyUpBoard b m ctrl mx cOps hops) ((dst : Nat) : Int)
      strip).sudo_5Board_4held.size := by
    simpa [copyUpBoard, mulAimed, strip] using hSpH
  have hOn := mul_copy_up_after b dst first second xs ys n moves bench peak peakS cOps
      m ctrl mx script hmk hoff hm hc hx hscript hbound hfitM hfitPtrl hfit2 hops hop0 hfops
      hbl hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneS hneF hn0 hn
      hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH hD
  have hGo := mul_copy_tail (copyUpBoard b m ctrl mx cOps hops) dst first second xs ys
      n moves bench peak peakS
      (by simp [copyUpBoard, markerUpFeed, bumpOp, hoff])
      (by simp [copyUpBoard, markerUpFeed, bumpOp, hbl])
      hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7
      hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH hD
  rw [hOn, ← hGo]
  have hon : copyUpBoard b m ctrl mx cOps hops = markerOn bFeed := by
    simp [copyUpBoard, markerOn, bFeed]
  rw [hon]
  have hflag := mul_copy_flag bFeed dst first second xs ys w h r n k moves hole bench peak peakS
      (by simp [bFeed, bumpOp, markerUpFeed]) hoff hbl hF hHome hHF hArr hS hHomeS hHS hYs
      hSpH hSpHome hSpE h7 hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan
      hxsT hfi hfm hfitP hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm
      hfitB hfold
  rw [hflag]
  have hH0 : 6 < (mulAimed bFeed ((dst : Nat) : Int) strip).sudo_5Board_4home.size := by
    simpa [bFeed, mulAimed, strip, bumpOp, markerUpFeed] using hSpHome
  have hD0 : 6 < (mulAimed bFeed ((dst : Nat) : Int) strip).sudo_5Board_4held.size := by
    simpa [bFeed, mulAimed, strip, bumpOp, markerUpFeed] using hSpH
  have hOff := mul_copy_off_after (markerUpFeed b m ctrl mx) dst first second xs ys
      n moves bench peak peakS cOps (by simp [markerUpFeed]) hoff
      (by simpa [markerUpFeed] using hops) (by simpa [markerUpFeed] using hop0) hfops
      hbl hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneS hneF hn0 hn
      hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH0 hD0
  have hGo0 := mul_copy_tail bFeed dst first second xs ys n moves bench peak peakS
      (by simp [bFeed, bumpOp, markerUpFeed, hoff])
      (by simp [bFeed, bumpOp, markerUpFeed, hbl])
      hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7
      hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH0 hD0
  have hlink : mulCopyGo bFeed ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int) =
      Ecbs.mul (markerUpFeed b m ctrl mx) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true false false := by
    rw [hGo0, ← hOff]
  rw [hlink]

/-- Marker on and lifted (`marker < 0`), bench off. Same copy multiply, on the
    board that seats the marker. -/
theorem mul_copy_down_eq (b : Ecbs.Board) (dst first second : Nat) (xs ys : List Nat)
    (w h r n k moves hole bench peak peakS cOps ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitD : FitsLen (ctrl + 1))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size) (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size) (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hSpH : 6 < b.sudo_5Board_4held.size) (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneS : second ≠ 6) (hneF : first ≠ 6)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1)))
    (hfitP : FitsLen (moves + pegCount ys))
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
    (hfold : FitsLen (moves + pegCount ys + n * (n + 1) + 3 * (bench - n))) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false false =
      (do
        let r ← Ecbs.mul (markerDownFeed b ctrl mx) ((dst : Nat) : Int)
          ((first : Nat) : Int) ((second : Nat) : Int) true false false
        pure { r with sudo_5Board_9marker_on := true }) := by
  let bFeed := bumpOp (markerDownFeed b ctrl mx) 0 cOps (by simpa [markerDownFeed] using hops)
  let strip := embed (List.replicate bench 0)
  have hH : 6 < (mulAimed (copyDownBoard b ctrl mx cOps hops) ((dst : Nat) : Int)
      strip).sudo_5Board_4home.size := by
    simpa [copyDownBoard, mulAimed, strip] using hSpHome
  have hD : 6 < (mulAimed (copyDownBoard b ctrl mx cOps hops) ((dst : Nat) : Int)
      strip).sudo_5Board_4held.size := by
    simpa [copyDownBoard, mulAimed, strip] using hSpH
  have hOn := mul_copy_down_after b dst first second xs ys n moves bench peak peakS cOps
      ctrl mx script hmk hoff hm hc hx hscript hpos hfitD hops hop0 hfops
      hbl hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneS hneF hn0 hn
      hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH hD
  have hGo := mul_copy_tail (copyDownBoard b ctrl mx cOps hops) dst first second xs ys
      n moves bench peak peakS
      (by simp [copyDownBoard, markerDownFeed, bumpOp, hoff])
      (by simp [copyDownBoard, markerDownFeed, bumpOp, hbl])
      hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7
      hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH hD
  rw [hOn, ← hGo]
  have hon : copyDownBoard b ctrl mx cOps hops = markerOn bFeed := by
    simp [copyDownBoard, markerOn, bFeed]
  rw [hon]
  have hflag := mul_copy_flag bFeed dst first second xs ys w h r n k moves hole bench peak peakS
      (by simp [bFeed, bumpOp, markerDownFeed]) hoff hbl hF hHome hHF hArr hS hHomeS hHS hYs
      hSpH hSpHome hSpE h7 hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan
      hxsT hfi hfm hfitP hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm
      hfitB hfold
  rw [hflag]
  have hH0 : 6 < (mulAimed bFeed ((dst : Nat) : Int) strip).sudo_5Board_4home.size := by
    simpa [bFeed, mulAimed, strip, bumpOp, markerDownFeed] using hSpHome
  have hD0 : 6 < (mulAimed bFeed ((dst : Nat) : Int) strip).sudo_5Board_4held.size := by
    simpa [bFeed, mulAimed, strip, bumpOp, markerDownFeed] using hSpH
  have hOff := mul_copy_off_after (markerDownFeed b ctrl mx) dst first second xs ys
      n moves bench peak peakS cOps (by simp [markerDownFeed]) hoff
      (by simpa [markerDownFeed] using hops) (by simpa [markerDownFeed] using hop0) hfops
      hbl hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneS hneF hn0 hn
      hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH0 hD0
  have hGo0 := mul_copy_tail bFeed dst first second xs ys n moves bench peak peakS
      (by simp [bFeed, bumpOp, markerDownFeed, hoff])
      (by simp [bFeed, bumpOp, markerDownFeed, hbl])
      hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7
      hneS hneF hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm hfitP hH0 hD0
  have hlink : mulCopyGo bFeed ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int) =
      Ecbs.mul (markerDownFeed b ctrl mx) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true false false := by
    rw [hGo0, ← hOff]
  rw [hlink]

/-- The square: `mul` of the gap by a copy of itself into the bottom, marker
    seated. The bench prefix is `fieldMul` of that slope by itself. SPEC.md §3
    R7 line 156, the slope-squared step of the chord. -/
theorem chord_square (b : Ecbs.Board) (slope : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitPtrl : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h5 : 5 < b.sudo_5Board_4held.size) (h5h : 5 < b.sudo_5Board_4home.size)
    (h5t : b.sudo_5Board_4held[5] = true)
    (h5a : b.sudo_5Board_4home[5] = embed slope)
    (h6 : 6 < b.sudo_5Board_4held.size) (h6h : 6 < b.sudo_5Board_4home.size)
    (h6e : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : slope.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (htri : allTritList slope)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount slope + n * (n + 1)))
    (hfitP : FitsLen (moves + pegCount slope))
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
    (hfold : FitsLen (moves + pegCount slope + n * (n + 1) + 3 * (bench - n))) :
    ∃ b', Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false = .ok b' ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = Ecbs.bottom ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)) ∧
      (laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)).take n =
        fieldMul n k bench slope slope ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mulMoves moves slope slope n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      (∀ h : 5 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[5] = embed slope) := by
  have hup := mul_copy_up_eq b 2 5 5 slope slope w h r n k moves hole bench peak peakS cOps
    m ctrl mx script hmk hoff hm hc hx hscript hbound hfitM hfitPtrl hfit2 hops hop0 hfops
    hbl h5 h5h h5t h5a h5 h5h h5t h5a h6 h6h h6e h7 (by decide) (by decide) hn0 hn hlen hlen
    hf hmoves hpeak hpeakS hspan htri hfi hfm hfitP hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh
    hr hk hsm hnsm hfitB hfold
  have href := mul_refines (markerUpFeed b m ctrl mx) 2 5 5 slope slope w h r n k moves hole
    bench peak peakS cOps rfl hoff hops hop0 hfops hbl h5 h5h h5t h5a h5 h5h h5t h5a h6 h6h
    h6e h7 (by decide) (by decide) hn0 hn hlen hlen hf hmoves hpeak hpeakS hfitP hspan htri
    hfi hfm ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩ hw hh hr hk hhole hsm hnsm hfitB hfold
  rcases href with ⟨b0, hb, hon, hto, hbench, htake, hhigh, hmv, _, hsl, ht, hsz, _, h5conj, _,
      _, _, _, _⟩
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, show Ecbs.gap = ((5 : Nat) : Int) from rfl]
  rw [hup, hb, ok_bind, pure_eq_ok]
  refine ⟨{ b0 with sudo_5Board_9marker_on := true }, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hon
  · simpa [Ecbs.bottom] using hto
  · exact hbench
  · exact htake
  · exact hhigh
  · exact hmv
  · simpa [markerUpFeed] using hsl
  · simpa [markerUpFeed] using ht
  · intro h
    have h5f : 5 < (markerUpFeed b m ctrl mx).sudo_5Board_4home.size := h5h
    rw [h5conj h5f h]
    simpa [markerUpFeed] using h5a

end EcbsLink2.Link2
