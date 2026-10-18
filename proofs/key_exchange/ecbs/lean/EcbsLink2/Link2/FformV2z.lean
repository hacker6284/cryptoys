/-
  `v²` times the bottom, in its own module. The run square left `v²` on the
  bench, aimed at the spare. `cOps` is the cell that square left. On the rise
  chain that is the rise's cell plus 4, and this multiply leaves the rise's
  cell plus 5. The spare receives `v²`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformGapLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `v²` times `Z` on the board `gap_v2` leaves. `cOps = cRise + 4`. The cell
    this multiply leaves is `cRise + 5`. The gap stays held and still contains
    `u²Z`. The spare holds `v²`. The bottom ends empty. -/
theorem gap_v2z_on_v2 (b : Ecbs.Board) (sp bot gap : Nat)
    (v v2 z lane gHome u : List Nat)
    (m ctrl mx script cOps cRise n k w h r moves slides hole peak peakS bench : Nat)
    (hRead : cOps = cRise + 4)
    (hS : sp < b.sudo_5Board_4home.size)
    (hSD : sp < b.sudo_5Board_4held.size)
    (hBH : bot < b.sudo_5Board_4home.size)
    (hBD : bot < b.sudo_5Board_4held.size)
    (hHeldB : b.sudo_5Board_4held[bot] = true)
    (hArrB : b.sudo_5Board_4home[bot] = embed z)
    (hGH : gap < b.sudo_5Board_4home.size)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hHeldG : b.sudo_5Board_4held[gap] = true)
    (hArrG : b.sudo_5Board_4home[gap] = embed gHome)
    (hneGS : gap ≠ sp) (hneGB : gap ≠ bot)
    (hGHome : gHome = fieldMul n k bench z (fieldMul n k bench u u))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (sp : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[sp] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hne : sp ≠ bot)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (htake : lane.take n = v2) (hlenv : v2.length = n) (hlenz : z.length = n)
    (hvSq : v2 = fieldMul n k bench v v)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeakS7 : 7 ≤ peakS)
    (hspan : 2 * (n - 1) < bench)
    (hv2 : allTritList v2)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
        3 * (bench - n))) :
    ∃ (b' : Ecbs.Board) (lane' : List Nat),
      Ecbs.mul b ((bot : Nat) : Int) ((sp : Nat) : Int) ((bot : Nat) : Int)
          false false false = .ok b' ∧
      lane'.take n = fieldMul n k bench (fieldMul n k bench v v) z ∧
      (∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h = Int.ofNat (cRise + 5)) ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = ((bot : Nat) : Int) ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      (∀ h : gap < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[gap]'h =
          embed (fieldMul n k bench z (fieldMul n k bench u u))) ∧
      (∀ h : gap < b'.sudo_5Board_4held.size,
        b'.sudo_5Board_4held[gap]'h = true) ∧
      (∀ h : sp < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[sp]'h = embed (fieldMul n k bench v v)) ∧
      (∀ h : sp < b'.sudo_5Board_4held.size,
        b'.sudo_5Board_4held[sp]'h = true) ∧
      (∀ h : bot < b'.sudo_5Board_4held.size,
        b'.sudo_5Board_4held[bot]'h = false) ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat ((moves + 2 * pegCount (lane.take n)) + schoolMoves v2 z n n +
          foldCharge n (n - k) (school n v2 z (List.replicate bench 0) false)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n)) ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      (∀ j, j ≠ bot → j ≠ sp →
        ∀ hj : j < b.sudo_5Board_4home.size,
        ∀ hj' : j < b'.sudo_5Board_4home.size,
          b'.sudo_5Board_4home[j]'hj' = b.sudo_5Board_4home[j]'hj) ∧
      (∀ j, j ≠ bot → j ≠ sp →
        ∀ hj : j < b.sudo_5Board_4held.size,
        ∀ hj' : j < b'.sudo_5Board_4held.size,
          b'.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        Int.ofNat (if hole < topIdx (school n v2 z (List.replicate bench 0) false) then
          topIdx (school n v2 z (List.replicate bench 0) false) else hole) ∧
      0 < lane'.length ∧
      n ≤ lane'.length ∧
      FitsLen lane'.length ∧
      (∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i]'hi = 0) ∧
      0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  obtain ⟨b', lane', hok, hb, ht, hon', hto', hmk, hix, hctrl, hops,
      hhomeG, hheldG, hhomeS, hheldS, hemptyB, _hb2, _hmk2, htier, _hctrl2, hmx,
      hmv, hsl, hszD, hszH, hhome, hheld, hpk, hst, hhole, hposL', hnle', hfitL', hzero',
      hopsSz⟩ :=
    gap_v2z b sp bot gap v2 z lane gHome m ctrl mx script cOps n k w h r moves slides hole
      peak peakS bench hS hSD hBH hBD hHeldB hArrB hGH hGD hHeldG hArrG hneGS hneGB
      hmk hon hto hm hc hx hscript
      hbound hfitMk hfitC hfit2 hn hops hop0 hfops h7 hempty hbench hposL hnle hzero
      hf hfitL hmoves hslides hpeak hpeg hfitM hfitS hbl
      hne hn0 hnb htake hlenv hlenz
      hpeak7 hpeakS hpeakS7 hspan hv2 hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap
      hw hh hr hk hsm hnsm hfitB hfold
  have hc : cOps + 1 = cRise + 5 := by
    rw [hRead]
  refine ⟨b', lane', hok, ?_, ?_, hon', hto', hix, ?_, hheldG, ?_, hheldS, hemptyB,
      hb, hmk, htier, hctrl, hmx, hmv, hsl, hszD, hszH, hhome, hheld,       hpk, hst, hhole,
      hposL', hnle', hfitL', hzero', hopsSz⟩
  · rw [ht, hvSq]
  · intro h
    simpa [hc] using hops h
  · intro h
    rw [hhomeG h, hGHome]
  · intro h
    rw [hhomeS h, hvSq]

end EcbsLink2.Link2
