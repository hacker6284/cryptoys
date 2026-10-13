/-
  The first multiply of `chord_tail`: the gap (the inverse of the run) times the
  spare (the rise), into the gap. The marker is already seated, so this is
  `mul_up_eq`. The bench prefix is `fieldMul` of those two homes, first times
  second. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerMul

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Gap times spare. The second home (the spare) is cleared and the product sits
    on the bench, aimed at the gap. The marker flag stays on. -/
theorem chord_gap_mul (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
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
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList inv)
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    let bM := { mulNoOffBoard (markerUpFeed b m ctrl mx) 5 6 inv rise n k moves hole bench
        peak peakS cOps hops hS hHomeS with sudo_5Board_9marker_on := true }
    Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false = .ok bM ∧
      bM.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n inv rise (List.replicate bench 0) false)) ∧
      (laneFold n (n - k) (school n inv rise (List.replicate bench 0) false)).take n =
        fieldMul n k bench inv rise ∧
      bM.sudo_5Board_9marker_on = true := by
  intro bM
  have hne : (5 : Nat) ≠ 6 := by decide
  have hmul := mul_up_eq b 5 5 6 inv rise w h r n k moves hole bench peak peakS cOps
    m ctrl mx script hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hops hop0 hfops hbl
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0 hn hlenx hleny hf hmoves hpeak hpeakS
    hspan hxsT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  refine ⟨?_, ?_, mul_no_prefix n k bench inv rise, ?_⟩
  · rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl,
        show Ecbs.spare = ((6 : Nat) : Int) from rfl]
    simpa [bM] using hmul
  · have hb : bM.sudo_5Board_5bench =
        (mulNoOffBoard (markerUpFeed b m ctrl mx) 5 6 inv rise n k moves hole bench
          peak peakS cOps hops hS hHomeS).sudo_5Board_5bench := by
      simp [bM]
    rw [hb, mul_no_bench]
  · simp [bM]

end EcbsLink2.Link2
