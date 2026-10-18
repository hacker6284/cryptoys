/-
  The run square, in its own module. `gap_u2z` left the bench aimed at the
  gap. This call reads that ops cell. On the rise chain that cell is the
  rise's cell plus 3, and this square leaves the rise's cell plus 4.
  SPEC.md §3 R7. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformGapLay

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Square the run on the board `gap_u2z` leaves. `cOps` is the ops cell that
    line left. `cRise` is the cell the rise read, and `cOps = cRise + 3`.
    This square reads `cOps` and leaves `cRise + 4`. The bench prefix is `v²`. -/
theorem gap_v2_on_u2z (b : Ecbs.Board) (dst gap across : Nat)
    (v lane u z : List Nat)
    (m ctrl mx script cOps cRise n k w h r moves slides hole peak peakS bench : Nat)
    (hRead : cOps = cRise + 3)
    (hG : gap < b.sudo_5Board_4home.size)
    (hGD : gap < b.sudo_5Board_4held.size)
    (hAH : across < b.sudo_5Board_4home.size)
    (hAD : across < b.sudo_5Board_4held.size)
    (hHeldA : b.sudo_5Board_4held[across] = true)
    (hArrA : b.sudo_5Board_4home[across] = embed v)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (gap : Int))
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
    (hempty : b.sudo_5Board_4held[gap] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hpref : lane.take n = fieldMul n k bench z (fieldMul n k bench u u))
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (hne : gap ≠ across) (hne6 : across ≠ 6) (hneG6 : gap ≠ 6)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlen : v.length = n)
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeakS7 : 7 ≤ peakS)
    (hfitP : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v + n * (n + 1)))
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
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + pegCount v +
        n * (n + 1) + 3 * (bench - n))) :
    ∃ b' lane' hole',
      Ecbs.mul b ((dst : Nat) : Int) ((across : Nat) : Int) ((across : Nat) : Int)
          true false false = .ok b' ∧
      lane'.take n = fieldMul n k bench v v ∧
      lane.take n = fieldMul n k bench z (fieldMul n k bench u u) ∧
      BenchCarry b' lane' n (cRise + 4) peak hole' peakS ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = ((dst : Nat) : Int) ∧
      b'.sudo_5Board_9marker_on = true ∧
      b'.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
  obtain ⟨b', lane', hole', hok, _hb, ht, carry, hon', hto', hmk', _htier, hix, hctrl, _hmx⟩ :=
    gap_v2 b dst gap across v lane m ctrl mx script cOps n k w h r moves slides hole
      peak peakS bench hG hGD hAH hAD hHeldA hArrA hmk hon hto hm hc hx hscript
      hbound hfitMk hfitC hfit2 hn hops hop0 hfops h7 hempty hbench hposL hnle hzero
      hf hfitL hmoves hslides hpeak hpeg hfitM hfitS hbl hSpH hSpHome hSpE hne hne6 hneG6
      hn0 hnb hlen hpeak7 hpeakS hpeakS7 hfitP hspan hv hfi hfm hhole hw0 hh0 hrR hrP
      hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  have hc : cOps + 1 = cRise + 4 := by
    rw [hRead]
  refine ⟨b', lane', hole', hok, ht, hpref, ?_, hon', hto', hmk', hix, hctrl⟩
  · simpa [hc] using carry

end EcbsLink2.Link2
