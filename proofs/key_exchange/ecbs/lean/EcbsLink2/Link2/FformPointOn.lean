/-
  The success tail of `fform_add` on the board the gap add leaves. The bench
  prefix is `fformF`, aimed at the empty gap, and the bottom holds `v²Z`.
  The six calls are `fform_add_point`. SPEC.md §3 R7 lines 152–154.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformJoin
import EcbsLink2.Link2.FieldLin

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem fformF_trits (n k bench : Nat) (u v z : List Nat) :
    allTritList (fformF n k bench u v z) := by
  intro a ha
  simp only [fformF, fieldAdd, List.mem_map] at ha
  rcases ha with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

/-- `fform_add_point` when the bench prefix is already `fformF`. The gap is
    empty, the bench is aimed at it, and home 2 holds `v²Z`. The new across,
    the new bottom, and the new up are Spec's. -/
theorem fform_add_on_f (b : Ecbs.Board) (red : Bool)
    (v z x2 u y2 lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size) (h7H : 7 ≤ b.sudo_5Board_4home.size)
    (hvH : b.sudo_5Board_4held[0] = true) (hvA : b.sudo_5Board_4home[0] = embed v)
    (huH : b.sudo_5Board_4held[1] = true) (huA : b.sudo_5Board_4home[1] = embed u)
    (hzH : b.sudo_5Board_4held[2] = true)
    (hzA : b.sudo_5Board_4home[2] =
      embed (fieldMul n k bench (fieldMul n k bench v v) z))
    (hxH : b.sudo_5Board_4held[3] = true) (hxA : b.sudo_5Board_4home[3] = embed x2)
    (hyH : b.sudo_5Board_4held[4] = true) (hyA : b.sudo_5Board_4home[4] = embed y2)
    (hgH : b.sudo_5Board_4held[5] = false) (hsH : b.sudo_5Board_4held[6] = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (5 : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (htake : lane.take n = fformF n k bench u v z)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenv : v.length = n) (hlenu : u.length = n)
    (hlenx : x2.length = n) (hleny : y2.length = n)
    (hpeak7 : 7 ≤ peak) (hpeakS7 : 7 ≤ peakS)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v) (hu : allTritList u)
    (hx2 : allTritList x2) (hy2 : allTritList y2)
    (hfi : FitsLen (2 * (n - 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench) :
    ∃ b' lane',
      (Ecbs.mul b Ecbs.bottom Ecbs.across Ecbs.bottom false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.base_across Ecbs.bottom true true false >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.up false false true >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.base_up Ecbs.bottom true true (! red) >>= fun b =>
        Ecbs.clear b Ecbs.gap >>= fun b =>
        pure (true, b)) = .ok (true, b') ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[0]'h0 = embed (fformAcross n k bench x2 u v z)) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[2]'h2 = embed (fformBottom n k bench v z)) ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n =
        (if red then fformUp n k bench (mirrorTrits y2) u v z
          else fformUp n k bench y2 u v z) ∧
      (∀ hg : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5]'hg = false) ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (1 : Int) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1]'h1 = false) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2]'h2 = true) ∧
      n ≤ lane'.length ∧
      (∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i]'hi = 0) :=
  fform_add_point b red (fformF n k bench u v z) v z x2 u y2 lane
    m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
    h7 h7H hvH hvA huH huA hzH hzA hxH hxA hyH hyA hgH hsH
    hmk hon hto hm hc hmx hscript hbound hfitM6 hfitC6 hfops6
    hn hops hop0 hbench hposL hnle hzero htake rfl
    hf hfitL hmoves hslides hpeak hBig hSlide hbl hn0 hnb
    hlenv hlenu hlenx hleny hpeak7 hpeakS7 hpeakS hspan hv
    (fformF_trits n k bench u v z) hu hx2 hy2 hfi hhole
    hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB

end EcbsLink2.Link2
