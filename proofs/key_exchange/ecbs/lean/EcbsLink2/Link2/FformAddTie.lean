/-
  The success tail of `fform_add` is the projective chord. `fform_add_on_f`
  writes Spec's across, bottom, and up. `across_on_x3` and `up_on_parts`
  say those lists are `x₃ · Z₃` and `y₃ · Z₃`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformPointOn
import EcbsLink2.Link2.FformLine

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The up the red cell writes is the ordinary up of `−y₂`. -/
def addUp (n k bench : Nat) (red : Bool) (y2 u v z : List Nat) : List Nat :=
  if red then fformUp n k bench (mirrorTrits y2) u v z
  else fformUp n k bench y2 u v z

theorem add_board_proj (n k bench : Nat) (x2 u v z x3 yUp : List Nat) (red : Bool)
    (y2 : List Nat) (b' : Ecbs.Board) (lane' : List Nat)
    (h0 : ∀ h0 : 0 < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[0]'h0 = embed (fformAcross n k bench x2 u v z))
    (h2 : ∀ h2 : 2 < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[2]'h2 = embed (fformBottom n k bench v z))
    (htake : lane'.take n = addUp n k bench red y2 u v z)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z)) :
    (∀ h0 : 0 < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[0]'h0 =
        embed (fieldMul n k bench x3 (fformBottom n k bench v z))) ∧
    (∀ h2 : 2 < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[2]'h2 = embed (fformBottom n k bench v z)) ∧
    lane'.take n = fieldMul n k bench yUp (fformBottom n k bench v z) := by
  refine ⟨?_, h2, ?_⟩
  · intro h
    rw [h0 h, hx]
  · rw [htake, hy]

theorem fform_add_on_proj (b : Ecbs.Board) (red : Bool)
    (v z x2 u y2 lane x3 yUp : List Nat)
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
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v) (hu : allTritList u)
    (hx2 : allTritList x2) (hy2t : allTritList y2)
    (hfi : FitsLen (2 * (n - 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z)) :
    ∃ b' lane',
      (Ecbs.mul b Ecbs.bottom Ecbs.across Ecbs.bottom false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.base_across Ecbs.bottom true true false >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.up false false true >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.base_up Ecbs.bottom true true (! red) >>= fun b =>
        Ecbs.clear b Ecbs.gap >>= fun b =>
        pure (true, b)) = .ok (true, b') ∧
      (∀ h0 : 0 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[0]'h0 =
          embed (fieldMul n k bench x3 (fformBottom n k bench v z))) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[2]'h2 = embed (fformBottom n k bench v z)) ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fieldMul n k bench yUp (fformBottom n k bench v z) ∧
      (∀ hg : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5]'hg = false) ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = (1 : Int) ∧
      (∀ h1 : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1]'h1 = false) ∧
      (∀ h2 : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2]'h2 = true) ∧
      n ≤ lane'.length ∧
      (∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i]'hi = 0) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3]'h3 = embed x2) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3]'h3 = true) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4]'h4 = embed y2) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4]'h4 = true) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∃ moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps',
        TailCharge b' moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps') ∧
      ((1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) := by
  obtain ⟨b', lane', hdo, h0, h2, hbench, htake, hheld, hon, hto, h1, h2h, hnle', hzero,
      h3a, h3h, h4a, h4h, htier, hszH, hszD, hcharge, hops1, _hmon, _hH0⟩ :=
    fform_add_on_f b red v z x2 u y2 lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h7 h7H hvH hvA huH huA hzH hzA hxH hxA hyH hyA hgH hsH
      hmk hon hto hm hc hmx hscript hbound hfitM6 hfitC6 hfops6
      hn hops hop0 hbench hposL hnle hzero htake
      hf hfitL hmoves hslides hpeak hBig hSlide hbl hn0 hnb
      hlenv hlenu hlenx hleny hpeakS hspan hv hu hx2 hy2t hfi hhole
      hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB
  have htake' : lane'.take n = addUp n k bench red y2 u v z := by
    simpa [addUp] using htake
  obtain ⟨h0', h2', hy'⟩ := add_board_proj n k bench x2 u v z x3 yUp red y2 b' lane' h0 h2 htake' hx hy
  obtain ⟨mv, sl, ct, mk, mx', pk', ps, ho, cops, ch, _, _, _, _⟩ := hcharge
  exact ⟨b', lane', hdo, h0', h2', hbench, hy', hheld, hon, hto, h1, h2h, hnle', hzero,
      h3a, h3h, h4a, h4h, htier, hszH, hszD, ⟨mv, sl, ct, mk, mx', pk', ps, ho, cops, ch⟩, hops1⟩

end EcbsLink2.Link2
