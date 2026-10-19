/-
  The five calls from `F·v` through `clear`, as one obtain.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformUpClear

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem add_move_le (moves mv nocopy n bench : Nat)
    (hnoc : nocopy ≤ moves + stepBudget n bench)
    (hmv : mv ≤ nocopy + 16 * stepBudget n bench) :
    mv ≤ moves + 24 * stepBudget n bench := by
  omega

/-- `F·v`, the across, the mirrored rise product, the up, and `clear`.
    The bench on entry holds `fformBottom` and is aimed at the bottom.
    The gap holds `F`. Homes 0 and 2 are Spec's across and bottom.
    The bench prefix is Spec's up. SPEC.md §3 R7 lines 153 and 154. -/
theorem fform_suffix (b : Ecbs.Board) (red : Bool)
    (f v z x2 u y2 lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size) (h7H : 7 ≤ b.sudo_5Board_4home.size)
    (hvH : b.sudo_5Board_4held[0] = true) (hvA : b.sudo_5Board_4home[0] = embed v)
    (huH : b.sudo_5Board_4held[1] = true) (huA : b.sudo_5Board_4home[1] = embed u)
    (hemptyB : b.sudo_5Board_4held[2] = false)
    (hxH : b.sudo_5Board_4held[3] = true) (hxA : b.sudo_5Board_4home[3] = embed x2)
    (hyH : b.sudo_5Board_4held[4] = true) (hyA : b.sudo_5Board_4home[4] = embed y2)
    (hfH : b.sudo_5Board_4held[5] = true) (hfA : b.sudo_5Board_4home[5] = embed f)
    (hsH : b.sudo_5Board_4held[6] = false)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hmx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 4 < script)
    (hfitM : FitsLen (m + 5)) (hfitC : FitsLen (ctrl + 8)) (hfops : FitsLen (cOps + 4))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (htake : lane.take n = fformBottom n k bench v z)
    (hfEq : f = fformF n k bench u v z)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hBig : FitsLen (moves + 5 * stepBudget n bench))
    (hSlide : FitsLen (slides + 4 * n))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenf : f.length = n) (hlenv : v.length = n)
    (hlenu : u.length = n) (hlenx : x2.length = n) (hleny : y2.length = n)
    (hpeak7 : 7 ≤ peak) (hpeakS7 : 7 ≤ peakS)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hfT : allTritList f) (hv : allTritList v) (hu : allTritList u)
    (hx2 : allTritList x2) (hy2 : allTritList y2)
    (hfi : FitsLen (2 * (n - 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapE : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench) :
    ∃ b' lane',
      (Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
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
      (∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i]'hi = 0) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3]'h3 = embed x2) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3]'h3 = true) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4]'h4 = embed y2) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4]'h4 = true) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∃ moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps',
        TailCharge b' moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps' ∧
        cOps' = cOps + 4 ∧
        ctrl' = ctrl + 8 ∧
        moves' ≤ moves + 16 * stepBudget n bench ∧
        slides' ≤ slides + 12 * n) ∧
      ((1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) ∧
      b'.sudo_5Board_9marker_on = true ∧
      (∀ h0 : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) := by
  obtain ⟨bA, laneA, hA⟩ := fform_across_step b f v z x2 u y2 lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h7 h7H hvH hvA huH huA hemptyB hxH hxA hyH hyA hfH hfA hsH
      hmk hon hto hm hc hmx hscript hbound hfitM hfitC hfops hn hops hop0
      hbench hposL hnle hzero htake hfEq hf hfitL hmoves hslides hpeak hBig hSlide hbl
      hn0 hnb hlenf hlenv hlenu hlenx hleny hpeak7 hpeakS7 hpeakS hspan
      hfT hv hx2 hfi hhole hw0 hh0 hrR hrP hnE hkLe hgapE hw hh hr hk
      hsm hnsm hfitB
  have hnoc := nocopyCharge_le n k moves bench f v lane false hnle
  have hfvLen := fieldMul_len n k bench f v hnb
  have hzLen : (fformBottom n k bench v z).length = n := by
    unfold fformBottom
    exact fieldMul_len n k bench v _ hnb
  have hkeep := keepCharge_le n k (nocopyCharge n k moves bench f v lane false) bench x2
      (fformBottom n k bench v z) (fieldMul n k bench f v) false hfvLen hzLen hnb
  have hBigU : FitsLen (keepCharge n k (nocopyCharge n k moves bench f v lane false) bench x2
      (fformBottom n k bench v z) (fieldMul n k bench f v) false + 3 * stepBudget n bench) :=
    fits_le hBig (by unfold stepBudget at hnoc hkeep ⊢; omega)
  have hSlU : FitsLen ((slides + 2 * pegCount (lane.take n)) + 2 * n) :=
    fits_le hSlide (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      omega)
  obtain ⟨b', lane', htail, h0, h2, hb, ht, hg, hon', hto', h1, h2h, hnle', hzero',
      h3a, h3h, h4a, h4h, htier', hszH', hszD', hcharge, hops1, hmon, hH0⟩ :=
    fform_up_clear b bA laneA f u y2 v z x2 red
      (m + 2) (ctrl + 4) (max (max mx (m + 2)) (m + 3)) script (cOps + 2)
      n k w h r
      (keepCharge n k (nocopyCharge n k moves bench f v lane false) bench x2
        (fformBottom n k bench v z) (fieldMul n k bench f v) false)
      (slides + 2 * pegCount (lane.take n))
      (raisedHole (raisedHole hole (topIdx (nocopySchool n bench f v false)))
        (topIdx (keepSchool n bench x2 (fformBottom n k bench v z)
          (fieldMul n k bench f v) false)))
      peak peakS bench hA h7 h7H hscript hbound hfitM hfitC hfops hn hops
      hfEq hf hBigU hSlU hbl hn0 hnb hlenf hlenu hleny hpeak7 hpeakS7 hspan
      hfT hu hy2 hfi hw0 hh0 hrR hrP hnE hkLe hgapE hw hh hr hk hsm hnsm hfitB
  obtain ⟨mv, sl, ct, mk, mx', pk, ps, ho, cops, ch, hopEq, hctrlEq, hmvLe, hslLe⟩ := hcharge
  have hmvS : mv ≤ moves + 16 * stepBudget n bench := by
    have hnoc := nocopyCharge_le n k moves bench f v lane false hnle
    have hkeep := keepCharge_le n k (nocopyCharge n k moves bench f v lane false) bench x2
      (fformBottom n k bench v z) (fieldMul n k bench f v) false
      (fieldMul_len n k bench f v hnb)
      (by unfold fformBottom; exact fieldMul_len n k bench v _ hnb) hnb
    have hstep : 10 * stepBudget n bench ≤ 16 * stepBudget n bench := by
      unfold stepBudget; omega
    omega
  have hslS : sl ≤ slides + 12 * n := by
    have hp := pegCount_le (lane.take n)
    rw [List.length_take, Nat.min_eq_left hnle] at hp
    omega
  refine ⟨b', lane', ?_, h0, h2, hb, ht, hg, hon', hto', h1, h2h, hnle', hzero',
      h3a, h3h, h4a, h4h, htier', hszH', hszD',
      ⟨mv, sl, ct, mk, mx', pk, ps, ho, cops, ch, ?_, ?_, hmvS, hslS⟩, hops1, hmon, hH0⟩
  · rw [← bind_assoc, hA.mul_do, ok_bind, htail]
  · omega
  · omega

/-- The success tail of `fform_add`, from the new bottom through `clear`.
    On entry the bench holds `F` and is aimed at the gap, and the bottom holds
    `v²Z`. Homes 0 and 2 are Spec's across and bottom. The bench prefix is
    Spec's up. SPEC.md §3 R7 lines 152–154. -/
theorem fform_add_point (b : Ecbs.Board) (red : Bool)
    (f v z x2 u y2 lane : List Nat)
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
    (htake : lane.take n = f) (hfEq : f = fformF n k bench u v z)
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
    (hv : allTritList v) (hfT : allTritList f) (hu : allTritList u)
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
      (∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i]'hi = 0) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3]'h3 = embed x2) ∧
      (∀ h3 : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3]'h3 = true) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4]'h4 = embed y2) ∧
      (∀ h4 : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4]'h4 = true) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∃ moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps',
        TailCharge b' moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps' ∧
        cOps' = cOps + 5 ∧
        ctrl' = ctrl + 10 ∧
        moves' ≤ moves + 24 * stepBudget n bench ∧
        slides' ≤ slides + 16 * n) ∧
      ((1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) ∧
      b'.sudo_5Board_9marker_on = true ∧
      (∀ h0 : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) := by
  have hpeg : FitsLen (2 * pegCount (lane.take n)) :=
    fits_le hBig (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfitMv : FitsLen (moves + 2 * pegCount (lane.take n)) :=
    fits_le hBig (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfitSl : FitsLen (slides + 2 * pegCount (lane.take n)) :=
    fits_le hSlide (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      omega)
  have hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)) :=
    fits_le hBig (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
      3 * (bench - n)) :=
    fits_le hBig (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have h0 : (0 : Nat) < b.sudo_5Board_4held.size := by omega
  have h1 : (1 : Nat) < b.sudo_5Board_4held.size := by omega
  have h2 : (2 : Nat) < b.sudo_5Board_4held.size := by omega
  have h3 : (3 : Nat) < b.sudo_5Board_4held.size := by omega
  have h4 : (4 : Nat) < b.sudo_5Board_4held.size := by omega
  have h5 : (5 : Nat) < b.sudo_5Board_4held.size := by omega
  have h6 : (6 : Nat) < b.sudo_5Board_4held.size := by omega
  have h0H : (0 : Nat) < b.sudo_5Board_4home.size := by omega
  have h1H : (1 : Nat) < b.sudo_5Board_4home.size := by omega
  have h2H : (2 : Nat) < b.sudo_5Board_4home.size := by omega
  have h3H : (3 : Nat) < b.sudo_5Board_4home.size := by omega
  have h4H : (4 : Nat) < b.sudo_5Board_4home.size := by omega
  have h5H : (5 : Nat) < b.sudo_5Board_4home.size := by omega
  have h6H : (6 : Nat) < b.sudo_5Board_4home.size := by omega
  obtain ⟨b1, lane1, s1, hzTake⟩ := fform_new_bottom b 0 2 5 v z lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h5H h5 h0H h0 h2H h2 hvH hvA hzH hzA
      hmk hon hto hm hc hmx hscript
      (by omega) (fits_le hfitM6 (by omega)) (fits_le hfitC6 (by omega))
      (fits_le hfitM6 (by omega))
      hn hops hop0 (fits_le hfops6 (by omega))
      h7 hgH hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitMv hfitSl
      hbl (by decide) (by decide) (by decide) hn0 hnb hlenv hpeak7 hpeakS7 hpeakS
      hspan hv hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB hfold
  have hlen1 : lane1.length = bench := s1.lane_len
  have hlenf : f.length = n := by
    rw [← htake, List.length_take, Nat.min_eq_left hnle]
  have h5b1 : (5 : Nat) < b1.sudo_5Board_4home.size := by rw [s1.homeSz]; exact h5H
  have h5d1 : (5 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h5
  have h0b1 : (0 : Nat) < b1.sudo_5Board_4home.size := by rw [s1.homeSz]; exact h0H
  have h0d1 : (0 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h0
  have h1b1 : (1 : Nat) < b1.sudo_5Board_4home.size := by rw [s1.homeSz]; exact h1H
  have h1d1 : (1 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h1
  have h2d1 : (2 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h2
  have h3b1 : (3 : Nat) < b1.sudo_5Board_4home.size := by rw [s1.homeSz]; exact h3H
  have h3d1 : (3 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h3
  have h4b1 : (4 : Nat) < b1.sudo_5Board_4home.size := by rw [s1.homeSz]; exact h4H
  have h4d1 : (4 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h4
  have h6d1 : (6 : Nat) < b1.sudo_5Board_4held.size := by rw [s1.heldSz]; exact h6
  have hfA1 : b1.sudo_5Board_4home[5] = embed f := by
    have hs := s1.stayA 5 (by decide) h5H h5b1
    rw [if_pos rfl, htake] at hs
    exact hs
  have hfH1 : b1.sudo_5Board_4held[5] = true := by
    have hs := s1.stayH 5 (by decide) h5 h5d1
    rw [if_pos rfl] at hs
    exact hs
  have hvA1 : b1.sudo_5Board_4home[0] = embed v := by
    have hs := s1.stayA 0 (by decide) h0H h0b1
    rw [if_neg (by decide : ¬ (0 = 5))] at hs
    exact hs.trans hvA
  have hvH1 : b1.sudo_5Board_4held[0] = true := by
    have hs := s1.stayH 0 (by decide) h0 h0d1
    rw [if_neg (by decide : ¬ (0 = 5))] at hs
    exact hs.trans hvH
  have huA1 : b1.sudo_5Board_4home[1] = embed u := by
    have hs := s1.stayA 1 (by decide) h1H h1b1
    rw [if_neg (by decide : ¬ (1 = 5))] at hs
    exact hs.trans huA
  have huH1 : b1.sudo_5Board_4held[1] = true := by
    have hs := s1.stayH 1 (by decide) h1 h1d1
    rw [if_neg (by decide : ¬ (1 = 5))] at hs
    exact hs.trans huH
  have hxA1 : b1.sudo_5Board_4home[3] = embed x2 := by
    have hs := s1.stayA 3 (by decide) h3H h3b1
    rw [if_neg (by decide : ¬ (3 = 5))] at hs
    exact hs.trans hxA
  have hxH1 : b1.sudo_5Board_4held[3] = true := by
    have hs := s1.stayH 3 (by decide) h3 h3d1
    rw [if_neg (by decide : ¬ (3 = 5))] at hs
    exact hs.trans hxH
  have hyA1 : b1.sudo_5Board_4home[4] = embed y2 := by
    have hs := s1.stayA 4 (by decide) h4H h4b1
    rw [if_neg (by decide : ¬ (4 = 5))] at hs
    exact hs.trans hyA
  have hyH1 : b1.sudo_5Board_4held[4] = true := by
    have hs := s1.stayH 4 (by decide) h4 h4d1
    rw [if_neg (by decide : ¬ (4 = 5))] at hs
    exact hs.trans hyH
  have hsH1 : b1.sudo_5Board_4held[6] = false := by
    have hs := s1.stayH 6 (by decide) h6 h6d1
    rw [if_neg (by decide : ¬ (6 = 5))] at hs
    exact hs.trans hsH
  have hemptyZ : b1.sudo_5Board_4held[2] = false := s1.clearedH h2d1
  have hops1 : 0 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [s1.opsSz]; exact hops
  have hop1 : b1.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hops1 = Int.ofNat (cOps + 1) :=
    s1.ops0 hops1
  have hto1 : b1.sudo_5Board_8bench_to = (2 : Int) := by
    simpa [ofNat_eq_natCast] using s1.to_eq
  have hpeak1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    rw [s1.peak_eq]
    exact (ofNat_eq_natCast peak).symm
  have hnoc := nocopyCharge_le n k moves bench v
      (fieldMul n k bench (fieldMul n k bench v v) z) lane false hnle
  have hBigS : FitsLen (nocopyCharge n k moves bench v
      (fieldMul n k bench (fieldMul n k bench v v) z) lane false + 5 * stepBudget n bench) :=
    fits_le hBig (by unfold stepBudget at hnoc ⊢; omega)
  have hSlS : FitsLen ((slides + 2 * pegCount (lane.take n)) + 4 * n) :=
    fits_le hSlide (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      omega)
  obtain ⟨b', lane', hsuf, hAcross, hBotH, hb, ht, hg, hon', hto', h1, h2h, hnle', hzero',
      h3a, h3h, h4a, h4h, htier', hszH', hszD', hcharge, hops1, hmon, hH0⟩ :=
    fform_suffix b1 red f v z x2 u y2 lane1
      (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1) n k w h r
      (nocopyCharge n k moves bench v (fieldMul n k bench (fieldMul n k bench v v) z) lane false)
      (slides + 2 * pegCount (lane.take n))
      (raisedHole hole (topIdx (nocopySchool n bench v
        (fieldMul n k bench (fieldMul n k bench v v) z) false)))
      peak peakS bench
      (by rw [s1.heldSz]; exact h7) (by rw [s1.homeSz]; exact h7H)
      hvH1 hvA1 huH1 huA1 hemptyZ hxH1 hxA1 hyH1 hyA1 hfH1 hfA1 hsH1
      s1.mon s1.on hto1 s1.ix s1.ctrl s1.mx
      (by rw [s1.tier]; exact hscript)
      (by omega) (fits_le hfitM6 (by omega)) (fits_le hfitC6 (by omega))
      (fits_le hfops6 (by omega))
      (by rw [s1.tier]; exact hn) hops1 hop1
      s1.bench_eq
      (by rw [hlen1]; exact Nat.lt_of_lt_of_le hn0 hnb)
      (by rw [hlen1]; exact hnb) s1.tail hzTake hfEq hf
      (by rw [hlen1]; exact hfitB)
      s1.moves_eq s1.slides_eq hpeak1 hBigS hSlS
      (by rw [s1.tier]; exact hbl)
      hn0 hnb hlenf hlenv hlenu hlenx hleny hpeak7 hpeakS7 s1.strict_eq hspan
      hfT hv hu hx2 hy2 hfi s1.hole_eq
      hw0 hh0 hrR hrP hnE hkLe hgapN
      (by rw [s1.tier]; exact hw) (by rw [s1.tier]; exact hh)
      (by rw [s1.tier]; exact hr) (by rw [s1.tier]; exact hk)
      hsm hnsm hfitB
  obtain ⟨mv, sl, ct, mk, mx', pk', ps, ho, cops, ch, hopEq, hctrlEq, hmvLe, hslLe⟩ := hcharge
  have hmvA : mv ≤ moves + 24 * stepBudget n bench :=
    add_move_le moves mv
      (nocopyCharge n k moves bench v (fieldMul n k bench (fieldMul n k bench v v) z) lane false)
      n bench
      (nocopyCharge_le n k moves bench v
        (fieldMul n k bench (fieldMul n k bench v v) z) lane false hnle)
      hmvLe
  have hslA : sl ≤ slides + 16 * n := by
    have hp := pegCount_le (lane.take n)
    rw [List.length_take, Nat.min_eq_left hnle] at hp
    omega
  refine ⟨b', lane', ?_, hAcross, hBotH, hb, ht, hg, hon', hto', h1, h2h, hnle', hzero',
      h3a, h3h, h4a, h4h, htier'.trans s1.tier, hszH'.trans s1.homeSz, hszD'.trans s1.heldSz,
      ⟨mv, sl, ct, mk, mx', pk', ps, ho, cops, ch, ?_, ?_, hmvA, hslA⟩, by
        intro h1
        have h11 : 1 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
          rw [s1.opsSz]; exact h1
        rw [hops1 h11, Array.getElem?_eq_getElem h11, s1.ops1 h1,
          Array.getElem?_eq_getElem h1], hmon, hH0⟩
  · have hmul : Ecbs.mul b Ecbs.bottom Ecbs.across Ecbs.bottom false false false = .ok b1 := by
      rw [fform_consts.2.2.1, fform_consts.1, s1.mul_ok]
    rw [hmul, ok_bind, hsuf]
  · omega
  · omega

end EcbsLink2.Link2
