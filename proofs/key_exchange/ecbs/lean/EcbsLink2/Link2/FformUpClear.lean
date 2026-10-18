/-
  The rise product, the new up, and `clear`, then the five calls from `F·v`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformSuffix

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- From the board `fform_across_step` leaves, settle `fformAcross` into across,
    lay the mirrored rise product, keep the new up, and clear the gap.
    SPEC.md §3 R7 lines 153 and 154. -/
theorem fform_up_clear (b bA : Ecbs.Board) (laneA f u y2 v z x2 : List Nat) (red : Bool)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hA : AcrossBoard b bA laneA f u y2 v z x2 m ctrl mx cOps n k moves slides
      peak peakS hole bench)
    (h7 : 7 ≤ b.sudo_5Board_4held.size) (h7H : 7 ≤ b.sudo_5Board_4home.size)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script)
    (hfitM : FitsLen (m + 3)) (hfitC : FitsLen (ctrl + 4)) (hfops : FitsLen (cOps + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hopsB : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hfEq : f = fformF n k bench u v z)
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 3 * stepBudget n bench))
    (hSlide : FitsLen (slides + 2 * n))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenf : f.length = n) (hlenu : u.length = n) (hleny : y2.length = n)
    (hpeak7 : 7 ≤ peak) (hpeakS7 : 7 ≤ peakS)
    (hspan : 2 * (n - 1) < bench)
    (hfT : allTritList f) (hu : allTritList u) (hy2 : allTritList y2)
    (hfi : FitsLen (2 * (n - 1)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapE : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench) :
    ∃ b' lane',
      (Ecbs.mul bA Ecbs.up Ecbs.gap Ecbs.up false false true >>= fun b =>
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
      (∀ hg : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5]'hg = false) := by
  have h0d : (0 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h1d : (1 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h2d : (2 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h4d : (4 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h5d : (5 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h6d : (6 : Nat) < bA.sudo_5Board_4held.size := by rw [hA.heldSz]; omega
  have h0H : (0 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have h1H : (1 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have h2H : (2 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have h4H : (4 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have h5H : (5 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have h6H : (6 : Nat) < bA.sudo_5Board_4home.size := by rw [hA.homeSz]; omega
  have hopsA : 0 < bA.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hA.opsSz]; exact hopsB
  have hopA : bA.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsA = (cOps : Int) := by
    rw [hA.ops0 hopsA, ofNat_eq_natCast]
  have hto0 : bA.sudo_5Board_8bench_to = (0 : Int) := by
    simpa [ofNat_eq_natCast] using hA.to_eq
  have hpeakI : bA.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    rw [hA.peak_eq]
    exact (ofNat_eq_natCast peak).symm
  have hpegA : pegCount (laneA.take n) ≤ n := by
    have hp := pegCount_le (laneA.take n)
    rw [List.length_take, Nat.min_eq_left (by rw [hA.lane_len]; exact hnb)] at hp
    exact hp
  have hzLen : (fformBottom n k bench v z).length = n := by
    unfold fformBottom
    exact fieldMul_len n k bench v _ hnb
  have hz3T : allTritList (fformBottom n k bench v z) := by
    unfold fformBottom
    exact prod_trits n k bench v _ hspan hnb
  obtain ⟨b3, lane3, s3⟩ := settle_nocopy bA 1 5 1 0 f u laneA
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h0H h0d h5H h5d h1H h1d
      (hA.gapH h5d) (hA.gapA h5H) (hA.upH h1d) (hA.upA h1H)
      hA.mon hA.on hto0 hA.ix hA.ctrl hA.mx
      (by rw [hA.tier]; exact hscript)
      (by omega) (fits_le hfitM (by omega)) (fits_le hfitC (by omega))
      (fits_le hfitM (by omega))
      (by rw [hA.tier]; exact hn)
      hopsA hopA
      (fits_le hfops (by omega))
      (by rw [hA.heldSz]; exact h7)
      (hA.emptyA h0d) hA.bench_eq
      (by rw [hA.lane_len]; exact Nat.lt_of_lt_of_le hn0 hnb)
      (by rw [hA.lane_len]; exact hnb) hA.tail
      hf (by rw [hA.lane_len]; exact hfitB)
      hA.moves_eq hA.slides_eq hpeakI
      (fits_le hBig (by unfold stepBudget; omega))
      (fits_le hBig (by unfold stepBudget; omega))
      (fits_le hSlide (by omega))
      (by rw [hA.tier]; exact hbl)
      (by decide) (by decide) (by decide) hn0 hnb hlenf hlenu
      hpeak7 hpeakS7 hA.strict_eq hspan hfT hu true
      hfi
      (fits_le hBig (by unfold stepBudget; omega))
      hA.hole_eq
      hw0 hh0 hrR hrP hnE hkLe hgapE
      (by rw [hA.tier]; exact hw) (by rw [hA.tier]; exact hh)
      (by rw [hA.tier]; exact hr) (by rw [hA.tier]; exact hk)
      hsm hnsm hfitB
      (fits_le hBig (by unfold stepBudget; omega))
  have hfu : lane3.take n = mirrorTrits (fieldMul n k bench f u) := by
    have ht := s3.take_eq
    simp only [if_true] at ht
    exact ht
  have hlen3 : lane3.length = bench := s3.lane_len
  have hpref3 := zeroTail_pref lane3 n bench hlen3 (by rw [hlen3]; exact hnb) s3.tail
  have hbench3 : b3.sudo_5Board_5bench =
      embed (pref (mirrorTrits (fieldMul n k bench f u)) bench n) := by
    rw [s3.bench_eq, hpref3, hfu]
  have hfuT : allTritList (fieldMul n k bench f u) := prod_trits n k bench f u hspan hnb
  have hmirLen : (mirrorTrits (fieldMul n k bench f u)).length = n := by
    rw [mirrorList_len, fieldMul_len n k bench f u hnb]
  have hmirT : allTritList (mirrorTrits (fieldMul n k bench f u)) := mirrorList_trits _
  have hyzT : allTritList (fieldMul n k bench y2 (fformBottom n k bench v z)) :=
    prod_trits n k bench y2 (fformBottom n k bench v z) hspan hnb
  have h0b3 : (0 : Nat) < b3.sudo_5Board_4home.size := by rw [s3.homeSz]; exact h0H
  have h2b3 : (2 : Nat) < b3.sudo_5Board_4home.size := by rw [s3.homeSz]; exact h2H
  have h4b3 : (4 : Nat) < b3.sudo_5Board_4home.size := by rw [s3.homeSz]; exact h4H
  have h5b3 : (5 : Nat) < b3.sudo_5Board_4home.size := by rw [s3.homeSz]; exact h5H
  have h2d3 : (2 : Nat) < b3.sudo_5Board_4held.size := by rw [s3.heldSz]; exact h2d
  have h4d3 : (4 : Nat) < b3.sudo_5Board_4held.size := by rw [s3.heldSz]; exact h4d
  have h5d3 : (5 : Nat) < b3.sudo_5Board_4held.size := by rw [s3.heldSz]; exact h5d
  have h6d3 : (6 : Nat) < b3.sudo_5Board_4held.size := by rw [s3.heldSz]; exact h6d
  have h6b3 : (6 : Nat) < b3.sudo_5Board_4home.size := by rw [s3.homeSz]; exact h6H
  have h1d3 : (1 : Nat) < b3.sudo_5Board_4held.size := by rw [s3.heldSz]; exact h1d
  have hXhome : b3.sudo_5Board_4home[0] = embed (fformAcross n k bench x2 u v z) := by
    have hs := s3.stayA 0 (by decide) h0H h0b3
    rw [if_pos rfl, hA.take_eq] at hs
    exact hs
  have hzHome3 : b3.sudo_5Board_4home[2] = embed (fformBottom n k bench v z) := by
    have hs := s3.stayA 2 (by decide) h2H h2b3
    rw [if_neg (by decide : ¬ (2 = 0))] at hs
    exact hs.trans (hA.botA h2H)
  have hzHeld3 : b3.sudo_5Board_4held[2] = true := by
    have hs := s3.stayH 2 (by decide) h2d h2d3
    rw [if_neg (by decide : ¬ (2 = 0))] at hs
    exact hs.trans (hA.botH h2d)
  have hyHome3 : b3.sudo_5Board_4home[4] = embed y2 := by
    have hs := s3.stayA 4 (by decide) h4H h4b3
    rw [if_neg (by decide : ¬ (4 = 0))] at hs
    exact hs.trans (hA.yA h4H)
  have hyHeld3 : b3.sudo_5Board_4held[4] = true := by
    have hs := s3.stayH 4 (by decide) h4d h4d3
    rw [if_neg (by decide : ¬ (4 = 0))] at hs
    exact hs.trans (hA.yH h4d)
  have hfHome3 : b3.sudo_5Board_4home[5] = embed f := by
    have hs := s3.stayA 5 (by decide) h5H h5b3
    rw [if_neg (by decide : ¬ (5 = 0))] at hs
    exact hs.trans (hA.gapA h5H)
  have hfHeld3 : b3.sudo_5Board_4held[5] = true := by
    have hs := s3.stayH 5 (by decide) h5d h5d3
    rw [if_neg (by decide : ¬ (5 = 0))] at hs
    exact hs.trans (hA.gapH h5d)
  have hsHeld3 : b3.sudo_5Board_4held[6] = false := by
    have hs := s3.stayH 6 (by decide) h6d h6d3
    rw [if_neg (by decide : ¬ (6 = 0))] at hs
    exact hs.trans (hA.spareH h6d)
  have hemptyU : b3.sudo_5Board_4held[1] = false := s3.clearedH h1d3
  have hcu := nocopyCharge_le n k moves bench f u laneA true
    (by rw [hA.lane_len]; exact hnb)
  have hpegZ : pegCount (fformBottom n k bench v z) ≤ n := by
    simpa [hzLen] using pegCount_le (fformBottom n k bench v z)
  let moves3 := nocopyCharge n k moves bench f u laneA true
  let slides3 := slides + 2 * pegCount (laneA.take n)
  let hole3 := raisedHole hole (topIdx (nocopySchool n bench f u true))
  have hops3 : 0 < b3.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [s3.opsSz]; exact hopsA
  have hmv3 : b3.sudo_5Board_4cost.sudo_5Costs_5moves = (moves3 : Int) := by
    rw [s3.moves_eq, ofNat_eq_natCast]
  obtain ⟨b4, lane4, s4⟩ := keep_copy b3 1 4 2
      (mirrorTrits (fieldMul n k bench f u)) y2 (fformBottom n k bench v z)
      (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1)
      n k w h r moves3 slides3 hole3 peak peakS bench (! red)
      s3.mon s3.on s3.to_eq s3.ix s3.ctrl s3.mx
      (by rw [s3.tier, hA.tier]; exact hscript)
      (by omega) (fits_le hfitM (by omega)) (fits_le hfitC (by omega))
      (fits_le hfitM (by omega))
      (by rw [s3.tier, hA.tier]; exact hn)
      hops3 (s3.ops0 hops3) (fits_le hfops (by omega))
      (by rw [s3.tier, hA.tier]; exact hbl)
      h1d3 hemptyU hbench3
      h4d3 h4b3 hyHeld3 hyHome3
      h2d3 h2b3 hzHeld3 hzHome3
      h6d3 h6b3 hsHeld3
      (by rw [s3.heldSz, hA.heldSz]; exact h7)
      (by decide) (by decide)
      hn0 hnb hmirLen hleny hzLen hf
      hmv3 s3.slides_eq s3.peak_eq s3.strict_eq hpeak7 hpeakS7
      hspan hmirT hy2 hz3T hfi
      (fits_le hBig (by
        show nocopyCharge n k moves bench f u laneA true +
          pegCount (fformBottom n k bench v z) ≤ moves + 3 * stepBudget n bench
        unfold stepBudget at hcu ⊢
        omega))
      (fits_le hBig (by
        show nocopyCharge n k moves bench f u laneA true +
          pegCount (fformBottom n k bench v z) + n * (n + 1) ≤
          moves + 3 * stepBudget n bench
        unfold stepBudget at hcu ⊢
        omega))
      s3.hole_eq
      hw0 hh0 hrR hrP hnE hkLe hgapE
      (by rw [s3.tier, hA.tier]; exact hw) (by rw [s3.tier, hA.tier]; exact hh)
      (by rw [s3.tier, hA.tier]; exact hr) (by rw [s3.tier, hA.tier]; exact hk)
      hsm hnsm hfitB
      (fits_le hBig (by
        show nocopyCharge n k moves bench f u laneA true +
          pegCount (fformBottom n k bench v z) + n * (n + 1) + 3 * (bench - n) ≤
          moves + 3 * stepBudget n bench
        unfold stepBudget at hcu ⊢
        omega))
  have hY : lane4.take n =
      (if red then fformUp n k bench (mirrorTrits y2) u v z
        else fformUp n k bench y2 u v z) :=
    up_on_bench b3 b4 lane4 f u y2 (fformBottom n k bench v z) red
      1 4 2 (m + 1) (ctrl + 2) (max mx (m + 2)) (cOps + 1)
      n k moves3 slides3 peak peakS hole3 bench v z s4
      hspan hnb hfT hu hy2 hz3T hfuT hyzT hfEq rfl
  have h0b4 : (0 : Nat) < b4.sudo_5Board_4home.size := by rw [s4.homeSz]; exact h0b3
  have h2b4 : (2 : Nat) < b4.sudo_5Board_4home.size := by rw [s4.homeSz]; exact h2b3
  have h5b4 : (5 : Nat) < b4.sudo_5Board_4home.size := by rw [s4.homeSz]; exact h5b3
  have h5d4 : (5 : Nat) < b4.sudo_5Board_4held.size := by rw [s4.heldSz]; exact h5d3
  have hX4 : b4.sudo_5Board_4home[0] = embed (fformAcross n k bench x2 u v z) :=
    (s4.stayA 0 (by decide) h0b3 h0b4).trans hXhome
  have hZ4 : b4.sudo_5Board_4home[2] = embed (fformBottom n k bench v z) :=
    (s4.stayA 2 (by decide) h2b3 h2b4).trans hzHome3
  have hfHome4 : b4.sudo_5Board_4home[5] = embed f :=
    (s4.stayA 5 (by decide) h5b3 h5b4).trans hfHome3
  have hfHeld4 : b4.sudo_5Board_4held[5] = true :=
    (s4.stayH 5 (by decide) h5d3 h5d4).trans hfHeld3
  let moves4 := keepCharge n k moves3 bench y2 (fformBottom n k bench v z)
      (mirrorTrits (fieldMul n k bench f u)) (! red)
  have hmv4 : b4.sudo_5Board_4cost.sudo_5Costs_5moves = (moves4 : Int) := by
    rw [s4.moves_eq, ofNat_eq_natCast]
  have hpegF : pegCount f ≤ n := by simpa [hlenf] using pegCount_le f
  have hck := keepCharge_le n k moves3 bench y2 (fformBottom n k bench v z)
      (mirrorTrits (fieldMul n k bench f u)) (! red) hmirLen hzLen hnb
  have hck' : keepCharge n k (nocopyCharge n k moves bench f u laneA true) bench y2
      (fformBottom n k bench v z) (mirrorTrits (fieldMul n k bench f u)) (! red) ≤
      nocopyCharge n k moves bench f u laneA true + stepBudget n bench := by
    simpa [moves3] using hck
  have hfitClear : FitsLen (moves4 + pegCount f) :=
    fits_le hBig (by
      show keepCharge n k (nocopyCharge n k moves bench f u laneA true) bench y2
          (fformBottom n k bench v z) (mirrorTrits (fieldMul n k bench f u)) (! red) +
          pegCount f ≤ moves + 3 * stepBudget n bench
      unfold stepBudget at hcu hck' ⊢
      omega)
  have hclear := clear_held_refines b4 5 f moves4 h5b4 h5d4 hfHeld4 hfHome4 hmv4
      (by rw [hlenf]; exact hf) hfitClear
  let bC := { b4 with
    sudo_5Board_4home := b4.sudo_5Board_4home.set ⟨5, h5b4⟩ #[]
    sudo_5Board_4held := b4.sudo_5Board_4held.set ⟨5, h5d4⟩ false
    sudo_5Board_4cost := { b4.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves4 + pegCount f) } }
  refine ⟨bC, lane4, ?_, ?_, ?_, ?_, hY, ?_⟩
  · have hUp := fform_consts.2.1
    have hBot := fform_consts.2.2.1
    have hBu := fform_consts.2.2.2.2.1
    have hGap := fform_consts.2.2.2.2.2
    rw [hUp, hGap, hBu, hBot, s3.mul_ok, ok_bind, s4.mul_ok, ok_bind, hclear,
      ok_bind, pure_eq_ok]
  · intro _
    have hne : (5 : Nat) ≠ 0 := by decide
    simpa [bC, Array.getElem_set_ne, hne] using hX4
  · intro _
    have hne : (5 : Nat) ≠ 2 := by decide
    simpa [bC, Array.getElem_set_ne, hne] using hZ4
  · simpa [bC] using s4.bench_eq
  · intro _
    simp [bC, Array.getElem_set]

end EcbsLink2.Link2
