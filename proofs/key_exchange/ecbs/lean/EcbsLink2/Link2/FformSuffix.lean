/-
  The success tail of `fform_add` from `F · v` through `clear`.
  One obtain: the run times the gap, the new across, the mirrored gap times
  the rise, the new up, then the gap is cleared. Homes 0 and 2 are Spec's
  across and bottom. The bench prefix is Spec's up.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformPointDo

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem mirrorList_trits (xs : List Nat) : allTritList (mirrorTrits xs) := by
  rw [mirrorTrits_map]
  intro a ha
  simp only [List.mem_map] at ha
  rcases ha with ⟨c, hc, rfl⟩
  exact flipTrit_le c

theorem mirrorList_len (xs : List Nat) : (mirrorTrits xs).length = xs.length := by
  rw [mirrorTrits_map, List.length_map]

theorem lane_tail (n k bench : Nat) (sch lane : List Nat)
    (heq : lane = laneFold n (n - k) sch) (hlen : sch.length = bench)
    (hnb : n ≤ bench) (hn0 : 0 < n) (hg : 0 < n - k) :
    ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
  intro i hi hii
  have hle : n ≤ sch.length := by rw [hlen]; exact hnb
  have hii' : i < (laneFold n (n - k) sch).length := by simpa [heq] using hii
  have hlenL := laneFold_length n (n - k) sch hle
  have hiiS : i < sch.length := by rw [← hlenL]; exact hii'
  have hcof := laneFold_high n (n - k) sch i hn0 hg hle hi hiiS
  have hget : (laneFold n (n - k) sch)[i] = 0 := by
    rw [← coeff_eq_get _ _ hii']
    exact hcof
  simpa [heq] using hget

/-- The board after `F·v` and the new across. The bench prefix is `fformAcross`,
    aimed at across. Home 2 holds `fformBottom`. The gap still holds `F`. -/
structure AcrossBoard
    (b b' : Ecbs.Board) (lane' f u y2 v z x2 : List Nat)
    (m ctrl mx cOps n k moves slides peak peakS hole bench : Nat) : Prop where
  mul_do : (Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
      Ecbs.mul b Ecbs.across Ecbs.base_across Ecbs.bottom true true false) = .ok b'
  bench_eq : b'.sudo_5Board_5bench = embed lane'
  lane_len : lane'.length = bench
  take_eq : lane'.take n = fformAcross n k bench x2 u v z
  tail : ∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i] = 0
  mon : b'.sudo_5Board_9marker_on = true
  on : b'.sudo_5Board_8bench_on = true
  to_eq : b'.sudo_5Board_8bench_to = ((0 : Nat) : Int)
  ix : b'.sudo_5Board_6marker = Int.ofNat m
  ctrl : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  mx : b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  tier : b'.sudo_5Board_1t = b.sudo_5Board_1t
  moves_eq : b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  slides_eq : b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  peak_eq : b'.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)
  strict_eq : b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  hole_eq : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  opsSz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
    b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : ∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h = Int.ofNat cOps
  heldSz : b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size
  homeSz : b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size
  emptyA : ∀ h : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0]'h = false
  upA : ∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1]'h = embed u
  upH : ∀ h : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1]'h = true
  botA : ∀ h : 2 < b'.sudo_5Board_4home.size,
    b'.sudo_5Board_4home[2]'h = embed (fformBottom n k bench v z)
  botH : ∀ h : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2]'h = true
  yA : ∀ h : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4]'h = embed y2
  yH : ∀ h : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4]'h = true
  gapA : ∀ h : 5 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[5]'h = embed f
  gapH : ∀ h : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5]'h = true
  spareH : ∀ h : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6]'h = false

/-- `F·v` and the new across. The bench on entry holds `fformBottom` and is
    aimed at the bottom. The gap holds `F`. SPEC.md §3 R7 lines 152 and 153. -/
theorem fform_across_step (b : Ecbs.Board)
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
    (hfT : allTritList f) (hv : allTritList v) (hx2 : allTritList x2)
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
      AcrossBoard b b' lane' f u y2 v z x2 (m + 2) (ctrl + 4)
        (max (max mx (m + 2)) (m + 3)) (cOps + 2) n k
        (keepCharge n k (nocopyCharge n k moves bench f v lane false) bench x2
          (fformBottom n k bench v z) (fieldMul n k bench f v) false)
        (slides + 2 * pegCount (lane.take n)) peak peakS
        (raisedHole (raisedHole hole (topIdx (nocopySchool n bench f v false)))
          (topIdx (keepSchool n bench x2 (fformBottom n k bench v z)
            (fieldMul n k bench f v) false)))
        bench := by
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
  obtain ⟨b1, lane1, s1⟩ := settle_nocopy b 0 5 0 2 f v lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h2H h2 h5H h5 h0H h0
      hfH hfA hvH hvA
      hmk hon hto hm hc hmx hscript
      (by omega : m + 1 < script)
      (fits_le hfitM (by omega)) (fits_le hfitC (by omega)) (fits_le hfitM (by omega))
      hn hops hop0 (fits_le hfops (by omega))
      h7 hemptyB hbench hposL hnle hzero hf hfitL hmoves hslides hpeak
      hpeg hfitMv hfitSl hbl
      (by decide) (by decide) (by decide) hn0 hnb hlenf hlenv
      hpeak7 hpeakS7 hpeakS hspan hfT hv false
      hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgapE hw hh hr hk hsm hnsm hfitB hfold
  have hfv : lane1.take n = fieldMul n k bench f v := by
    rw [s1.take_eq, if_neg (fun p => Bool.noConfusion p)]
  have hz3T : allTritList (fformBottom n k bench v z) := by
    unfold fformBottom
    exact prod_trits n k bench v _ hspan hnb
  have hfvT : allTritList (fieldMul n k bench f v) := prod_trits n k bench f v hspan hnb
  have hfvLen : (fieldMul n k bench f v).length = n := fieldMul_len n k bench f v hnb
  have hZlen : lane1.length = bench := s1.lane_len
  have hpref1 := zeroTail_pref lane1 n bench hZlen (by rw [hZlen]; exact hnb) s1.tail
  have hbench1 : b1.sudo_5Board_5bench =
      embed (pref (fieldMul n k bench f v) bench n) := by
    rw [s1.bench_eq, hpref1, hfv]
  have hzHome : b1.sudo_5Board_4home[2]'(by rw [s1.homeSz]; exact h2H) =
      embed (fformBottom n k bench v z) := by
    have hs := s1.stayA 2 (by decide) h2H (by rw [s1.homeSz]; exact h2H)
    rw [if_pos rfl, htake] at hs
    exact hs
  have hzHeld : b1.sudo_5Board_4held[2]'(by rw [s1.heldSz]; exact h2) = true := by
    have hs := s1.stayH 2 (by decide) h2 (by rw [s1.heldSz]; exact h2)
    rw [if_pos rfl] at hs
    exact hs
  have hfHome1 : b1.sudo_5Board_4home[5]'(by rw [s1.homeSz]; exact h5H) = embed f := by
    have hs := s1.stayA 5 (by decide) h5H (by rw [s1.homeSz]; exact h5H)
    rw [if_neg (by decide : ¬ (5 = 2))] at hs
    exact hs.trans hfA
  have hfHeld1 : b1.sudo_5Board_4held[5]'(by rw [s1.heldSz]; exact h5) = true := by
    have hs := s1.stayH 5 (by decide) h5 (by rw [s1.heldSz]; exact h5)
    rw [if_neg (by decide : ¬ (5 = 2))] at hs
    exact hs.trans hfH
  have huHome1 : b1.sudo_5Board_4home[1]'(by rw [s1.homeSz]; exact h1H) = embed u := by
    have hs := s1.stayA 1 (by decide) h1H (by rw [s1.homeSz]; exact h1H)
    rw [if_neg (by decide : ¬ (1 = 2))] at hs
    exact hs.trans huA
  have huHeld1 : b1.sudo_5Board_4held[1]'(by rw [s1.heldSz]; exact h1) = true := by
    have hs := s1.stayH 1 (by decide) h1 (by rw [s1.heldSz]; exact h1)
    rw [if_neg (by decide : ¬ (1 = 2))] at hs
    exact hs.trans huH
  have hxHome1 : b1.sudo_5Board_4home[3]'(by rw [s1.homeSz]; exact h3H) = embed x2 := by
    have hs := s1.stayA 3 (by decide) h3H (by rw [s1.homeSz]; exact h3H)
    rw [if_neg (by decide : ¬ (3 = 2))] at hs
    exact hs.trans hxA
  have hxHeld1 : b1.sudo_5Board_4held[3]'(by rw [s1.heldSz]; exact h3) = true := by
    have hs := s1.stayH 3 (by decide) h3 (by rw [s1.heldSz]; exact h3)
    rw [if_neg (by decide : ¬ (3 = 2))] at hs
    exact hs.trans hxH
  have hyHome1 : b1.sudo_5Board_4home[4]'(by rw [s1.homeSz]; exact h4H) = embed y2 := by
    have hs := s1.stayA 4 (by decide) h4H (by rw [s1.homeSz]; exact h4H)
    rw [if_neg (by decide : ¬ (4 = 2))] at hs
    exact hs.trans hyA
  have hyHeld1 : b1.sudo_5Board_4held[4]'(by rw [s1.heldSz]; exact h4) = true := by
    have hs := s1.stayH 4 (by decide) h4 (by rw [s1.heldSz]; exact h4)
    rw [if_neg (by decide : ¬ (4 = 2))] at hs
    exact hs.trans hyH
  have hsHeld1 : b1.sudo_5Board_4held[6]'(by rw [s1.heldSz]; exact h6) = false := by
    have hs := s1.stayH 6 (by decide) h6 (by rw [s1.heldSz]; exact h6)
    rw [if_neg (by decide : ¬ (6 = 2))] at hs
    exact hs.trans hsH
  have hempty0 : b1.sudo_5Board_4held[0]'(by rw [s1.heldSz]; exact h0) = false :=
    s1.clearedH (by rw [s1.heldSz]; exact h0)
  have hzLen : (fformBottom n k bench v z).length = n := by
    unfold fformBottom
    exact fieldMul_len n k bench v _ hnb
  have hcharge1 := nocopyCharge_le n k moves bench f v lane false hnle
  have hpegZ : pegCount (fformBottom n k bench v z) ≤ n := by
    simpa [hzLen] using pegCount_le (fformBottom n k bench v z)
  have hops1 : 0 < b1.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [s1.opsSz]; exact hops
  have hop1 : b1.sudo_5Board_4cost.sudo_5Costs_3ops[0] = Int.ofNat (cOps + 1) :=
    s1.ops0 hops1
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      (nocopyCharge n k moves bench f v lane false : Int) := by
    rw [s1.moves_eq, ofNat_eq_natCast]
  let slides1 := slides + 2 * pegCount (lane.take n)
  let hole1 := raisedHole hole (topIdx (nocopySchool n bench f v false))
  let moves1 := nocopyCharge n k moves bench f v lane false
  obtain ⟨b2, lane2, s2⟩ := keep_copy b1 0 3 2 (fieldMul n k bench f v) x2
      (fformBottom n k bench v z)
      (m + 1) (ctrl + 2) (max mx (m + 2)) script (cOps + 1)
      n k w h r moves1 slides1 hole1 peak peakS bench false
      s1.mon s1.on s1.to_eq s1.ix s1.ctrl s1.mx
      (by rw [s1.tier]; exact hscript)
      (by omega) (fits_le hfitM (by omega)) (fits_le hfitC (by omega))
      (fits_le hfitM (by omega))
      (by rw [s1.tier]; exact hn) hops1 hop1 (fits_le hfops (by omega))
      (by rw [s1.tier]; exact hbl)
      (by rw [s1.heldSz]; exact h0) hempty0 hbench1
      (by rw [s1.heldSz]; exact h3) (by rw [s1.homeSz]; exact h3H) hxHeld1 hxHome1
      (by rw [s1.heldSz]; exact h2) (by rw [s1.homeSz]; exact h2H) hzHeld hzHome
      (by rw [s1.heldSz]; exact h6) (by rw [s1.homeSz]; exact h6H) hsHeld1
      (by rw [s1.heldSz]; exact h7)
      (by decide) (by decide)
      hn0 hnb hfvLen hlenx hzLen hf
      hmv1 s1.slides_eq s1.peak_eq s1.strict_eq hpeak7 hpeakS7
      hspan hfvT hx2 hz3T hfi
      (fits_le hBig (by unfold stepBudget at hcharge1 ⊢; omega))
      (fits_le hBig (by unfold stepBudget at hcharge1 ⊢; omega))
      s1.hole_eq
      hw0 hh0 hrR hrP hnE hkLe hgapE
      (by rw [s1.tier]; exact hw) (by rw [s1.tier]; exact hh)
      (by rw [s1.tier]; exact hr) (by rw [s1.tier]; exact hk)
      hsm hnsm hfitB
      (fits_le hBig (by unfold stepBudget at hcharge1 ⊢; omega))
  have hposG : 0 < n - k := by rw [hgapE]; exact Nat.mul_pos hw0 hrP
  have hsch2 : (keepSchool n bench x2 (fformBottom n k bench v z)
      (fieldMul n k bench f v) false).length = bench := by
    have hpad : (pref (fieldMul n k bench f v) bench n).length = bench :=
      pref_length hnb (by rw [hfvLen]; exact Nat.le_refl _)
    simpa [keepSchool, hpad] using school_length x2 (fformBottom n k bench v z)
      (pref (fieldMul n k bench f v) bench n) false n
  have hlen2 : lane2.length = bench := by
    rw [s2.lane_eq, laneFold_length _ _ _ (by rw [hsch2]; exact hnb), hsch2]
  have htail2 := lane_tail n k bench _ lane2 s2.lane_eq hsch2 hnb hn0 hposG
  have hX : lane2.take n = fformAcross n k bench x2 u v z :=
    across_on_bench b1 b2 lane2 f v (fformBottom n k bench v z) x2
      0 3 2 (m + 1) (ctrl + 2) (max mx (m + 2)) (cOps + 1)
      n k moves1 slides1 peak peakS hole1 bench u z s2 hfT hv hfEq rfl
  have hemptyA : b2.sudo_5Board_4held[0]'(by rw [s2.heldSz]; exact
      (by rw [s1.heldSz]; exact h0)) = false := by
    have hs := s2.stayH 0 (by decide) (by rw [s1.heldSz]; exact h0)
      (by rw [s2.heldSz, s1.heldSz]; exact h0)
    exact hs.trans hempty0
  have hfHome2 : b2.sudo_5Board_4home[5]'(by rw [s2.homeSz, s1.homeSz]; exact h5H) = embed f := by
    have hs := s2.stayA 5 (by decide) (by rw [s1.homeSz]; exact h5H)
      (by rw [s2.homeSz, s1.homeSz]; exact h5H)
    exact hs.trans hfHome1
  have hfHeld2 : b2.sudo_5Board_4held[5]'(by rw [s2.heldSz, s1.heldSz]; exact h5) = true := by
    have hs := s2.stayH 5 (by decide) (by rw [s1.heldSz]; exact h5)
      (by rw [s2.heldSz, s1.heldSz]; exact h5)
    exact hs.trans hfHeld1
  have huHome2 : b2.sudo_5Board_4home[1]'(by rw [s2.homeSz, s1.homeSz]; exact h1H) = embed u := by
    have hs := s2.stayA 1 (by decide) (by rw [s1.homeSz]; exact h1H)
      (by rw [s2.homeSz, s1.homeSz]; exact h1H)
    exact hs.trans huHome1
  have huHeld2 : b2.sudo_5Board_4held[1]'(by rw [s2.heldSz, s1.heldSz]; exact h1) = true := by
    have hs := s2.stayH 1 (by decide) (by rw [s1.heldSz]; exact h1)
      (by rw [s2.heldSz, s1.heldSz]; exact h1)
    exact hs.trans huHeld1
  have hyHome2 : b2.sudo_5Board_4home[4]'(by rw [s2.homeSz, s1.homeSz]; exact h4H) = embed y2 := by
    have hs := s2.stayA 4 (by decide) (by rw [s1.homeSz]; exact h4H)
      (by rw [s2.homeSz, s1.homeSz]; exact h4H)
    exact hs.trans hyHome1
  have hyHeld2 : b2.sudo_5Board_4held[4]'(by rw [s2.heldSz, s1.heldSz]; exact h4) = true := by
    have hs := s2.stayH 4 (by decide) (by rw [s1.heldSz]; exact h4)
      (by rw [s2.heldSz, s1.heldSz]; exact h4)
    exact hs.trans hyHeld1
  have hzHome2 : b2.sudo_5Board_4home[2]'(by rw [s2.homeSz, s1.homeSz]; exact h2H) =
      embed (fformBottom n k bench v z) := by
    have hs := s2.stayA 2 (by decide) (by rw [s1.homeSz]; exact h2H)
      (by rw [s2.homeSz, s1.homeSz]; exact h2H)
    exact hs.trans hzHome
  have hzHeld2 : b2.sudo_5Board_4held[2]'(by rw [s2.heldSz, s1.heldSz]; exact h2) = true := by
    have hs := s2.stayH 2 (by decide) (by rw [s1.heldSz]; exact h2)
      (by rw [s2.heldSz, s1.heldSz]; exact h2)
    exact hs.trans hzHeld
  have hsHeld2 : b2.sudo_5Board_4held[6]'(by rw [s2.heldSz, s1.heldSz]; exact h6) = false :=
    s2.spareH _

  have hdo :
      (Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.base_across Ecbs.bottom true true false) = .ok b2 := by
    have hAc := fform_consts.1
    have hBot := fform_consts.2.2.1
    have hBa := fform_consts.2.2.2.1
    have hGap := fform_consts.2.2.2.2.2
    rw [hAc, hGap, hBa, hBot, s1.mul_ok, ok_bind, s2.mul_ok]
  exact ⟨b2, lane2, {
    mul_do := hdo
    bench_eq := s2.bench_eq
    lane_len := hlen2
    take_eq := hX
    tail := htail2
    mon := s2.mon
    on := s2.on
    to_eq := s2.to_eq
    ix := s2.ix
    ctrl := s2.ctrl
    mx := s2.mx
    tier := s2.tier.trans s1.tier
    moves_eq := s2.moves_eq
    slides_eq := s2.slides_eq
    peak_eq := s2.peak_eq
    strict_eq := s2.strict_eq
    hole_eq := s2.hole_eq
    opsSz := s2.opsSz.trans s1.opsSz
    ops0 := s2.ops0
    heldSz := s2.heldSz.trans s1.heldSz
    homeSz := s2.homeSz.trans s1.homeSz
    emptyA := fun _ => hemptyA
    upA := fun _ => huHome2
    upH := fun _ => huHeld2
    botA := fun _ => hzHome2
    botH := fun _ => hzHeld2
    yA := fun _ => hyHome2
    yH := fun _ => hyHeld2
    gapA := fun _ => hfHome2
    gapH := fun _ => hfHeld2
    spareH := fun _ => hsHeld2 }⟩

end EcbsLink2.Link2
