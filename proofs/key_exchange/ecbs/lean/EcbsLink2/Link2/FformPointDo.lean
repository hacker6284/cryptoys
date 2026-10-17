/-
  The new point of `fform_add`, from the bench that already holds `F`.
  Bottom, then `F` times the run, then the across, then the mirrored rise
  product, then the up, then the gap is cleared. The homes are Spec's
  `fformBottom` and `fformAcross`. The bench prefix is `fformUp`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformPointKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

def stepBudget (n bench : Nat) : Nat :=
  2 * n + n * (n + 1) + 3 * (bench - n)

theorem nocopyCharge_le (n k moves bench : Nat) (xs ys lane : List Nat) (mir : Bool)
    (hn : n ≤ lane.length) :
    nocopyCharge n k moves bench xs ys lane mir ≤ moves + stepBudget n bench := by
  unfold nocopyCharge stepBudget
  have hp : pegCount (lane.take n) ≤ n := by
    have h := pegCount_le (lane.take n)
    rw [List.length_take, Nat.min_eq_left hn] at h
    exact h
  have hs := schoolMoves_bound xs ys n
  have hlen : (nocopySchool n bench xs ys mir).length = bench := by
    simpa [nocopySchool, List.length_replicate] using
      school_length xs ys (List.replicate bench 0) mir n
  have hf := foldCharge_bound n (n - k) (nocopySchool n bench xs ys mir)
  rw [hlen] at hf
  omega

theorem keepCharge_le (n k moves bench : Nat) (xs ys home : List Nat) (mir : Bool)
    (hn : home.length = n) (hleny : ys.length = n) (hb : n ≤ bench) :
    keepCharge n k moves bench xs ys home mir ≤ moves + stepBudget n bench := by
  unfold keepCharge stepBudget
  have hp : pegCount ys ≤ n := by
    simpa [hleny] using pegCount_le ys
  have hs := schoolMoves_bound xs ys n
  have hpad : (pref home bench n).length = bench := pref_length hb (by omega)
  have hlen : (keepSchool n bench xs ys home mir).length = bench := by
    simpa [keepSchool, hpad] using school_length xs ys (pref home bench n) mir n
  have hf := foldCharge_bound n (n - k) (keepSchool n bench xs ys home mir)
  rw [hlen] at hf
  omega

theorem fform_consts :
    Ecbs.across = ((0 : Nat) : Int) ∧ Ecbs.up = ((1 : Nat) : Int) ∧
    Ecbs.bottom = ((2 : Nat) : Int) ∧ Ecbs.base_across = ((3 : Nat) : Int) ∧
    Ecbs.base_up = ((4 : Nat) : Int) ∧ Ecbs.gap = ((5 : Nat) : Int) := by
  simp [Ecbs.across, Ecbs.up, Ecbs.bottom, Ecbs.base_across, Ecbs.base_up, Ecbs.gap,
    ofNat_eq_natCast]

/-- Red new up: the base-up product is not mirrored, because `not red` is false.
    That sum is Spec's new up at `−y₂`. -/
theorem up_red (n k bench : Nat) (y2 u v z f z3 : List Nat)
    (hspan : 2 * (n - 1) < bench) (hnb : n ≤ bench)
    (hfT : allTritList f) (hu : allTritList u) (hy2 : allTritList y2)
    (hz3T : allTritList z3)
    (hfu : allTritList (fieldMul n k bench f u))
    (hyz : allTritList (fieldMul n k bench y2 z3))
    (hf : f = fformF n k bench u v z)
    (hz3 : z3 = fformBottom n k bench v z) :
    fieldAdd n (mirrorTrits (fieldMul n k bench f u)) (fieldMul n k bench y2 z3) =
      fformUp n k bench (mirrorTrits y2) u v z := by
  have hmy : allTritList (fieldMul n k bench (mirrorTrits y2) z3) :=
    prod_trits n k bench (mirrorTrits y2) z3 hspan hnb
  have hmir := fieldMul_mirror_left n k bench y2 z3 hy2 hz3T
  have hback : fieldMul n k bench y2 z3 =
      mirrorTrits (fieldMul n k bench (mirrorTrits y2) z3) := by
    rw [← mirrorTrits_invol (fieldMul n k bench y2 z3) hyz, ← hmir]
  rw [hback, ← mirrorTrits_fieldAdd n (fieldMul n k bench f u)
      (fieldMul n k bench (mirrorTrits y2) z3) hfu hmy,
    fieldMul_comm n k bench f u hfT hu, hf, hz3]
  unfold fformUp
  rfl

/-- One `FitsLen` covers every later counter that stays under the bound. -/
theorem fits_le {a b : Nat} (h : FitsLen b) (hle : a ≤ b) : FitsLen a :=
  FitsLen.of_le h hle

/-- The new bottom. `F` was on the bench aimed at the gap, so the gap now holds
    `F` and the bench prefix is `fformBottom`. SPEC.md §3 R7 line 152. -/
theorem fform_bottom_step (b : Ecbs.Board)
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
    (hlenv : v.length = n)
    (hpeak7 : 7 ≤ peak) (hpeakS7 : 7 ≤ peakS)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v)
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
      Ecbs.mul b Ecbs.bottom Ecbs.across Ecbs.bottom false false false = .ok b' ∧
      b'.sudo_5Board_5bench = embed lane' ∧
      lane'.take n = fformBottom n k bench v z ∧
      (∀ h, b'.sudo_5Board_4home[5]'h = embed (fformF n k bench u v z)) ∧
      (∀ h, b'.sudo_5Board_4home[0]'h = embed v) ∧
      (∀ h, b'.sudo_5Board_4home[1]'h = embed u) ∧
      (∀ h, b'.sudo_5Board_4home[3]'h = embed x2) ∧
      (∀ h, b'.sudo_5Board_4home[4]'h = embed y2) ∧
      (∀ h, b'.sudo_5Board_4held[1]'h = true) ∧
      (∀ h, b'.sudo_5Board_4held[3]'h = true) ∧
      (∀ h, b'.sudo_5Board_4held[4]'h = true) ∧
      (∀ h, b'.sudo_5Board_4held[6]'h = false) ∧
      (∀ h, b'.sudo_5Board_4held[2]'h = false) := by
  have fitLe : ∀ {a}, a ≤ moves + 8 * stepBudget n bench → FitsLen a :=
    fun hle => fits_le hBig hle
  have fitSl : ∀ {a}, a ≤ slides + 8 * n → FitsLen a :=
    fun hle => fits_le hSlide hle
  have hpeg : FitsLen (2 * pegCount (lane.take n)) :=
    fitLe (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfitM : FitsLen (moves + 2 * pegCount (lane.take n)) :=
    fitLe (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfitS : FitsLen (slides + 2 * pegCount (lane.take n)) :=
    fitSl (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      omega)
  have hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)) :=
    fitLe (by
      have hp := pegCount_le (lane.take n)
      rw [List.length_take, Nat.min_eq_left hnle] at hp
      unfold stepBudget; omega)
  have hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
      3 * (bench - n)) :=
    fitLe (by
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
  obtain ⟨b1, lane1, s1, hz3⟩ := fform_new_bottom b 0 2 5 v z lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      h5H h5 h0H h0 h2H h2 hvH hvA hzH hzA
      hmk hon hto hm hc hmx hscript
      (by omega) (fits_le hfitM6 (by omega)) (fits_le hfitC6 (by omega))
      (fits_le hfitM6 (by omega))
      hn hops hop0 (fits_le hfops6 (by omega))
      h7 hgH hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
      hbl (by decide) (by decide) (by decide) hn0 hnb hlenv hpeak7 hpeakS7 hpeakS
      hspan hv hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgapN hw hh hr hk hsm hnsm hfitB hfold
  have hAc := fform_consts.1
  have hBotC := fform_consts.2.2.1
  have stayHome {xs : List Nat} (j : Nat) (hne2 : j ≠ 2) (hne5 : j ≠ 5)
      (hj : j < b.sudo_5Board_4home.size) (harr : b.sudo_5Board_4home[j] = embed xs) :
      ∀ h, b1.sudo_5Board_4home[j]'h = embed xs := by
    intro h
    have hs := s1.stayA j hne2 hj (by rw [s1.homeSz]; exact hj)
    rw [if_neg hne5] at hs
    exact hs.trans harr
  have stayHeld (j : Nat) (hne2 : j ≠ 2) (hne5 : j ≠ 5)
      (hj : j < b.sudo_5Board_4held.size) (harr : b.sudo_5Board_4held[j] = true) :
      ∀ h, b1.sudo_5Board_4held[j]'h = true := by
    intro h
    have hs := s1.stayH j hne2 hj (by rw [s1.heldSz]; exact hj)
    rw [if_neg hne5] at hs
    exact hs.trans harr
  exact ⟨b1, lane1, by rw [hBotC, hAc, s1.mul_ok], s1.bench_eq, hz3,
    by
      intro h
      have hs := s1.stayA 5 (by decide) h5H (by rw [s1.homeSz]; exact h5H)
      rw [if_pos rfl, htake, hfEq] at hs
      exact hs,
    stayHome 0 (by decide) (by decide) h0H hvA,
    stayHome 1 (by decide) (by decide) h1H huA,
    stayHome 3 (by decide) (by decide) h3H hxA,
    stayHome 4 (by decide) (by decide) h4H hyA,
    stayHeld 1 (by decide) (by decide) h1 huH,
    stayHeld 3 (by decide) (by decide) h3 hxH,
    stayHeld 4 (by decide) (by decide) h4 hyH,
    by
      intro h
      have hs := s1.stayH 6 (by decide) h6 (by rw [s1.heldSz]; exact h6)
      rw [if_neg (by decide : ¬ 6 = 5)] at hs
      exact hs.trans hsH,
    s1.clearedH⟩

end EcbsLink2.Link2
