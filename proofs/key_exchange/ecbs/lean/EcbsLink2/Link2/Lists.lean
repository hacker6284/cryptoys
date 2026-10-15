/-
  ECBS Link 2: `flip`, `prefix`, `npeg`, `is_empty`, `is_trits`. Proof-only.
-/
import EcbsLink2.Link2.Basic

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem not_gt_cast {a b : Nat} (h : a ≤ b) : ¬ ((a : Int) > (b : Int)) :=
  ofNat_not_gt h

theorem subI_cast_zero : SudoRt.subI (Int.ofNat 0) (1 : Int) = .ok (-1) :=
  subI_zero_one

/-- R0. On a trit `0`, `1` or `2`, `flip` is negation in GF(3). -/
theorem flip_refines (c : Nat) (hc : c ≤ 2) :
    Ecbs.flip (Int.ofNat c) = .ok (Int.ofNat (flipTrit c)) := by
  unfold Ecbs.flip flipTrit
  by_cases h0 : c = 0
  · subst h0
    have hb : SudoRt.SEq.beq (Int.ofNat 0) (0 : Int) = true := by
      rw [sEq_int]; exact decide_eq_true rfl
    rw [hb, if_pos rfl, pure_eq_ok]
    simp
  · have hc0 : SudoRt.SEq.beq (Int.ofNat c) (0 : Int) = false := by
      rw [show (0 : Int) = Int.ofNat 0 from rfl, sEq_ofNat]
      simp [h0]
    rw [hc0]
    simp only [Bool.false_eq_true, if_false]
    rw [show (3 : Int) = Int.ofNat 3 from rfl,
      subI_ofNat 3 c (fits_small (by decide)) (by omega), ok_bind, pure_eq_ok]
    simp [h0]

theorem embed_replicate_zero (m : Nat) :
    embed (List.replicate m 0) = Array.mkArray m 0 := by
  apply Array.ext
  · simp [size_embed, List.length_replicate]
  · intro i h1 h2
    simp [get_embed, List.getElem_replicate, Array.getElem_mkArray]

def pref (xs : List Nat) (m i : Nat) : List Nat :=
  xs.take i ++ List.replicate (m - i) 0

theorem pref_length {xs : List Nat} {m i : Nat} (hi : i ≤ m) (hx : i ≤ xs.length) :
    (pref xs m i).length = m := by
  rw [pref, List.length_append, List.length_take, List.length_replicate, Nat.min_eq_left hx]
  omega

theorem pref_zero (xs : List Nat) (m : Nat) : pref xs m 0 = List.replicate m 0 := by
  simp [pref]

theorem pref_done (xs : List Nat) (m : Nat) : pref xs m m = xs.take m := by
  simp [pref]

theorem pref_get {xs : List Nat} {m i j : Nat} (hi : i ≤ m) (hx : i ≤ xs.length) (hj : j < m) :
    (embed (pref xs m i))[j]'(by rw [size_embed, pref_length hi hx]; exact hj) =
      if j < i then Int.ofNat (xs.getD j 0) else 0 := by
  rw [get_embed]
  by_cases hlt : j < i
  · have h1 : j < (xs.take i).length := by rw [List.length_take, Nat.min_eq_left hx]; omega
    have hjx : j < xs.length := by omega
    simp [pref, hlt, List.getElem_append_left h1, List.getElem_take, List.getElem?_eq_getElem hjx,
      List.getD]
  · have h1 : (xs.take i).length ≤ j := by rw [List.length_take, Nat.min_eq_left hx]; omega
    simp [pref, hlt, List.getElem_append_right h1, List.getElem_replicate]

theorem pref_set {xs : List Nat} {m i : Nat} (hi : i < m) (hx : i < xs.length) :
    (embed (pref xs m i)).set
        ⟨i, by rw [size_embed, pref_length (Nat.le_of_lt hi) (Nat.le_of_lt hx)]; omega⟩
        (Int.ofNat xs[i]) =
      embed (pref xs m (i + 1)) := by
  have hle : i ≤ m := Nat.le_of_lt hi
  have hxle : i ≤ xs.length := Nat.le_of_lt hx
  have hle1 : i + 1 ≤ m := Nat.succ_le_of_lt hi
  have hx1 : i + 1 ≤ xs.length := Nat.succ_le_of_lt hx
  apply Array.ext
  · simp [size_embed, pref_length hle hxle, pref_length hle1 hx1]
  · intro j hjL hjR
    have hj : j < m := by
      simpa [size_embed, pref_length hle hxle] using hjL
    by_cases hji : i = j
    · subst hji
      rw [get_embed]
      have htake : i < (xs.take (i + 1)).length := by rw [List.length_take]; omega
      simp [Array.getElem_set, pref, List.getElem_append_left htake, List.getElem_take]
    · simp [Array.getElem_set, hji]
      rw [pref_get hle hxle hj, pref_get hle1 hx1 (by omega : j < m)]
      by_cases hlt : j < i
      · simp [hlt, show j < i + 1 by omega]
      · simp [hlt, show ¬ j < i + 1 by omega]

theorem prefix_refines (xs : List Nat) (m : Nat) (hm : m ≤ xs.length) (hf : FitsLen m) :
    Ecbs.prefix (embed xs) (Int.ofNat m) = .ok (embed (xs.take m)) := by
  unfold Ecbs.prefix
  rw [filledL_ofNat, ok_bind, subI_len_one m hf, ok_bind]
  cases m with
  | zero =>
    rw [show Int.ofNat 0 - 1 = (-1 : Int) by decide]
    dsimp
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    simp [show (0 : Int) > (-1 : Int) by decide, pure_eq_ok]
    simpa [List.replicate, embed] using (embed_replicate_zero 0).symm
  | succ m =>
    have hbound : Int.ofNat (m + 1) - 1 = Int.ofNat m := by
      rw [ofNat_eq_natCast (m + 1), ofNat_eq_natCast m]
      omega
    rw [hbound]
    dsimp
    rw [fuelRange_eq, except_bind_pure]
    refine asc_goal (fromN := 0) (toN := m)
      (fun i (out : Array Int) => out = embed (pref xs (m + 1) i))
      (Nat.zero_le _) ?_ ?_ ?_
    · change Array.mkArray (m + 1) (0 : Int) = embed (pref xs (m + 1) 0)
      rw [pref_zero, embed_replicate_zero]
    · intro i out _ hi hI
      have hix : i < xs.length := by omega
      have hii : i < m + 1 := Nat.lt_succ_of_le hi
      have hlen := pref_length (Nat.le_of_lt hii) (Nat.le_of_lt hix)
      have hio : i < (embed (pref xs (m + 1) i)).size := by rw [size_embed, hlen]; omega
      have hfi : FitsLen (i + 1) := FitsLen.of_le hf (by omega)
      have hng := not_gt_cast hi
      refine ⟨(embed (pref xs (m + 1) i)).set ⟨i, hio⟩ (Int.ofNat xs[i]), ?_, ?_⟩
      · rw [pref_set hii hix]
      · rw [hI]
        dsimp only
        split
        · next hgt => exact absurd hgt (not_gt_cast hi)
        · rw [atL_embed xs i hix, ok_bind, putL_ofNat _ i _ hio, ok_bind]
          exact asc_tail m i hfi _
    · intro out hI
      rw [hI, pref_done, pure_eq_ok]

theorem is_empty_refines (a : Array Int) (hf : FitsLen a.size) :
    Ecbs.is_empty a = .ok (decide (∀ i (h : i < a.size), a[i] = 0)) := by
  unfold Ecbs.is_empty
  simp only [listLen_eq]
  by_cases h0 : a.size = 0
  · simp only [h0]
    rw [subI_cast_zero, ok_bind]
    dsimp
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, pure_eq_ok]
    simp [show (0 : Int) > (-1 : Int) by decide, h0, pure_eq_ok]
  · have hn : 0 < a.size := Nat.pos_of_ne_zero h0
    rw [subI_ofNat_one _ hn hf, ok_bind, except_bind_pure]
    dsimp
    rw [fuelRange_eq]
    refine asc_scan_goal _ _ _ (fun i => if h : i < a.size then decide (a[i] ≠ 0) else false)
      0 (a.size - 1) (Nat.zero_le _) (.ok (decide (∀ i (h : i < a.size), a[i] = 0))) ?_ ?_ ?_
    · intro i hlo hi
      have hix : i < a.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.succ_le hix hf
      dsimp only
      split
      · next hgt => exact absurd hgt (not_gt_cast hi)
      · rw [atL_ofNat a i hix, ok_bind]
        by_cases hz : a[i] = 0
        · simp only [hz, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
            pure_eq_ok, ok_bind, hix, decide_False]
          exact asc_tail_idx (a.size - 1) i hfi
        · simp [sEq_int, hz, hix, pure_eq_ok]
    · intro hall
      have ht : ∀ i (h : i < a.size), a[i] = 0 := by
        intro i hi
        have hle : i ≤ a.size - 1 := by omega
        have hbad := hall i (Nat.zero_le _) hle
        simp [hi] at hbad
        exact hbad
      simp [decide_eq_true ht, pure_eq_ok]
    · intro i hlo hi hb
      have hix : i < a.size := by omega
      have hne : ¬ ∀ j (h : j < a.size), a[j] = 0 := by
        intro hall
        have hz := hall i hix
        have hb' : decide (a[i] ≠ 0) = true := by simpa [hix] using hb
        simp [hz] at hb'
      simp [decide_eq_false hne, pure_eq_ok]

theorem is_trits_refines (a : Array Int) (hf : FitsLen a.size) :
    Ecbs.is_trits a = .ok (decide (∀ i (h : i < a.size), 0 ≤ a[i] ∧ a[i] ≤ 2)) := by
  unfold Ecbs.is_trits
  simp only [listLen_eq]
  by_cases h0 : a.size = 0
  · simp only [h0]
    rw [subI_cast_zero, ok_bind]
    dsimp
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, pure_eq_ok]
    simp [show (0 : Int) > (-1 : Int) by decide, h0, pure_eq_ok]
  · have hn : 0 < a.size := Nat.pos_of_ne_zero h0
    rw [subI_ofNat_one _ hn hf, ok_bind, except_bind_pure]
    dsimp
    rw [fuelRange_eq]
    refine asc_scan_goal _ _ _
      (fun i => if h : i < a.size then decide (¬ (0 ≤ a[i] ∧ a[i] ≤ 2)) else false)
      0 (a.size - 1) (Nat.zero_le _)
      (.ok (decide (∀ i (h : i < a.size), 0 ≤ a[i] ∧ a[i] ≤ 2))) ?_ ?_ ?_
    · intro i hlo hi
      have hix : i < a.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.succ_le hix hf
      dsimp only
      split
      · next hgt => exact absurd hgt (not_gt_cast hi)
      · rw [atL_ofNat a i hix, ok_bind]
        by_cases hok : 0 ≤ a[i] ∧ a[i] ≤ 2
        · have hlo' : ¬ a[i] < 0 := by omega
          have hhi : ¬ a[i] > 2 := by omega
          simp only [hix, hok, hlo', hhi, decide_False, pure_eq_ok, ok_bind, Bool.false_eq_true,
            if_false]
          exact asc_tail_idx (a.size - 1) i hfi
        · by_cases hlt : a[i] < 0
          · simp [hlt, hix, hok, pure_eq_ok]
          · have hhi : a[i] > 2 := by omega
            simp [hlt, hhi, hix, hok, pure_eq_ok]
    · intro hall
      have ht : ∀ i (h : i < a.size), 0 ≤ a[i] ∧ a[i] ≤ 2 := by
        intro i hi
        have hbad := hall i (Nat.zero_le _) (by omega)
        simp [hi] at hbad
        exact hbad
      simp [decide_eq_true ht, pure_eq_ok]
    · intro i hlo hi hb
      have hix : i < a.size := by omega
      have hne : ¬ ∀ j (h : j < a.size), 0 ≤ a[j] ∧ a[j] ≤ 2 := by
        intro hall
        have hz := hall i hix
        have hb' : decide (¬ (0 ≤ a[i] ∧ a[i] ≤ 2)) = true := by simpa [hix] using hb
        simp [hz] at hb'
      simp [decide_eq_false hne, pure_eq_ok]

theorem nnz_append_zero (xs : List Int) : nnz (xs ++ [0]) = nnz xs := by
  induction xs with
  | nil => simp [nnz]
  | cons x xs ih => simp [nnz, ih]

theorem nnz_append_nz (xs : List Int) {x : Int} (hx : x ≠ 0) : nnz (xs ++ [x]) = nnz xs + 1 := by
  induction xs with
  | nil => simp [nnz, hx]
  | cons y ys ih =>
    simp [nnz, ih]
    omega

theorem npeg_refines (a : Array Int) (hf : FitsLen a.size) :
    Ecbs.npeg a = .ok (Int.ofNat (nnz a.toList)) := by
  unfold Ecbs.npeg
  simp only [listLen_eq]
  by_cases h0 : a.size = 0
  · simp only [h0]
    rw [subI_cast_zero, ok_bind]
    dsimp
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, pure_eq_ok]
    have hempty : a.toList = [] := List.eq_nil_of_length_eq_zero (by simp [h0])
    simp [show (0 : Int) > (-1 : Int) by decide, hempty, nnz, pure_eq_ok]
  · have hn : 0 < a.size := Nat.pos_of_ne_zero h0
    rw [subI_ofNat_one _ hn hf, ok_bind, except_bind_pure]
    dsimp
    rw [fuelRange_eq]
    refine asc_goal (fromN := 0) (toN := a.size - 1)
      (fun i (c : Int) => c = Int.ofNat (nnz (a.toList.take i)))
      (Nat.zero_le _) (by simp [nnz]) ?_ ?_
    · intro i c _ hi hc
      have hix : i < a.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.succ_le hix hf
      have hcount : nnz (a.toList.take i) ≤ i := by
        have hlen := nnz_length_le (a.toList.take i)
        simp [List.length_take] at hlen
        omega
      have hfitc : FitsLen (nnz (a.toList.take i) + 1) := FitsLen.of_le hf (by omega)
      refine ⟨if a[i] = 0 then c else Int.ofNat (nnz (a.toList.take i) + 1), ?_, ?_⟩
      · have htake : a.toList.take (i + 1) = a.toList.take i ++ [a.toList[i]] := by
          rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hix)]
          simp
        dsimp
        rw [htake, hc]
        by_cases hz : a[i] = 0
        · simp [nnz_append_zero, hz, show a.toList[i] = (a[i] : Int) by simp]
        · have hnz : (a[i] : Int) ≠ 0 := by simpa using hz
          simp [nnz_append_nz (a.toList.take i) hnz, hz,
            show a.toList[i] = (a[i] : Int) by simp, Int.ofNat_add]
      · dsimp only
        split
        · next hgt => exact absurd hgt (not_gt_cast hi)
        · rw [atL_ofNat a i hix, ok_bind, hc]
          by_cases hz : a[i] = 0
          · simp only [hz, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
              pure_eq_ok, ok_bind]
            exact asc_tail (a.size - 1) i hfi _
          · simp only [hz, sEq_int, Bool.not_false, decide_False, if_true, pure_eq_ok, ok_bind]
            rw [show (1 : Int) = Int.ofNat 1 from rfl, addI_ofNat _ 1 hfitc]
            exact asc_tail (a.size - 1) i hfi _
    · intro c hc
      have hlen : a.size - 1 + 1 = a.size := by omega
      have htake : a.toList.take a.size = a.toList := by
        rw [← Array.length_toList, List.take_length]
      rw [pure_eq_ok, hc, hlen, htake]
      simp

end EcbsLink2.Link2
