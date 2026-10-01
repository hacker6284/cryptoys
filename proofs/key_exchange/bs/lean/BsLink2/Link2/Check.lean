/-
  BS Link 2: B8 checking a received number (`is_trits`, `is_empty`, `is_lone_white`,
  `check_received`) against the model `Spec.checkReceived`, for an arbitrary received
  list. Includes an index-only scan driver for loops that return early. Proof-only.
-/
import BsLink2.Link2.Walk

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- Ascending index-only `for` loop that returns `false` at the first bad index. -/
theorem asc_scan {β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int Bool))
    (after : Int → Except SudoRt.Trap β) (onRet : Bool → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret false)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1)))) :
    ((∀ i, fromN ≤ i → i ≤ toN → bad i = false) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = after (Int.ofNat toN)) ∧
    ((∃ i, fromN ≤ i ∧ i ≤ toN ∧ bad i = true) →
      SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet = onRet false) := by
  rw [fuelRange_le hle]
  obtain ⟨d, hd⟩ : ∃ d, toN - fromN = d := ⟨_, rfl⟩
  rw [hd]
  induction d generalizing fromN with
  | zero =>
    have heq : fromN = toN := by omega
    subst heq
    constructor
    · intro hall
      have hb := hall fromN (Nat.le_refl _) (Nat.le_refl _)
      rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) (Nat.le_refl _),
        if_neg (by simp [hb]), if_pos rfl]
    · intro ⟨i, h1, h2, hb⟩
      have heq : i = fromN := by omega
      subst heq
      rw [runLoopOn_succ, hstep i (Nat.le_refl _) (Nat.le_refl _),
        if_pos hb]
  | succ d ih =>
    have hne : fromN ≠ toN := by omega
    have ih' := ih (fromN + 1) (by omega) (fun i h1 h2 => hstep i (by omega) h2) (by omega)
    constructor
    · intro hall
      have hb := hall fromN (Nat.le_refl _) hle
      rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle,
        if_neg (by simp [hb]), if_neg hne]
      exact ih'.1 (fun i h1 h2 => hall i (by omega) h2)
    · intro ⟨i, h1, h2, hb⟩
      cases hf : bad fromN
      · rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, hf]
        simp only [Bool.false_eq_true, if_false, if_neg hne]
        have : i ≠ fromN := fun e => by subst e; rw [hf] at hb; exact absurd hb (by decide)
        exact ih'.2 ⟨i, by omega, h2, hb⟩
      · rw [runLoopOn_succ, hstep fromN (Nat.le_refl _) hle, hf]
        rfl

/-- `asc_scan` in goal form. -/
theorem asc_scan_goal {β}
    (step : Int → Except SudoRt.Trap (SudoRt.Flow Int Bool))
    (after : Int → Except SudoRt.Trap β) (onRet : Bool → Except SudoRt.Trap β)
    (bad : Nat → Bool) (fromN toN : Nat) (hle : fromN ≤ toN) (R : Except SudoRt.Trap β)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN → step (Int.ofNat i) =
      if bad i then .ok (.ret false)
      else if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1))))
    (hA : (∀ i, fromN ≤ i → i ≤ toN → bad i = false) → after (Int.ofNat toN) = R)
    (hB : ∀ i, fromN ≤ i → i ≤ toN → bad i = true → onRet false = R) :
    SudoRt.runLoopOn (Int.ofNat fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = R := by
  have hsc := asc_scan step after onRet bad fromN toN hle hstep
  by_cases hall : ∀ i, fromN ≤ i → i ≤ toN → bad i = false
  · rw [hsc.1 hall]; exact hA hall
  · have hex : ∃ i, fromN ≤ i ∧ i ≤ toN ∧ bad i = true := by
      apply Classical.byContradiction
      intro hne; apply hall
      intro i h1 h2
      cases h : bad i
      · rfl
      · exact absurd ⟨i, h1, h2, h⟩ hne
    obtain ⟨i, h1, h2, hb⟩ := hex
    rw [hsc.2 ⟨i, h1, h2, hb⟩]; exact hB i h1 h2 hb

/-- Two trit arrays of the same size with the same value are equal. -/
theorem trits_ext {a b : Array Int} (ha : Trits a) (hb : Trits b) (hs : a.size = b.size)
    (hv : val a = val b) : a = b := by
  have h0 := val_nonneg ha
  obtain ⟨v, hvv⟩ : ∃ v : Nat, val a = (v : Int) := ⟨(val a).toNat, by omega⟩
  rw [eq_embed_toReg ha rfl hvv, eq_embed_toReg hb hs.symm (hv ▸ hvv)]

theorem is_empty_spec (x : Array Int) (n : Nat) (hx : x.size = n) (htx : Trits x)
    (hn : 0 < n) (hfit : FitsLen n) : Bs.is_empty x = .ok (decide (val x = 0)) := by
  unfold Bs.is_empty
  simp only [listLen_eq, hx]
  rw [subI_ofNat_one n hn hfit, ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_scan_goal (fromN := 0) (toN := n - 1) _ _ _
    (fun i => decide (x.getD i 0 ≠ 0)) (Nat.zero_le _) _ ?_ ?_ ?_
  · intro i _ hi
    have hix : i < x.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    dsimp only
    rw [if_neg (ofNat_not_gt hi), atL_ofNat x i hix, ok_bind]
    simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some]
    by_cases hz : x[i] = 0
    · simp only [hz, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
        ne_eq, not_true_eq_false, decide_False, pure_eq_ok, ok_bind]
      exact asc_tail_idx _ i hfi
    · simp [sEq_int, hz]; rfl
  · intro hall
    have hz : x = Array.mkArray n 0 := by
      apply Array.ext _ _ (by simp [hx])
      intro i h1 h2
      have := hall i (Nat.zero_le _) (by omega)
      simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem h1, Option.getD_some] at this
      simp at this; simp [this]
    rw [hz, val_mkArray_zero]; rfl
  · intro i _ h2 hb
    have hix : i < x.size := by omega
    simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some] at hb
    have hne : val x ≠ 0 := by
      intro hv
      have := val_ge_digit htx i hix
      have := (trits_get htx i hix).1
      simp at hb
      have : 0 < x[i] * pw i := Int.mul_pos (by omega) (pw_pos i)
      omega
    simp [hne]; rfl

theorem is_lone_white_spec (x : Array Int) (n : Nat) (hx : x.size = n) (htx : Trits x)
    (hn : 2 ≤ n) (hfit : FitsLen n) : Bs.is_lone_white x = .ok (decide (val x = 1)) := by
  have h0 : 0 < (Array.mkArray n (0 : Int)).size := by simp; omega
  have hLt : Trits ((Array.mkArray n (0 : Int)).set ⟨0, h0⟩ 1) :=
    trits_set (trits_mkArray_zero n) _ h0 (by decide)
  have hLs : ((Array.mkArray n (0 : Int)).set ⟨0, h0⟩ 1).size = n := by simp
  have hLv : val ((Array.mkArray n (0 : Int)).set ⟨0, h0⟩ 1) = 1 := by
    rw [val_set, val_mkArray_zero]; simp [pw]
  have hlone : val x = 1 → x = (Array.mkArray n (0 : Int)).set ⟨0, h0⟩ 1 := fun hv =>
    trits_ext htx hLt (by rw [hx, hLs]) (by rw [hv, hLv])
  have hx0 : 0 < x.size := by omega
  unfold Bs.is_lone_white
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_ofNat x 0 hx0, ok_bind]
  by_cases h1 : x[0] = 1
  · simp only [h1, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false]
    simp only [listLen_eq, hx]
    rw [subI_ofNat_one n (by omega) hfit, ok_bind]
    rw [except_bind_pure, fuelRange_eq]
    refine asc_scan_goal (fromN := 1) (toN := n - 1) _ _ _
      (fun i => decide (x.getD i 0 ≠ 0)) (by omega) _ ?_ ?_ ?_
    · intro i _ hi
      have hix : i < x.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      dsimp only
      rw [if_neg (ofNat_not_gt hi), atL_ofNat x i hix, ok_bind]
      simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some]
      by_cases hz : x[i] = 0
      · simp only [hz, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
          ne_eq, not_true_eq_false, decide_False, pure_eq_ok, ok_bind]
        exact asc_tail_idx _ i hfi
      · simp [sEq_int, hz]; rfl
    · intro hall
      have hz : x = (Array.mkArray n (0 : Int)).set ⟨0, h0⟩ 1 := by
        apply Array.ext _ _ (by simp [hx])
        intro i h1' h2
        by_cases hi0 : i = 0
        · subst hi0; simp [h1]
        · have := hall i (by omega) (by omega)
          simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem h1', Option.getD_some] at this
          simp at this
          rw [Array.getElem_set_ne _ _ _ _ (Ne.symm hi0)]; simp [this]
      rw [hz, hLv]; rfl
    · intro i h1' h2 hb
      have hix : i < x.size := by omega
      simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some] at hb
      have hne : val x ≠ 1 := by
        intro hv
        have hi0 : i ≠ 0 := by omega
        simp at hb
        exact hb (by simp [hlone hv, Array.getElem_set, Ne.symm hi0])
      simp [hne]; rfl
  · have hne : val x ≠ 1 := by
      intro hv
      exact h1 (by simp [hlone hv])
    simp [sEq_int, h1, hne]; rfl

theorem is_trits_spec (x : Array Int) (n : Nat) (hx : x.size = n)
    (hn : 0 < n) (hfit : FitsLen n) :
    Bs.is_trits x = .ok (decide (∀ v ∈ x.toList, 0 ≤ v ∧ v ≤ 2)) := by
  unfold Bs.is_trits
  simp only [listLen_eq, hx]
  rw [subI_ofNat_one n hn hfit, ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_scan_goal (fromN := 0) (toN := n - 1) _ _ _
    (fun i => decide (x.getD i 0 < 0 ∨ x.getD i 0 > 2)) (Nat.zero_le _) _ ?_ ?_ ?_
  · intro i _ hi
    have hix : i < x.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    dsimp only
    rw [if_neg (ofNat_not_gt hi), atL_ofNat x i hix, ok_bind]
    simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some]
    by_cases hz : x[i] < 0
    · simp [hz]; rfl
    · by_cases h2 : x[i] > 2
      · simp [hz, h2, atL_ofNat x i hix]; rfl
      · simp only [hz, h2, decide_False, Bool.false_eq_true, if_false, atL_ofNat x i hix,
          ok_bind, pure_eq_ok, or_self]
        exact asc_tail_idx _ i hfi
  · intro hall
    have ht : ∀ v ∈ x.toList, 0 ≤ v ∧ v ≤ 2 := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      have hix : i < x.size := by simpa using hi
      have := hall i (Nat.zero_le _) (by omega)
      simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some] at this
      simp at this
      simp only [Array.getElem_toList]
      omega
    rw [decide_eq_true ht]; rfl
  · intro i _ h2 hb
    have hix : i < x.size := by omega
    simp only [Array.getD_eq_get?, Array.getElem?_eq_getElem hix, Option.getD_some] at hb
    have hne : ¬ ∀ v ∈ x.toList, 0 ≤ v ∧ v ≤ 2 := by
      intro hall
      have := hall x[i] (Array.getElem_mem_toList x hix)
      simp at hb
      omega
    simp only [hne, decide_False]; rfl

theorem check_received_refines (F : Spec.Field) (hF : F.Wf)
    (hfit : FitsLen (2 * F.n + 2)) (r : List Nat) :
    Bs.check_received (emb F) (embed r) = .ok ((Spec.checkReceived F r).map embed) := by
  have htt := trits_embed hF.toll_trits
  have hts : 0 < (embed F.toll).size := by rw [size_embed]; exact hF.toll_pos
  have htn : (embed F.toll).size < F.n := by rw [size_embed]; exact hF.toll_lt
  have hn2 : 2 ≤ F.n := by have := hF.toll_pos; have := hF.toll_lt; omega
  have hfn : FitsLen F.n := FitsLen.of_le hfit (by omega)
  unfold Bs.check_received Spec.checkReceived
  simp only [listLen_eq, size_embed, sEq_int, show (emb F).sudo_5Field_1n = Int.ofNat F.n from rfl]
  by_cases hl : r.length = F.n
  · have hrs : (embed r).size = F.n := by rw [size_embed, hl]
    simp only [hl, decide_True, Bool.not_true, Bool.false_eq_true, if_false, true_and]
    rw [is_trits_spec (embed r) F.n hrs (by omega) hfn, ok_bind]
    have hiff : (∀ v ∈ (embed r).toList, 0 ≤ v ∧ v ≤ 2) ↔ ∀ t ∈ r, t ≤ 2 := by
      constructor
      · intro h t ht
        have := h (Int.ofNat t) (by rw [toList_embed]; exact List.mem_map_of_mem _ ht)
        have h2 : Int.ofNat t ≤ Int.ofNat 2 := this.2
        exact Int.ofNat_le.mp h2
      · intro h v hv
        exact trits_embed h v hv
    by_cases ht : ∀ t ∈ r, t ≤ 2
    · rw [decide_eq_true (hiff.mpr ht)]
      simp only [ht, Bool.not_true, Bool.false_eq_true, if_false, implies_true, if_true]
      rw [if_pos ht]
      have hr : Trits (embed r) := trits_embed ht
      obtain ⟨m, hm, hms, hmt, _, K, hK⟩ := multiply_spec (emb F) F.n (embed F.toll) rfl rfl
        htt hts htn (embed r) (embed r) hr hr hrs hrs 0 (by decide) (FitsLen.of_le hfit (by omega))
      obtain ⟨t, htid, hts', htt', htv⟩ := tidy_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn
        (FitsLen.of_le hfit (by omega)) m hmt hms
      rw [empty_register_spec (emb F) F.n rfl, ok_bind,
        show (0 : Int) = Int.ofNat 0 from rfl, hm, ok_bind,
        slide_spec _ m (by simp [hms]) (by simp; omega) (by simp; exact hfn), ok_bind,
        ← tidy_eq_in_place, htid, ok_bind,
        is_empty_spec t F.n hts' htt' (by omega) hfn, ok_bind]
      -- the tidy square, as a model number
      have hP := p_cast F hF
      have hsq : val t = ((Spec.value r * Spec.value r % F.p : Nat) : Int) := by
        rw [htv, hK, emod_sub_mul, pw_zero, Int.mul_one, val_embed, ← hP, Int.ofNat_emod,
          Int.ofNat_mul]
      have ht_eq : t = embed (Spec.toReg F.n (Spec.value r * Spec.value r % F.p)) :=
        eq_embed_toReg htt' hts' hsq
      by_cases h0 : Spec.value r * Spec.value r % F.p = 0
      · have : val t = 0 := by rw [hsq, h0]; rfl
        simp only [this, decide_True, if_true, h0, true_or]; rfl
      · have hv0 : ¬ val t = 0 := by rw [hsq]; exact fun e => h0 (Int.ofNat.inj e)
        simp only [hv0, decide_False, Bool.false_eq_true, if_false]
        rw [is_lone_white_spec t F.n hts' htt' hn2 hfn, except_bind_pure]
        by_cases h1 : Spec.value r * Spec.value r % F.p = 1
        · have : val t = 1 := by rw [hsq, h1]; rfl
          simp only [this, decide_True, if_true, h1, or_true]; rfl
        · have hv1 : ¬ val t = 1 := by rw [hsq]; exact fun e => h1 (Int.ofNat.inj e)
          simp only [hv1, decide_False, Bool.false_eq_true, if_false, h0, h1, or_self]
          rw [ht_eq]; rfl
    · rw [decide_eq_false (fun h => ht (hiff.mp h))]
      simp [ht]; rfl
  · have hne : ¬ Int.ofNat r.length = Int.ofNat F.n := fun e => hl (Int.ofNat.inj e)
    rw [decide_eq_false hne]
    simp only [hl, false_and, if_false]; rfl

end BsLink2.Link2
