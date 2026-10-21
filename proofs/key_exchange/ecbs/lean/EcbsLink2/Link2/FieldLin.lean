/-
  `fieldMul` distributes over `fieldAdd` on the right, and a mirrored
  schoolbook is the colour flip of the plain one. Those two facts tie the
  card's gap schedule to SPEC.md §3 R7. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.StripFold

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem tritAdd_le (a b : Nat) : tritAdd a b ≤ 2 := by
  unfold tritAdd
  exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))

theorem trit_diamond (a b c d : Nat) :
    tritAdd (tritAdd a b) (tritAdd c d) = tritAdd (tritAdd a c) (tritAdd b d) := by
  rw [tritAdd_assoc, ← tritAdd_assoc b, tritAdd_comm b c, tritAdd_assoc, ← tritAdd_assoc]

theorem tritMul_add_left (a b c : Nat) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    tritMul (tritAdd a b) c = tritAdd (tritMul a c) (tritMul b c) := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;>
    rcases hb3 with rfl | rfl | rfl <;>
    rcases hc3 with rfl | rfl | rfl <;>
    simp [tritMul, tritAdd, flipTrit]

theorem flipTrit_le (c : Nat) : flipTrit c ≤ 2 := by
  by_cases h0 : c = 0
  · simp [flipTrit, h0]
  · by_cases h1 : c = 1
    · simp [flipTrit, h1]
    · by_cases h2 : c = 2
      · simp [flipTrit, h2]
      · have hge : 3 ≤ c := by omega
        simp [flipTrit, h0]
        omega

theorem flipTrit_add (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) :
    flipTrit (tritAdd a b) = tritAdd (flipTrit a) (flipTrit b) := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;>
    simp [flipTrit, tritAdd]

theorem flipTrit_invol (c : Nat) (hc : c ≤ 2) : flipTrit (flipTrit c) = c := by
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hc3 with rfl | rfl | rfl <;> simp [flipTrit]

theorem flipTrit_mul (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) :
    flipTrit (tritMul a b) = tritMul a (flipTrit b) := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;>
    simp [tritMul, flipTrit]

theorem mirrorTrits_map (xs : List Nat) : mirrorTrits xs = xs.map flipTrit := by
  unfold mirrorTrits flipTrit
  rfl

private theorem coeff_le_local {xs : List Nat} (h : allTritList xs) (i : Nat) : coeff xs i ≤ 2 := by
  by_cases hi : i < xs.length
  · rw [coeff_eq_get xs i hi]
    exact h _ (List.getElem_mem hi)
  · unfold coeff
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp

private theorem coeff_ge_local (xs : List Nat) (t : Nat) (h : xs.length ≤ t) : coeff xs t = 0 := by
  unfold coeff
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp

private theorem coeff_replicate_zero_local (bench t : Nat) :
    coeff (List.replicate bench 0) t = 0 := by
  by_cases ht : t < bench
  · rw [coeff_eq_get _ t (by simpa using ht), List.getElem_replicate]
  · exact coeff_ge_local _ t (by simpa using Nat.le_of_not_gt ht)

private theorem list_set_ge {α : Type} (xs : List α) (i : Nat) (a : α) (h : xs.length ≤ i) :
    xs.set i a = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.length_cons] at h
      omega
    | succ i =>
      simp only [List.set]
      apply congrArg (fun ys => x :: ys)
      apply ih
      simp only [List.length_cons] at h
      omega

private theorem coeff_set_same (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    coeff (xs.set i v) i = v := by
  have hi' : i < (xs.set i v).length := by rw [List.length_set]; exact hi
  rw [coeff_eq_get _ i hi', List.getElem_set_self]

private theorem coeff_set_ne_local (xs : List Nat) (i v j : Nat) (hj : j < xs.length) (hne : i ≠ j) :
    coeff (xs.set i v) j = coeff xs j := by
  have hj' : j < (xs.set i v).length := by rw [List.length_set]; exact hj
  rw [coeff_eq_get _ j hj', List.getElem_set, if_neg hne, ← coeff_eq_get xs j hj]

private theorem laidTrit_zero (mir : Bool) : laidTrit 0 mir = 0 := by
  cases mir <;> simp [laidTrit, flipTrit]

private theorem laid_tritMul (c d : Nat) (hc : c ≤ 2) (h0 : c ≠ 0) :
    laidTrit d (decide (c = 2)) = tritMul c d := by
  have hc3 : c = 1 ∨ c = 2 := by omega
  rcases hc3 with rfl | rfl <;> simp [laidTrit, tritMul]

private theorem laid_mirror (c d : Nat) (hc : c ≤ 2) (hd : d ≤ 2) (h0 : c ≠ 0) :
    laidTrit d (decide (c = 2) != true) = flipTrit (tritMul c d) := by
  have hc3 : c = 1 ∨ c = 2 := by omega
  rcases hc3 with rfl | rfl
  · have hflag : (decide ((1 : Nat) = 2) != true) = true := by decide
    rw [hflag]
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;> simp [laidTrit, tritMul, flipTrit]
  · have hflag : (decide ((2 : Nat) = 2) != true) = false := by decide
    rw [hflag]
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl <;> simp [laidTrit, tritMul, flipTrit]

private theorem schoolStep_eq (a st : List Nat) (i j : Nat) (mir : Bool) :
    schoolStep a i mir st j =
      if coeff a j = 0 then st else
        st.set (i + j) (tritAdd (coeff st (i + j)) (laidTrit (coeff a j) mir)) := by
  unfold schoolStep layCell laidTrit
  rfl

private theorem schoolStep_len (xs st : List Nat) (i j : Nat) (mir : Bool) :
    (schoolStep xs i mir st j).length = st.length := by
  rw [schoolStep_eq]
  by_cases hz : coeff xs j = 0
  · simp [hz]
  · simp [hz, List.length_set]

private theorem schoolStep_coeff (a st : List Nat) (i j t : Nat) (mir : Bool)
    (hc : coeff st t ≤ 2) :
    coeff (schoolStep a i mir st j) t =
      if t = i + j ∧ t < st.length then
        tritAdd (coeff st t) (laidTrit (coeff a j) mir)
      else coeff st t := by
  rw [schoolStep_eq]
  by_cases hz : coeff a j = 0
  · rw [if_pos hz]
    have hlay : laidTrit (coeff a j) mir = 0 := by rw [hz]; exact laidTrit_zero mir
    rw [hlay]
    by_cases hhit : t = i + j ∧ t < st.length
    · rw [if_pos hhit, tritAdd_zero_right _ hc]
    · rw [if_neg hhit]
  · rw [if_neg hz]
    by_cases hidx : i + j < st.length
    · by_cases ht : t = i + j
      · rw [ht]
        rw [coeff_set_same _ _ _ hidx, if_pos ⟨rfl, hidx⟩]
      · by_cases htl : t < st.length
        · have hne : i + j ≠ t := by
            intro h
            exact ht h.symm
          rw [coeff_set_ne_local _ _ _ _ htl hne]
          have hmiss : ¬ (t = i + j ∧ t < st.length) := by
            intro h
            exact ht h.1
          rw [if_neg hmiss]
        · have hlenS : (st.set (i + j) (tritAdd (coeff st (i + j)) (laidTrit (coeff a j) mir))).length =
              st.length := by rw [List.length_set]
          rw [coeff_ge_local _ t (by rw [hlenS]; exact Nat.le_of_not_gt htl)]
          have hmiss : ¬ (t = i + j ∧ t < st.length) := by
            intro h
            exact htl h.2
          rw [if_neg hmiss]
          exact (coeff_ge_local st t (Nat.le_of_not_gt htl)).symm
    · rw [list_set_ge _ _ _ (Nat.le_of_not_gt hidx)]
      have hmiss : ¬ (t = i + j ∧ t < st.length) := by
        intro h
        exact hidx (by rw [← h.1]; exact h.2)
      rw [if_neg hmiss]

private theorem rowAt_len (a st : List Nat) (i : Nat) (mir : Bool) :
    ∀ k, (rowAt a i mir st k).length = st.length
  | 0 => rfl
  | k + 1 => by
    rw [rowAt_succ, schoolStep_len, rowAt_len a st i mir k]

private theorem rowAt_coeff_go (a st : List Nat) (i k t : Nat) (mir : Bool)
    (hc : coeff st t ≤ 2) :
    coeff (rowAt a i mir st k) t =
      if i ≤ t ∧ t - i < k ∧ t < st.length then
        tritAdd (coeff st t) (laidTrit (coeff a (t - i)) mir)
      else coeff st t := by
  induction k with
  | zero =>
    rw [rowAt_zero]
    have hno : ¬ (i ≤ t ∧ t - i < 0 ∧ t < st.length) := by
      intro h
      exact Nat.not_lt_zero _ h.2.1
    simp only [hno, ite_false]
  | succ k ih =>
    rw [rowAt_succ]
    have hprev_le : coeff (rowAt a i mir st k) t ≤ 2 := by
      rw [ih]
      by_cases h : i ≤ t ∧ t - i < k ∧ t < st.length
      · rw [if_pos h]
        exact tritAdd_le _ _
      · rw [if_neg h]
        exact hc
    have hlen : (rowAt a i mir st k).length = st.length := rowAt_len a st i mir k
    have hstep := schoolStep_coeff a (rowAt a i mir st k) i k t mir hprev_le
    rw [hlen] at hstep
    rw [hstep, ih]
    by_cases hhit : t = i + k ∧ t < st.length
    · rcases hhit with ⟨ht, htl⟩
      have hsub : t - i = k := by rw [ht]; omega
      have hcondk : ¬ (i ≤ t ∧ t - i < k ∧ t < st.length) := by
        intro hc2
        have : t - i < k := hc2.2.1
        rw [hsub] at this
        exact Nat.lt_irrefl k this
      have hcond1 : i ≤ t ∧ t - i < k + 1 ∧ t < st.length := by
        refine ⟨?_, ?_, htl⟩
        · rw [ht]; exact Nat.le_add_right _ _
        · rw [hsub]; exact Nat.lt_succ_self k
      rw [if_pos ⟨ht, htl⟩, if_neg hcondk, if_pos hcond1, hsub]
    · by_cases hcond1 : i ≤ t ∧ t - i < k + 1 ∧ t < st.length
      · rcases hcond1 with ⟨hle, hlt1, htl⟩
        have hle_sub : t - i ≤ k := Nat.le_of_lt_succ hlt1
        have hsub_lt : t - i < k := by
          rcases Nat.lt_or_eq_of_le hle_sub with hlt | heq
          · exact hlt
          · exfalso
            apply hhit
            have hadd : i + (t - i) = t := Nat.add_sub_of_le hle
            rw [heq] at hadd
            exact ⟨hadd.symm, htl⟩
        have hcondk : i ≤ t ∧ t - i < k ∧ t < st.length := ⟨hle, hsub_lt, htl⟩
        have hcondS : i ≤ t ∧ t - i < k + 1 ∧ t < st.length :=
          ⟨hle, Nat.lt_trans hsub_lt (Nat.lt_succ_self k), htl⟩
        rw [if_neg hhit, if_pos hcondk, if_pos hcondS]
      · have hcondk : ¬ (i ≤ t ∧ t - i < k ∧ t < st.length) := by
          intro hc2
          exact hcond1 ⟨hc2.1, Nat.lt_trans hc2.2.1 (Nat.lt_succ_self k), hc2.2.2⟩
        rw [if_neg hhit, if_neg hcondk, if_neg hcond1]

private theorem rowAt_coeff (a st : List Nat) (i n t : Nat) (mir : Bool)
    (hc : coeff st t ≤ 2) :
    coeff (rowAt a i mir st n) t =
      if i ≤ t ∧ t - i < n ∧ t < st.length then
        tritAdd (coeff st t) (laidTrit (coeff a (t - i)) mir)
      else coeff st t :=
  rowAt_coeff_go a st i n t mir hc

private theorem schoolAt_eq (n : Nat) (first second : List Nat) (i : Nat) (st : List Nat) :
    schoolAt n first second false i st =
      if coeff second i = 0 then st else
        schoolRow n first i (decide (coeff second i = 2) != false) st := by
  unfold schoolAt
  rfl

private theorem mir_of_false (c : Nat) :
    (decide (c = 2) != false) = decide (c = 2) := by
  cases decide (c = 2) <;> rfl

private theorem schoolAt_coeff (x y st : List Nat) (n i t : Nat)
    (hc : coeff st t ≤ 2) (hy : allTritList y) :
    coeff (schoolAt n x y false i st) t =
      tritAdd (coeff st t)
        (if i ≤ t ∧ t - i < n ∧ t < st.length then
          tritMul (coeff y i) (coeff x (t - i)) else 0) := by
  rw [schoolAt_eq]
  by_cases hz : coeff y i = 0
  · rw [if_pos hz]
    have hmul : tritMul (coeff y i) (coeff x (t - i)) = 0 := by rw [hz]; rfl
    rw [hmul]
    have hif : (if i ≤ t ∧ t - i < n ∧ t < st.length then 0 else 0) = 0 := by
      by_cases h : i ≤ t ∧ t - i < n ∧ t < st.length <;> simp [h]
    rw [hif, tritAdd_zero_right _ hc]
  · rw [if_neg hz, schoolRow_eq_rowAt, mir_of_false]
    rw [rowAt_coeff x st i n t (decide (coeff y i = 2)) hc]
    have hlay := laid_tritMul (coeff y i) (coeff x (t - i)) (coeff_le_local hy i) hz
    by_cases hcond : i ≤ t ∧ t - i < n ∧ t < st.length
    · rw [if_pos hcond, hlay, if_pos hcond]
    · rw [if_neg hcond, if_neg hcond, tritAdd_zero_right _ hc]

private theorem schoolAt_coeff_mir (x y st : List Nat) (n i t : Nat)
    (hc : coeff st t ≤ 2) (hx : allTritList x) (hy : allTritList y) :
    coeff (schoolAt n x y true i st) t =
      tritAdd (coeff st t)
        (if i ≤ t ∧ t - i < n ∧ t < st.length then
          flipTrit (tritMul (coeff y i) (coeff x (t - i))) else 0) := by
  unfold schoolAt
  dsimp only
  by_cases hz : coeff y i = 0
  · rw [if_pos hz]
    have hmul : flipTrit (tritMul (coeff y i) (coeff x (t - i))) = 0 := by rw [hz]; rfl
    rw [hmul]
    have hif : (if i ≤ t ∧ t - i < n ∧ t < st.length then (0 : Nat) else 0) = 0 := by
      by_cases h : i ≤ t ∧ t - i < n ∧ t < st.length <;> simp [h]
    rw [hif, tritAdd_zero_right _ hc]
  · rw [if_neg hz, schoolRow_eq_rowAt]
    rw [rowAt_coeff x st i n t (decide (coeff y i = 2) != true) hc]
    have hd : coeff x (t - i) ≤ 2 := coeff_le_local hx (t - i)
    have hlay := laid_mirror (coeff y i) (coeff x (t - i)) (coeff_le_local hy i) hd hz
    by_cases hcond : i ≤ t ∧ t - i < n ∧ t < st.length
    · rw [if_pos hcond, hlay, if_pos hcond]
    · rw [if_neg hcond, if_neg hcond, tritAdd_zero_right _ hc]

theorem schoolDown_len (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) : ∀ k, (schoolDown first second mirror n strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by
    rw [schoolDown, schoolAt_length]
    exact schoolDown_len first second mirror n strip k

private theorem schoolDown_coeff_le (x y : List Nat) (n bench k t : Nat)
    (hy : allTritList y) :
    coeff (schoolDown x y false n (List.replicate bench 0) k) t ≤ 2 := by
  induction k generalizing t with
  | zero =>
    rw [schoolDown, coeff_replicate_zero_local]
    decide
    | succ k ih =>
    rw [schoolDown]
    rw [schoolAt_coeff x y _ n (n - (k + 1)) t (ih t) hy]
    exact tritAdd_le _ _

private theorem coeff_all_trits (xs : List Nat) (h : ∀ t, coeff xs t ≤ 2) : allTritList xs := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have ht := h i
  rwa [coeff_eq_get xs i hi] at ht

theorem school_zero_trits (n bench : Nat) (x y : List Nat) (hy : allTritList y) :
    allTritList (school n x y (List.replicate bench 0) false) := by
  apply coeff_all_trits
  intro t
  rw [← schoolDown_school]
  exact schoolDown_coeff_le x y n bench n t hy

private theorem fieldAdd_all_trits (n : Nat) (xs ys : List Nat) : allTritList (fieldAdd n xs ys) := by
  intro x hx
  simp only [fieldAdd, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  exact tritAdd_le _ _

theorem fieldAdd_at (n : Nat) (xs ys : List Nat) (i : Nat) (hi : i < n) :
    coeff (fieldAdd n xs ys) i = tritAdd (coeff xs i) (coeff ys i) := by
  have hlen : i < (fieldAdd n xs ys).length := by
    simp [fieldAdd, List.length_map, List.length_range, hi]
  rw [coeff_eq_get _ i hlen]
  simp [fieldAdd, List.getElem_map, List.getElem_range, hi]

private theorem stripAdd_coeff_local (xs ys : List Nat) (i : Nat) (hlen : ys.length = xs.length) :
    coeff (stripAdd xs ys) i = tritAdd (coeff xs i) (coeff ys i) := by
  by_cases hi : i < xs.length
  · rw [coeff_eq_get (stripAdd xs ys) i (by rw [stripAdd_length]; exact hi),
      stripAdd_get xs ys i hi]
  · rw [coeff_ge_local _ i (by rw [stripAdd_length]; exact Nat.le_of_not_gt hi),
      coeff_ge_local xs i (Nat.le_of_not_gt hi),
      coeff_ge_local ys i (by rw [hlen]; exact Nat.le_of_not_gt hi), tritAdd]

private theorem coeff_ext {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hc : ∀ t, coeff xs t = coeff ys t) : xs = ys := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi1 hi2
    have h := hc i
    rw [coeff_eq_get xs i hi1, coeff_eq_get ys i hi2] at h
    exact h

private theorem schoolDown_add_coeff (x y z : List Nat) (n bench k t : Nat)
    (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) (hk : k ≤ n) :
    coeff (schoolDown x (fieldAdd n y z) false n (List.replicate bench 0) k) t =
      tritAdd
        (coeff (schoolDown x y false n (List.replicate bench 0) k) t)
        (coeff (schoolDown x z false n (List.replicate bench 0) k) t) := by
  induction k generalizing t with
  | zero =>
    rw [schoolDown, schoolDown, schoolDown]
    simp [coeff_replicate_zero_local, tritAdd]
  | succ k ih =>
    have hiN : n - (k + 1) < n := by omega
    have hk' : k ≤ n := by omega
    have hSumLe : coeff (schoolDown x (fieldAdd n y z) false n (List.replicate bench 0) k) t ≤ 2 := by
      rw [ih t hk']
      exact tritAdd_le _ _
    have hYLe := schoolDown_coeff_le x y n bench k t hy
    have hZLe := schoolDown_coeff_le x z n bench k t hz
    have hAdd : allTritList (fieldAdd n y z) := fieldAdd_all_trits n y z
    rw [schoolDown, schoolDown, schoolDown]
    rw [schoolAt_coeff x (fieldAdd n y z)
        (schoolDown x (fieldAdd n y z) false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hSumLe hAdd]
    rw [schoolAt_coeff x y
        (schoolDown x y false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hYLe hy]
    rw [schoolAt_coeff x z
        (schoolDown x z false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hZLe hz]
    have hlenS : (schoolDown x (fieldAdd n y z) false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    have hlenY : (schoolDown x y false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    have hlenZ : (schoolDown x z false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    rw [hlenS, hlenY, hlenZ, ih t hk', fieldAdd_at n y z (n - (k + 1)) hiN]
    by_cases hcond : n - (k + 1) ≤ t ∧ t - (n - (k + 1)) < n ∧ t < bench
    · rw [if_pos hcond, if_pos hcond, if_pos hcond]
      have hdx : coeff x (t - (n - (k + 1))) ≤ 2 := coeff_le_local hx _
      have hy2 : coeff y (n - (k + 1)) ≤ 2 := coeff_le_local hy _
      have hz2 : coeff z (n - (k + 1)) ≤ 2 := coeff_le_local hz _
      rw [tritMul_add_left (coeff y (n - (k + 1))) (coeff z (n - (k + 1)))
          (coeff x (t - (n - (k + 1)))) hy2 hz2 hdx]
      exact trit_diamond
        (coeff (schoolDown x y false n (List.replicate bench 0) k) t)
        (coeff (schoolDown x z false n (List.replicate bench 0) k) t)
        (tritMul (coeff y (n - (k + 1))) (coeff x (t - (n - (k + 1)))))
        (tritMul (coeff z (n - (k + 1))) (coeff x (t - (n - (k + 1)))))
    · rw [if_neg hcond, if_neg hcond, if_neg hcond]
      rw [tritAdd_zero_right _
          (tritAdd_le (coeff (schoolDown x y false n (List.replicate bench 0) k) t)
            (coeff (schoolDown x z false n (List.replicate bench 0) k) t)),
        tritAdd_zero_right _ hYLe, tritAdd_zero_right _ hZLe]

private theorem school_right_add (n bench : Nat) (x y z : List Nat)
    (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) :
    school n x (fieldAdd n y z) (List.replicate bench 0) false =
      stripAdd
        (school n x y (List.replicate bench 0) false)
        (school n x z (List.replicate bench 0) false) := by
  rw [← schoolDown_school, ← schoolDown_school, ← schoolDown_school]
  apply coeff_ext
  · simp [schoolDown_len, List.length_replicate, stripAdd_length]
  · intro t
    rw [schoolDown_add_coeff x y z n bench n t hx hy hz (Nat.le_refl n)]
    have hlen : (schoolDown x z false n (List.replicate bench 0) n).length =
        (schoolDown x y false n (List.replicate bench 0) n).length := by
      simp [schoolDown_len]
    rw [stripAdd_coeff_local _ _ t hlen]

private theorem tritList_set_local (xs : List Nat) (h : allTritList xs) (i v : Nat)
    (hv : v ≤ 2) : allTritList (xs.set i v) := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hj' : j < xs.length := by rw [List.length_set] at hj; exact hj
  by_cases hij : i = j
  · subst hij
    rw [List.getElem_set_self]
    exact hv
  · rw [List.getElem_set, if_neg hij]
    exact h _ (List.getElem_mem hj')

private theorem foldHigh_len (n gap e : Nat) (strip : List Nat) :
    (foldHigh n gap e strip).length = strip.length := by
  unfold foldHigh
  by_cases h : coeff strip e = 0 ∨ e < n
  · simp [h]
  · simp [h, List.length_set]

private theorem foldHigh_trits (n gap e : Nat) (strip : List Nat) (hs : allTritList strip) :
    allTritList (foldHigh n gap e strip) := by
  unfold foldHigh
  by_cases hif : coeff strip e = 0 ∨ e < n
  · simpa [hif] using hs
  · simp only [hif, ite_false]
    let cleared := strip.set e 0
    have hcleared : allTritList cleared := tritList_set_local strip hs e 0 (Nat.zero_le 2)
    let once := cleared.set (e - n) (tritAdd (coeff cleared (e - n)) (coeff strip e))
    have honce : allTritList once :=
      tritList_set_local cleared hcleared (e - n) _ (tritAdd_le _ _)
    exact tritList_set_local once honce (e - gap) _ (tritAdd_le _ _)

private theorem foldr_len (n gap : Nat) (ds : List Nat) (xs : List Nat) :
    (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs).length = xs.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [foldHigh_len, ih]

private theorem foldr_trits (n gap : Nat) (ds : List Nat) (xs : List Nat)
    (ht : allTritList xs) :
    allTritList (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs) := by
  induction ds with
  | nil => exact ht
  | cons d ds ih =>
    simp only [List.foldr_cons]
    exact foldHigh_trits n gap (n + d) _ ih

/-- The high-hole update, including a zero peg. Adding zero and clearing a
    zero hole leave the strip alone, so this agrees with `foldHigh` once the
    hole sits at or above `n`. -/
def foldForm (n gap e : Nat) (xs : List Nat) : List Nat :=
  ((xs.set e 0).set (e - n)
      (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e))).set
    (e - gap)
    (tritAdd
      (coeff
        ((xs.set e 0).set (e - n)
          (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e)))
        (e - gap))
      (coeff xs e))

private theorem set_same (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.set j xs[j] = xs := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    by_cases h : i = j
    · subst h
      simp
    · simp [List.getElem_set_ne (Ne.symm h)]

private theorem set_coeff_id (xs : List Nat) (j : Nat) :
    xs.set j (coeff xs j) = xs := by
  by_cases hj : j < xs.length
  · rw [coeff_eq_get xs j hj, set_same xs j hj]
  · exact list_set_ge xs j _ (Nat.le_of_not_gt hj)

private theorem foldForm_zero (n gap e : Nat) (xs : List Nat) (ht : allTritList xs)
    (hz : coeff xs e = 0) : foldForm n gap e xs = xs := by
  unfold foldForm
  rw [hz]
  have h0 : xs.set e 0 = xs := by
    by_cases he : e < xs.length
    · have hx0 : xs[e] = 0 := by rw [← coeff_eq_get xs e he, hz]
      simpa [hx0] using set_same xs e he
    · exact list_set_ge xs e 0 (Nat.le_of_not_gt he)
  rw [h0]
  rw [tritAdd_zero_right _ (coeff_le_local ht (e - n)), set_coeff_id xs (e - n)]
  rw [tritAdd_zero_right _ (coeff_le_local ht (e - gap)), set_coeff_id xs (e - gap)]

private theorem foldHigh_form (n gap e : Nat) (xs : List Nat) (ht : allTritList xs)
    (hge : ¬ e < n) : foldHigh n gap e xs = foldForm n gap e xs := by
  unfold foldHigh
  by_cases hz : coeff xs e = 0
  · simp only [hz, true_or, ite_true]
    exact (foldForm_zero n gap e xs ht hz).symm
  · have hif : ¬ (coeff xs e = 0 ∨ e < n) := by
      intro h
      rcases h with h0 | hlt
      · exact hz h0
      · exact hge hlt
    rw [if_neg hif]
    unfold foldForm
    rfl

private theorem strip_set0 (xs ys : List Nat) (e : Nat)
    (he : e < xs.length) (hlen : ys.length = xs.length) :
    (stripAdd xs ys).set e 0 = stripAdd (xs.set e 0) (ys.set e 0) := by
  have h := stripAdd_set xs ys e 0 0 he hlen
  simpa [tritAdd] using h.symm

private theorem addBoth (xs ys : List Nat) (j a b : Nat)
    (hj : j < xs.length) (hlen : ys.length = xs.length) :
    (stripAdd xs ys).set j (tritAdd (coeff (stripAdd xs ys) j) (tritAdd a b)) =
      stripAdd
        (xs.set j (tritAdd (coeff xs j) a))
        (ys.set j (tritAdd (coeff ys j) b)) := by
  have hset := stripAdd_set xs ys j (tritAdd (coeff xs j) a) (tritAdd (coeff ys j) b) hj hlen
  have hco : tritAdd (tritAdd (coeff xs j) a) (tritAdd (coeff ys j) b) =
      tritAdd (coeff (stripAdd xs ys) j) (tritAdd a b) := by
    have hlenS : j < (stripAdd xs ys).length := by rw [stripAdd_length]; exact hj
    rw [coeff_eq_get (stripAdd xs ys) j hlenS, stripAdd_get xs ys j hj]
    exact trit_diamond (coeff xs j) a (coeff ys j) b
  rw [hco] at hset
  exact hset.symm

private theorem foldForm_lin (n gap e : Nat) (xs ys : List Nat)
    (he : e < xs.length) (hlen : ys.length = xs.length) :
    foldForm n gap e (stripAdd xs ys) =
      stripAdd (foldForm n gap e xs) (foldForm n gap e ys) := by
  have hp1 : e - n < xs.length := by omega
  have hp2 : e - gap < xs.length := by omega
  unfold foldForm
  rw [stripAdd_coeff_local xs ys e hlen, strip_set0 xs ys e he hlen]
  have hlen0 : (ys.set e 0).length = (xs.set e 0).length := by simp [List.length_set, hlen]
  have hp1s : e - n < (xs.set e 0).length := by simpa [List.length_set] using hp1
  rw [addBoth (xs.set e 0) (ys.set e 0) (e - n) (coeff xs e) (coeff ys e) hp1s hlen0]
  have hlen1 :
      ((ys.set e 0).set (e - n) (tritAdd (coeff (ys.set e 0) (e - n)) (coeff ys e))).length =
        ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e))).length := by
    simp [List.length_set, hlen]
  have hp2s : e - gap <
      ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e))).length := by
    simpa [List.length_set] using hp2
  rw [addBoth
      ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e)))
      ((ys.set e 0).set (e - n) (tritAdd (coeff (ys.set e 0) (e - n)) (coeff ys e)))
      (e - gap) (coeff xs e) (coeff ys e) hp2s hlen1]

private theorem foldHigh_lin (n gap e : Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs) (hty : allTritList ys) :
    foldHigh n gap e (stripAdd xs ys) =
      stripAdd (foldHigh n gap e xs) (foldHigh n gap e ys) := by
  by_cases hlt : e < n
  · simp [foldHigh, hlt]
  · by_cases he : e < xs.length
    · rw [foldHigh_form n gap e xs htx hlt, foldHigh_form n gap e ys hty hlt,
        foldHigh_form n gap e (stripAdd xs ys) (stripAdd_trits xs ys) hlt]
      exact foldForm_lin n gap e xs ys he hlen
    · have hcx : coeff xs e = 0 := coeff_ge_local xs e (Nat.le_of_not_gt he)
      have hcy : coeff ys e = 0 := coeff_ge_local ys e (by rw [hlen]; exact Nat.le_of_not_gt he)
      have hcs : coeff (stripAdd xs ys) e = 0 :=
        coeff_ge_local _ e (by rw [stripAdd_length]; exact Nat.le_of_not_gt he)
      simp [foldHigh, hcx, hcy, hcs]

private theorem foldrHigh_add (n gap : Nat) (ds : List Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs) (hty : allTritList ys) :
    ds.foldr (fun d st => foldHigh n gap (n + d) st) (stripAdd xs ys) =
      stripAdd
        (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs)
        (ds.foldr (fun d st => foldHigh n gap (n + d) st) ys) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact foldHigh_lin n gap (n + d) _ _ (by rw [foldr_len, foldr_len, hlen])
      (foldr_trits n gap ds xs htx) (foldr_trits n gap ds ys hty)

theorem reduceStrip_add (n gap : Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs) (hty : allTritList ys) :
    reduceStrip n gap (stripAdd xs ys) =
      stripAdd (reduceStrip n gap xs) (reduceStrip n gap ys) := by
  unfold reduceStrip
  rw [stripAdd_length, hlen]
  exact foldrHigh_add n gap (List.range (xs.length - n)) xs ys hlen htx hty

private theorem reduceStrip_len (n gap : Nat) (xs : List Nat) :
    (reduceStrip n gap xs).length = xs.length := by
  unfold reduceStrip
  exact foldr_len n gap (List.range (xs.length - n)) xs

theorem fieldAdd_assoc (n : Nat) (a b c : List Nat) :
    fieldAdd n (fieldAdd n a b) c = fieldAdd n a (fieldAdd n b c) := by
  apply coeff_ext
  · simp [fieldAdd, List.length_map, List.length_range]
  · intro t
    by_cases ht : t < n
    · rw [fieldAdd_at n (fieldAdd n a b) c t ht, fieldAdd_at n a b t ht,
        fieldAdd_at n a (fieldAdd n b c) t ht, fieldAdd_at n b c t ht, tritAdd_assoc]
    · rw [coeff_ge_local _ t (by simp [fieldAdd, List.length_map, List.length_range]; omega),
        coeff_ge_local _ t (by simp [fieldAdd, List.length_map, List.length_range]; omega)]

private theorem fieldAdd_take_left (n : Nat) (xs ys : List Nat) (hn : n ≤ xs.length) :
    fieldAdd n (xs.take n) ys = fieldAdd n xs ys := by
  apply fieldAdd_coeff
  · intro i hi
    have hi' : i < (xs.take n).length := by
      rw [List.length_take, Nat.min_eq_left hn]
      exact hi
    rw [coeff_eq_get _ i hi', List.getElem_take, ← coeff_eq_get xs i (by omega)]
  · intro _ _
    rfl

private theorem fieldAdd_take_both (n : Nat) (xs ys : List Nat)
    (hx : n ≤ xs.length) (hy : n ≤ ys.length) :
    fieldAdd n xs ys = fieldAdd n (xs.take n) (ys.take n) := by
  rw [← fieldAdd_take_left n xs ys hx, ← fieldAdd_right_take n (xs.take n) ys hy]

/-- Right distributivity. The schoolbook's second factor is the one the card
    adds before multiplying. -/
theorem fieldMul_right_add (n k bench : Nat) (x y z : List Nat)
    (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) (hn : n ≤ bench) :
    fieldMul n k bench x (fieldAdd n y z) =
      fieldAdd n (fieldMul n k bench x y) (fieldMul n k bench x z) := by
  unfold fieldMul
  rw [school_right_add n bench x y z hx hy hz]
  have htY : allTritList (school n x y (List.replicate bench 0) false) :=
    school_zero_trits n bench x y hy
  have htZ : allTritList (school n x z (List.replicate bench 0) false) :=
    school_zero_trits n bench x z hz
  have hlen : (school n x z (List.replicate bench 0) false).length =
      (school n x y (List.replicate bench 0) false).length := by
    simp [school_length, List.length_replicate]
  rw [reduceStrip_add n (n - k) (school n x y (List.replicate bench 0) false)
      (school n x z (List.replicate bench 0) false) hlen htY htZ]
  have hlenR : n ≤ (reduceStrip n (n - k) (school n x y (List.replicate bench 0) false)).length := by
    rw [reduceStrip_len, school_length, List.length_replicate]
    exact hn
  have hlenS : n ≤ (reduceStrip n (n - k) (school n x z (List.replicate bench 0) false)).length := by
    rw [reduceStrip_len, school_length, List.length_replicate]
    exact hn
  rw [stripAdd_take n _ _ hlenR, fieldAdd_take_both n _ _ hlenR hlenS]

private theorem map_flip_coeff (xs : List Nat) (t : Nat) :
    coeff (xs.map flipTrit) t = flipTrit (coeff xs t) := by
  by_cases ht : t < xs.length
  · rw [coeff_eq_get _ t (by simp; exact ht), List.getElem_map, coeff_eq_get xs t ht]
  · rw [coeff_ge_local _ t (by simp; exact Nat.le_of_not_gt ht),
      coeff_ge_local xs t (Nat.le_of_not_gt ht), flipTrit]
    simp

private theorem schoolDown_mirror_coeff (x y : List Nat) (n bench k t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    coeff (schoolDown x y true n (List.replicate bench 0) k) t =
      flipTrit (coeff (schoolDown x y false n (List.replicate bench 0) k) t) := by
  induction k generalizing t with
  | zero =>
    rw [schoolDown, schoolDown]
    simp [coeff_replicate_zero_local, flipTrit]
  | succ k ih =>
    have hYLe := schoolDown_coeff_le x y n bench k t hy
    have hMLe : coeff (schoolDown x y true n (List.replicate bench 0) k) t ≤ 2 := by
      rw [ih t]
      exact flipTrit_le _
    rw [schoolDown, schoolDown]
    rw [schoolAt_coeff_mir x y (schoolDown x y true n (List.replicate bench 0) k)
        n (n - (k + 1)) t hMLe hx hy]
    rw [schoolAt_coeff x y (schoolDown x y false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hYLe hy]
    have hlenM : (schoolDown x y true n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    have hlen : (schoolDown x y false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    rw [hlenM, hlen, ih t]
    by_cases hcond : n - (k + 1) ≤ t ∧ t - (n - (k + 1)) < n ∧ t < bench
    · rw [if_pos hcond, if_pos hcond]
      have hdx : coeff x (t - (n - (k + 1))) ≤ 2 := coeff_le_local hx _
      have hy2 : coeff y (n - (k + 1)) ≤ 2 := coeff_le_local hy _
      have hprod : tritMul (coeff y (n - (k + 1)))
          (coeff x (t - (n - (k + 1)))) ≤ 2 := tritMul_le _ _ hy2 hdx
      rw [flipTrit_add
          (coeff (schoolDown x y false n (List.replicate bench 0) k) t)
          (tritMul (coeff y (n - (k + 1))) (coeff x (t - (n - (k + 1)))))
          hYLe hprod]
    · rw [if_neg hcond, if_neg hcond, tritAdd_zero_right _ (flipTrit_le _),
        tritAdd_zero_right _ hYLe]

/-- A mirrored schoolbook on a zero strip is the colour flip of the plain one. -/
theorem school_mirror (n bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    school n x y (List.replicate bench 0) true =
      (school n x y (List.replicate bench 0) false).map flipTrit := by
  apply coeff_ext
  · simp [school_length, List.length_replicate, List.length_map]
  · intro t
    rw [← schoolDown_school, ← schoolDown_school,
      schoolDown_mirror_coeff x y n bench n t hx hy, map_flip_coeff]

private theorem schoolDown_flip_coeff (x y : List Nat) (n bench k t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    coeff (schoolDown (mirrorTrits x) y false n (List.replicate bench 0) k) t =
      flipTrit (coeff (schoolDown x y false n (List.replicate bench 0) k) t) := by
  induction k generalizing t with
  | zero =>
    rw [schoolDown, schoolDown]
    simp [coeff_replicate_zero_local, flipTrit]
  | succ k ih =>
    have hYLe := schoolDown_coeff_le x y n bench k t hy
    have hMLe : coeff (schoolDown (mirrorTrits x) y false n (List.replicate bench 0) k) t ≤ 2 := by
      rw [ih t]
      exact flipTrit_le _
    rw [schoolDown, schoolDown]
    rw [schoolAt_coeff (mirrorTrits x) y
        (schoolDown (mirrorTrits x) y false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hMLe hy]
    rw [schoolAt_coeff x y (schoolDown x y false n (List.replicate bench 0) k)
        n (n - (k + 1)) t hYLe hy]
    have hlenM : (schoolDown (mirrorTrits x) y false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    have hlen : (schoolDown x y false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len, List.length_replicate]
    rw [hlenM, hlen, ih t, mirrorTrits_map, map_flip_coeff]
    by_cases hcond : n - (k + 1) ≤ t ∧ t - (n - (k + 1)) < n ∧ t < bench
    · rw [if_pos hcond, if_pos hcond]
      have hdx : coeff x (t - (n - (k + 1))) ≤ 2 := coeff_le_local hx _
      have hy2 : coeff y (n - (k + 1)) ≤ 2 := coeff_le_local hy _
      rw [← flipTrit_mul (coeff y (n - (k + 1))) (coeff x (t - (n - (k + 1)))) hy2 hdx]
      exact (flipTrit_add
        (coeff (schoolDown x y false n (List.replicate bench 0) k) t)
        (tritMul (coeff y (n - (k + 1))) (coeff x (t - (n - (k + 1)))))
        hYLe (tritMul_le _ _ hy2 hdx)).symm
    · rw [if_neg hcond, if_neg hcond, tritAdd_zero_right _ (flipTrit_le _),
        tritAdd_zero_right _ hYLe]

private theorem school_flip_left (n bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    school n (mirrorTrits x) y (List.replicate bench 0) false =
      (school n x y (List.replicate bench 0) false).map flipTrit := by
  apply coeff_ext
  · simp [school_length, List.length_replicate, List.length_map]
  · intro t
    rw [← schoolDown_school, ← schoolDown_school,
      schoolDown_flip_coeff x y n bench n t hx hy, map_flip_coeff]

private theorem map_set_flip (xs : List Nat) (i v : Nat) :
    (xs.set i v).map flipTrit = (xs.map flipTrit).set i (flipTrit v) := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    by_cases h : i = j
    · subst h
      simp [List.getElem_map, List.getElem_set_self]
    · simp [List.getElem_map, List.getElem_set, h]

private theorem map_flip_trits (xs : List Nat) : allTritList (xs.map flipTrit) := by
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  exact flipTrit_le _

private theorem foldForm_flip (n gap e : Nat) (xs : List Nat) (ht : allTritList xs) :
    foldForm n gap e (xs.map flipTrit) = (foldForm n gap e xs).map flipTrit := by
  have hc : coeff xs e ≤ 2 := coeff_le_local ht e
  let xs0 := xs.set e 0
  have ht0 : allTritList xs0 := tritList_set_local xs ht e 0 (Nat.zero_le 2)
  let p1 := e - n
  let p2 := e - gap
  let v1 := tritAdd (coeff xs0 p1) (coeff xs e)
  have hv1 : v1 ≤ 2 := tritAdd_le _ _
  let xs1 := xs0.set p1 v1
  have ht1 : allTritList xs1 := tritList_set_local xs0 ht0 p1 v1 hv1
  let v2 := tritAdd (coeff xs1 p2) (coeff xs e)
  have hxs : foldForm n gap e xs = xs1.set p2 v2 := by
    unfold foldForm
    rfl
  have hys : foldForm n gap e (xs.map flipTrit) =
      (((xs.map flipTrit).set e 0).set p1
          (tritAdd (coeff ((xs.map flipTrit).set e 0) p1) (flipTrit (coeff xs e)))).set p2
        (tritAdd
          (coeff (((xs.map flipTrit).set e 0).set p1
              (tritAdd (coeff ((xs.map flipTrit).set e 0) p1) (flipTrit (coeff xs e)))) p2)
          (flipTrit (coeff xs e))) := by
    unfold foldForm
    rw [map_flip_coeff]
  rw [hxs, hys, map_set_flip xs1 p2 v2]
  have hv2 : flipTrit v2 = tritAdd (flipTrit (coeff xs1 p2)) (flipTrit (coeff xs e)) :=
    flipTrit_add _ _ (coeff_le_local ht1 p2) hc
  rw [hv2, ← map_flip_coeff xs1 p2, map_set_flip xs0 p1 v1]
  have hv1f : flipTrit v1 = tritAdd (flipTrit (coeff xs0 p1)) (flipTrit (coeff xs e)) :=
    flipTrit_add _ _ (coeff_le_local ht0 p1) hc
  rw [hv1f, ← map_flip_coeff xs0 p1, map_set_flip xs e 0]
  rw [show flipTrit 0 = 0 by simp [flipTrit]]

private theorem foldHigh_flip (n gap e : Nat) (xs : List Nat) (ht : allTritList xs) :
    foldHigh n gap e (xs.map flipTrit) = (foldHigh n gap e xs).map flipTrit := by
  by_cases hlt : e < n
  · simp [foldHigh, hlt]
  · rw [foldHigh_form n gap e xs ht hlt,
      foldHigh_form n gap e (xs.map flipTrit) (map_flip_trits xs) hlt]
    exact foldForm_flip n gap e xs ht

private theorem foldr_flip (n gap : Nat) (ds : List Nat) (xs : List Nat) (ht : allTritList xs) :
    ds.foldr (fun d st => foldHigh n gap (n + d) st) (xs.map flipTrit) =
      (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs).map flipTrit := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact foldHigh_flip n gap (n + d) _ (foldr_trits n gap ds xs ht)

theorem reduceStrip_flip (n gap : Nat) (xs : List Nat) (ht : allTritList xs) :
    reduceStrip n gap (xs.map flipTrit) = (reduceStrip n gap xs).map flipTrit := by
  unfold reduceStrip
  rw [List.length_map]
  exact foldr_flip n gap (List.range (xs.length - n)) xs ht

/-- Negating the first factor negates the product. -/
theorem fieldMul_mirror_left (n k bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    fieldMul n k bench (mirrorTrits x) y = mirrorTrits (fieldMul n k bench x y) := by
  unfold fieldMul
  rw [school_flip_left n bench x y hx hy, reduceStrip_flip n (n - k)
      (school n x y (List.replicate bench 0) false) (school_zero_trits n bench x y hy),
    ← List.map_take, ← mirrorTrits_map]

theorem mirrorTrits_fieldAdd (n : Nat) (xs ys : List Nat)
    (hx : allTritList xs) (hy : allTritList ys) :
    mirrorTrits (fieldAdd n xs ys) = fieldAdd n (mirrorTrits xs) (mirrorTrits ys) := by
  apply coeff_ext
  · simp [mirrorTrits, fieldAdd, List.length_map, List.length_range]
  · intro t
    by_cases ht : t < n
    · rw [mirrorTrits_map, map_flip_coeff, fieldAdd_at n xs ys t ht,
        flipTrit_add _ _ (coeff_le_local hx t) (coeff_le_local hy t),
        fieldAdd_at n (mirrorTrits xs) (mirrorTrits ys) t ht,
        mirrorTrits_map, mirrorTrits_map, map_flip_coeff, map_flip_coeff]
    · rw [coeff_ge_local _ t (by simp [mirrorTrits, fieldAdd, List.length_map, List.length_range]; omega),
        coeff_ge_local _ t (by simp [fieldAdd, List.length_map, List.length_range]; omega)]

theorem mirrorTrits_invol (xs : List Nat) (ht : allTritList xs) :
    mirrorTrits (mirrorTrits xs) = xs := by
  rw [mirrorTrits_map, mirrorTrits_map, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp
    have hi0 : i < xs.length := by simpa using hi
    exact flipTrit_invol _ (ht _ (List.getElem_mem hi0))

end EcbsLink2.Link2
