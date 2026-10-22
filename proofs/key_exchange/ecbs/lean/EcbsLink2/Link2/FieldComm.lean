/-
  `Spec.fieldMul` is the schoolbook product reduced by the lane fold.
  SPEC.md §3 R7 line 156 names the chord slope as "rise over run", which
  `Spec.chordAdd` multiplies as `fieldMul rise inv`. The same line's card says
  "do the gap times the spare": the gap holds the inverse and the spare holds
  the rise, so the emitted product is `fieldMul inv rise`. Those are the same
  list. The argument order in `Spec.chordAdd` stays the algebraic one.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.School

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- GF(3) product. An empty peg is zero; a red peg (`2`) negates. -/
def tritMul (a b : Nat) : Nat :=
  if a = 0 then 0 else if a = 2 then flipTrit b else b

/-- What one schoolbook cell lays. A red outer peg negates the inner trit. -/
def laidTrit (d : Nat) (mir : Bool) : Nat :=
  if mir then flipTrit d else d

theorem tritAdd_comm (a b : Nat) : tritAdd a b = tritAdd b a := by
  simp [tritAdd, Nat.add_comm]

theorem tritAdd_assoc (a b c : Nat) :
    tritAdd (tritAdd a b) c = tritAdd a (tritAdd b c) := by
  simp only [tritAdd]
  rw [Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_mod_mod]

theorem tritAdd_zero_left (a : Nat) (ha : a ≤ 2) : tritAdd 0 a = a := by
  simp [tritAdd]; omega

theorem tritAdd_zero_right (a : Nat) (ha : a ≤ 2) : tritAdd a 0 = a := by
  simp [tritAdd]; omega

private theorem tritAdd_le_local (a b : Nat) : tritAdd a b ≤ 2 := by
  simp [tritAdd]; omega

private theorem trit_cycle (a b c : Nat) :
    tritAdd (tritAdd a b) c = tritAdd (tritAdd a c) b := by
  rw [tritAdd_assoc, tritAdd_comm b c, ← tritAdd_assoc]

private theorem trit_diamond_local (a b c d : Nat) :
    tritAdd (tritAdd a b) (tritAdd c d) = tritAdd (tritAdd a c) (tritAdd b d) := by
  rw [tritAdd_assoc, ← tritAdd_assoc b, tritAdd_comm b c, tritAdd_assoc, ← tritAdd_assoc]

theorem tritMul_le (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) : tritMul a b ≤ 2 := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;>
    simp [tritMul, flipTrit]

theorem tritMul_comm (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) : tritMul a b = tritMul b a := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;>
    simp [tritMul, flipTrit]

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
  · have hlen : t < (List.replicate bench 0).length := by simpa using ht
    rw [coeff_eq_get _ t hlen, List.getElem_replicate]
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
        exact tritAdd_le_local _ _
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

private theorem schoolAt_len (n : Nat) (first second : List Nat) (mirror : Bool)
    (i : Nat) (st : List Nat) :
    (schoolAt n first second mirror i st).length = st.length := by
  unfold schoolAt
  dsimp only
  split
  · rfl
  · rw [schoolRow_eq_rowAt, rowAt_len]

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

private theorem schoolDown_len_local (first second : List Nat) (mirror : Bool) (n : Nat)
    (strip : List Nat) : ∀ k, (schoolDown first second mirror n strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by
    rw [show schoolDown first second mirror n strip (k + 1) =
        schoolAt n first second mirror (n - (k + 1))
          (schoolDown first second mirror n strip k) from rfl,
      schoolAt_len, schoolDown_len_local first second mirror n strip k]

/-- Sum `f 0`, then `f 1`, through `f (n - 1)`, in GF(3). -/
def tritSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => tritAdd (tritSum f n) (f n)

private theorem tritSum_le (f : Nat → Nat) (n : Nat) : tritSum f n ≤ 2 := by
  induction n with
  | zero => simp [tritSum]
  | succ n ih =>
    rw [tritSum]
    exact tritAdd_le_local _ _

private theorem tritSum_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i, i < n → f i = g i) : tritSum f n = tritSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tritSum, tritSum, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self _)]

private theorem tritSum_zero_fun (n : Nat) : tritSum (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tritSum, ih, tritAdd_zero_left 0 (by decide)]

private theorem tritSum_rot (f : Nat → Nat) (n : Nat) :
    tritSum f (n + 1) = tritAdd (f 0) (tritSum (fun i => f (i + 1)) n) := by
  induction n with
  | zero => simp [tritSum, tritAdd_comm]
  | succ n ih =>
    rw [tritSum, ih, tritSum, ← tritAdd_assoc]

/-- The sum is unchanged when its summands are read from the high index down. -/
private theorem tritSum_revGen (f : Nat → Nat) (start len : Nat) :
    tritSum (fun i => f (start + i)) len =
      tritSum (fun j => f (start + len - 1 - j)) len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
    have hrot := tritSum_rot (fun i => f (start + i)) len
    rw [hrot, tritSum]
    have hlast : start + (len + 1) - 1 - len = start := by omega
    have h0 : start + 0 = start := by omega
    simp only [hlast, h0]
    have hsumL :
        tritSum (fun i => f (start + (i + 1))) len =
          tritSum (fun i => f ((start + 1) + i)) len := by
      apply tritSum_congr
      intro i _
      have : start + (i + 1) = (start + 1) + i := by omega
      rw [this]
    rw [hsumL]
    rw [ih (start + 1)]
    have hsumR :
        tritSum (fun j => f (start + 1 + len - 1 - j)) len =
          tritSum (fun j => f (start + (len + 1) - 1 - j)) len := by
      apply tritSum_congr
      intro j hj
      have : start + 1 + len - 1 - j = start + (len + 1) - 1 - j := by omega
      rw [this]
    rw [hsumR, tritAdd_comm]

private theorem tritSum_reverse (f : Nat → Nat) (n : Nat) :
    tritSum f n = tritSum (fun j => f (n - 1 - j)) n := by
  have h := tritSum_revGen f 0 n
  have hL : tritSum (fun i => f (0 + i)) n = tritSum f n := by
    apply tritSum_congr
    intro i _
    simp
  have hR : tritSum (fun j => f (0 + n - 1 - j)) n =
      tritSum (fun j => f (n - 1 - j)) n := by
    apply tritSum_congr
    intro j _
    simp
  rw [← hL, h, hR]

private theorem tritSum_pointwise (f g : Nat → Nat) (n : Nat) :
    tritSum (fun i => tritAdd (f i) (g i)) n = tritAdd (tritSum f n) (tritSum g n) := by
  induction n with
  | zero => simp [tritSum, tritAdd]
  | succ n ih =>
    rw [tritSum, tritSum, tritSum, ih]
    exact trit_diamond_local _ _ _ _

private theorem tritSum_spike (n j v : Nat) (hj : j < n) (hv : v ≤ 2) :
    tritSum (fun i => if i = j then v else 0) n = v := by
  induction n with
  | zero => cases hj
  | succ n ih =>
    rw [tritSum]
    by_cases hjn : j < n
    · have hne : n ≠ j := Nat.ne_of_gt hjn
      rw [if_neg hne, tritAdd_zero_right _ (by
        rw [ih hjn]; exact hv), ih hjn]
    · have hn : n = j := by omega
      rw [hn, if_pos rfl]
      have hpre : tritSum (fun i => if i = j then v else 0) j = 0 := by
        have hfun : tritSum (fun i => if i = j then v else 0) j =
            tritSum (fun _ => 0) j := by
          apply tritSum_congr
          intro i hi
          simp [Nat.ne_of_lt hi]
        rw [hfun]
        exact tritSum_zero_fun j
      rw [hpre, tritAdd_zero_left _ hv]

/-- One outer index of the length-`bound` product, at hole `t`. -/
def boxTerm (x y : List Nat) (bound t i : Nat) : Nat :=
  if i ≤ t ∧ t - i < bound then tritMul (coeff y i) (coeff x (t - i)) else 0

def boxSum (x y : List Nat) (n t : Nat) : Nat :=
  tritSum (fun i => boxTerm x y n t i) n

/-- The pair that enters the box when the bound grows: outer index `t - n`. -/
def borderTerm (x y : List Nat) (n t : Nat) : Nat :=
  if n ≤ t ∧ t - n < n then tritMul (coeff y (t - n)) (coeff x n) else 0

/-- The new outer index `n` itself. -/
def freshTerm (x y : List Nat) (n t : Nat) : Nat :=
  boxTerm x y (n + 1) t n

private theorem boxTerm_le (x y : List Nat) (bound t i : Nat)
    (hx : allTritList x) (hy : allTritList y) : boxTerm x y bound t i ≤ 2 := by
  unfold boxTerm
  by_cases h : i ≤ t ∧ t - i < bound
  · simp only [h, ite_true]
    exact tritMul_le _ _ (coeff_le_local hy i) (coeff_le_local hx (t - i))
  · simp only [h, ite_false]
    omega

private theorem boxTerm_raise (x y : List Nat) (n t i : Nat) (hi : i < n)
    (hx : allTritList x) (hy : allTritList y) :
    boxTerm x y (n + 1) t i =
      tritAdd (boxTerm x y n t i)
        (if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) := by
  by_cases h : n ≤ t ∧ i = t - n ∧ t - n < n
  · rcases h with ⟨hnt, hiEq, hlt⟩
    have hsub : t - i = n := by rw [hiEq]; exact Nat.sub_sub_self hnt
    have hle : i ≤ t := by rw [hiEq]; exact Nat.sub_le _ _
    have hlt1 : t - i < n + 1 := by rw [hsub]; exact Nat.lt_succ_self n
    have hnot : ¬ (i ≤ t ∧ t - i < n) := by
      intro hc
      rw [hsub] at hc
      exact Nat.lt_irrefl n hc.2
    unfold boxTerm
    have hpos : n ≤ t ∧ i = t - n ∧ t - n < n := ⟨hnt, hiEq, hlt⟩
    rw [if_neg hnot, if_pos ⟨hle, hlt1⟩, hsub, if_pos hpos]
    exact (tritAdd_zero_left _ (tritMul_le _ _ (coeff_le_local hy i) (coeff_le_local hx n))).symm
  · have hdelta :
        (if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) = 0 := by
      rw [if_neg h]
    rw [hdelta, tritAdd_zero_right _ (boxTerm_le x y n t i hx hy)]
    unfold boxTerm
    by_cases hle : i ≤ t
    · by_cases hltn : t - i < n
      · have hlt1 : t - i < n + 1 := Nat.lt_trans hltn (Nat.lt_succ_self n)
        simp only [hle, hltn, hlt1, ite_true]
      · by_cases hlt1 : t - i < n + 1
        · have heq : t - i = n := by omega
          have hnt : n ≤ t := by omega
          have hiEq : i = t - n := by omega
          have hlt : t - n < n := by rw [← hiEq]; exact hi
          exact absurd ⟨hnt, hiEq, hlt⟩ h
        · simp only [hle, hltn, hlt1, ite_false]
    · simp only [hle, false_and, ite_false]

private theorem tritSum_delta (x y : List Nat) (n t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    tritSum (fun i =>
        if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) n =
      borderTerm x y n t := by
  unfold borderTerm
  by_cases h : n ≤ t ∧ t - n < n
  · rcases h with ⟨hnt, hlt⟩
    have hv : tritMul (coeff y (t - n)) (coeff x n) ≤ 2 :=
      tritMul_le _ _ (coeff_le_local hy (t - n)) (coeff_le_local hx n)
    have hspike := tritSum_spike n (t - n)
      (tritMul (coeff y (t - n)) (coeff x n)) hlt hv
    have hfun : tritSum (fun i =>
          if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) n =
        tritSum (fun i => if i = t - n then tritMul (coeff y (t - n)) (coeff x n) else 0) n := by
      apply tritSum_congr
      intro i hi
      by_cases he : i = t - n
      · simp [he, hnt, hlt]
      · simp [he]
    rw [hfun, hspike, if_pos ⟨hnt, hlt⟩]
  · have hfun : tritSum (fun i =>
        if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) n = 0 := by
      have hzero : tritSum (fun i =>
          if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0) n =
          tritSum (fun _ => 0) n := by
        apply tritSum_congr
        intro i _
        rw [if_neg (by
          intro hc
          exact h ⟨hc.1, hc.2.2⟩)]
      rw [hzero]
      exact tritSum_zero_fun n
    rw [hfun, if_neg h]

private theorem boxSum_succ (x y : List Nat) (n t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    boxSum x y (n + 1) t =
      tritAdd (tritAdd (boxSum x y n t) (borderTerm x y n t)) (freshTerm x y n t) := by
  unfold boxSum freshTerm
  rw [tritSum]
  have hprefix :
      tritSum (fun i => boxTerm x y (n + 1) t i) n =
        tritAdd (tritSum (fun i => boxTerm x y n t i) n) (borderTerm x y n t) := by
    have hraise :
        tritSum (fun i => boxTerm x y (n + 1) t i) n =
          tritSum (fun i => tritAdd (boxTerm x y n t i)
            (if n ≤ t ∧ i = t - n ∧ t - n < n then tritMul (coeff y i) (coeff x n) else 0)) n := by
      apply tritSum_congr
      intro i hi
      exact boxTerm_raise x y n t i hi hx hy
    rw [hraise, tritSum_pointwise, tritSum_delta x y n t hx hy]
  rw [hprefix]

private theorem border_fresh_swap (x y : List Nat) (n t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    tritAdd (borderTerm x y n t) (freshTerm x y n t) =
      tritAdd (borderTerm y x n t) (freshTerm y x n t) := by
  by_cases hnt : n ≤ t
  · by_cases hlow : t - n < n
    · have hlt1 : t - n < n + 1 := Nat.lt_succ_of_lt hlow
      have hBxy : borderTerm x y n t = tritMul (coeff y (t - n)) (coeff x n) := by
        unfold borderTerm
        simp [hnt, hlow]
      have hByx : borderTerm y x n t = tritMul (coeff x (t - n)) (coeff y n) := by
        unfold borderTerm
        simp [hnt, hlow]
      have hFxy : freshTerm x y n t = tritMul (coeff y n) (coeff x (t - n)) := by
        unfold freshTerm boxTerm
        simp [hnt, hlt1]
      have hFyx : freshTerm y x n t = tritMul (coeff x n) (coeff y (t - n)) := by
        unfold freshTerm boxTerm
        simp [hnt, hlt1]
      rw [hBxy, hByx, hFxy, hFyx,
        tritMul_comm (coeff y (t - n)) (coeff x n) (coeff_le_local hy _) (coeff_le_local hx _),
        tritMul_comm (coeff y n) (coeff x (t - n)) (coeff_le_local hy _) (coeff_le_local hx _)]
      exact tritAdd_comm _ _
    · by_cases hmid : t - n < n + 1
      · have heq : t - n = n := by omega
        have hBxy : borderTerm x y n t = 0 := by
          unfold borderTerm
          simp [hnt, hlow]
        have hByx : borderTerm y x n t = 0 := by
          unfold borderTerm
          simp [hnt, hlow]
        have hFxy : freshTerm x y n t = tritMul (coeff y n) (coeff x (t - n)) := by
          unfold freshTerm boxTerm
          simp [hnt, hmid]
        have hFyx : freshTerm y x n t = tritMul (coeff x n) (coeff y (t - n)) := by
          unfold freshTerm boxTerm
          simp [hnt, hmid]
        rw [hBxy, hByx, hFxy, hFyx, heq,
          tritAdd_zero_left _ (tritMul_le _ _ (coeff_le_local hy n) (coeff_le_local hx n)),
          tritAdd_zero_left _ (tritMul_le _ _ (coeff_le_local hx n) (coeff_le_local hy n))]
        exact tritMul_comm (coeff y n) (coeff x n) (coeff_le_local hy n) (coeff_le_local hx n)
      · have hBxy : borderTerm x y n t = 0 := by
          unfold borderTerm
          simp [hnt, hlow]
        have hByx : borderTerm y x n t = 0 := by
          unfold borderTerm
          simp [hnt, hlow]
        have hFxy : freshTerm x y n t = 0 := by
          unfold freshTerm boxTerm
          simp [hnt, hmid]
        have hFyx : freshTerm y x n t = 0 := by
          unfold freshTerm boxTerm
          simp [hnt, hmid]
        simp [hBxy, hByx, hFxy, hFyx, tritAdd]
  · have hBxy : borderTerm x y n t = 0 := by
      unfold borderTerm
      simp [hnt]
    have hByx : borderTerm y x n t = 0 := by
      unfold borderTerm
      simp [hnt]
    have hFxy : freshTerm x y n t = 0 := by
      unfold freshTerm boxTerm
      simp [hnt]
    have hFyx : freshTerm y x n t = 0 := by
      unfold freshTerm boxTerm
      simp [hnt]
    simp [hBxy, hByx, hFxy, hFyx, tritAdd]

/-- The convolution is symmetric in the two factors. -/
theorem boxSum_comm (x y : List Nat) (n t : Nat)
    (hx : allTritList x) (hy : allTritList y) :
    boxSum x y n t = boxSum y x n t := by
  induction n with
  | zero =>
    unfold boxSum tritSum
    rfl
  | succ n ih =>
    rw [boxSum_succ x y n t hx hy, boxSum_succ y x n t hy hx, ih, tritAdd_assoc, tritAdd_assoc,
      border_fresh_swap x y n t hx hy]

/-- Contribution of outer index `i` at hole `t`, dropped once `t` leaves the strip. -/
def rowHit (x y : List Nat) (n bench t i : Nat) : Nat :=
  if i ≤ t ∧ t - i < n ∧ t < bench then tritMul (coeff y i) (coeff x (t - i)) else 0

private theorem rowHit_guard (x y : List Nat) (n bench t i : Nat) :
    rowHit x y n bench t i = if t < bench then boxTerm x y n t i else 0 := by
  unfold rowHit boxTerm
  by_cases ht : t < bench
  · by_cases h : i ≤ t ∧ t - i < n
    · simp [ht, h]
    · simp [ht, h]
  · simp [ht]

private theorem tritSum_guard {p : Prop} [Decidable p] (f : Nat → Nat) (n : Nat) :
    tritSum (fun i => if p then f i else 0) n = if p then tritSum f n else 0 := by
  induction n with
  | zero =>
    by_cases hp : p <;> simp [tritSum, hp]
  | succ n ih =>
    rw [tritSum, ih]
    by_cases hp : p
    · simp [hp, tritSum]
    · simp [hp, tritAdd]

private theorem rowHit_sum (x y : List Nat) (n bench t : Nat) :
    tritSum (fun i => rowHit x y n bench t i) n =
      if t < bench then boxSum x y n t else 0 := by
  have hfun : tritSum (fun i => rowHit x y n bench t i) n =
      tritSum (fun i => if t < bench then boxTerm x y n t i else 0) n := by
    apply tritSum_congr
    intro i _
    exact rowHit_guard x y n bench t i
  rw [hfun, tritSum_guard, boxSum]

private theorem schoolDown_coeff (x y : List Nat) (n bench t k : Nat)
    (hy : allTritList y) (hk : k ≤ n) :
    coeff (schoolDown x y false n (List.replicate bench 0) k) t =
      tritSum (fun j => rowHit x y n bench t (n - 1 - j)) k := by
  induction k with
  | zero =>
    rw [show schoolDown x y false n (List.replicate bench 0) 0 =
        List.replicate bench 0 from rfl, tritSum, coeff_replicate_zero_local]
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hrec : schoolDown x y false n (List.replicate bench 0) (k + 1) =
        schoolAt n x y false (n - (k + 1))
          (schoolDown x y false n (List.replicate bench 0) k) := rfl
    rw [hrec]
    have hlen : (schoolDown x y false n (List.replicate bench 0) k).length = bench := by
      rw [schoolDown_len_local, List.length_replicate]
    have hc : coeff (schoolDown x y false n (List.replicate bench 0) k) t ≤ 2 := by
      rw [ih hk']
      exact tritSum_le _ _
    have hAt := schoolAt_coeff x y (schoolDown x y false n (List.replicate bench 0) k)
      n (n - (k + 1)) t hc hy
    rw [hlen] at hAt
    rw [hAt, ih hk', tritSum]
    have hidx : n - (k + 1) = n - 1 - k := by omega
    unfold rowHit
    rw [← hidx]

private theorem coeff_ext {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hc : ∀ t, coeff xs t = coeff ys t) : xs = ys := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi1 hi2
    have h := hc i
    rw [coeff_eq_get xs i hi1, coeff_eq_get ys i hi2] at h
    exact h

/-- The unreduced schoolbook strip does not depend on which factor is laid. -/
theorem school_comm (n bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    school n x y (List.replicate bench 0) false =
      school n y x (List.replicate bench 0) false := by
  apply coeff_ext
  · rw [school_length, school_length]
  · intro t
    rw [← schoolDown_school x y (List.replicate bench 0) false n,
      ← schoolDown_school y x (List.replicate bench 0) false n,
      schoolDown_coeff x y n bench t n hy (Nat.le_refl n),
      schoolDown_coeff y x n bench t n hx (Nat.le_refl n)]
    rw [← tritSum_reverse (fun i => rowHit x y n bench t i) n,
      ← tritSum_reverse (fun i => rowHit y x n bench t i) n,
      rowHit_sum x y n bench t, rowHit_sum y x n bench t]
    by_cases ht : t < bench
    · simp only [ht, ite_true]
      exact boxSum_comm x y n t hx hy
    · simp only [ht, ite_false]

/-- SPEC.md §3 R7 line 156. `Spec.chordAdd` multiplies rise by inverse.
    The card on that line multiplies the gap by the spare, which is inverse
    by rise. The products are equal. -/
theorem fieldMul_comm (n k bench : Nat) (x y : List Nat)
    (hx : allTritList x) (hy : allTritList y) :
    fieldMul n k bench x y = fieldMul n k bench y x := by
  unfold fieldMul
  rw [school_comm n bench x y hx hy]

/-- The chord slope in either argument order. SPEC.md §3 R7 line 156. -/
theorem slope_mul_swap (n k bench : Nat) (rise inv : List Nat)
    (hr : allTritList rise) (hi : allTritList inv) :
    fieldMul n k bench rise inv = fieldMul n k bench inv rise :=
  fieldMul_comm n k bench rise inv hr hi

end EcbsLink2.Link2
