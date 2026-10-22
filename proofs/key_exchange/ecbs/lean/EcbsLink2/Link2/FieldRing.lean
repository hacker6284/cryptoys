/-
  `fieldMul` is associative, and the one-peg is a unit. The lane fold is
  reduction by `X^n = 1 + X^k`, so a product reduced either way is the same
  remainder. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldNeg

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- The remainder of `c · X^e` modulo `X^n − X^k − 1`. `k < n`, so both
    images of a high power sit strictly lower. -/
def splat (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat) : List Nat :=
  if h : e < n then
    (List.replicate n 0).set e c
  else
    have hsub : e - n < e := Nat.sub_lt (Nat.lt_of_lt_of_le hn (Nat.le_of_not_gt h)) hn
    have hsub2 : e - n + k < e := by
      have hk' : k ≤ n - 1 := Nat.le_pred_of_lt hk
      omega
    stripAdd (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k))
termination_by e

theorem tritMul_zero_left (a : Nat) : tritMul 0 a = 0 := by
  simp [tritMul]

theorem tritMul_one_left (a : Nat) (ha : a ≤ 2) : tritMul 1 a = a := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritMul, flipTrit]

theorem tritMul_one_right (a : Nat) (ha : a ≤ 2) : tritMul a 1 = a := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritMul, flipTrit]

theorem tritMul_zero_right (a : Nat) (ha : a ≤ 2) : tritMul a 0 = 0 := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritMul, flipTrit]

theorem tritMul_assoc (a b c : Nat) (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    tritMul (tritMul a b) c = tritMul a (tritMul b c) := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;>
    rcases hb3 with rfl | rfl | rfl <;>
    rcases hc3 with rfl | rfl | rfl <;>
    simp [tritMul, flipTrit]

theorem trit_cube (a : Nat) (ha : a ≤ 2) : tritMul a (tritMul a a) = a := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;> simp [tritMul, flipTrit]

theorem replicate_trits (m : Nat) : allTritList (List.replicate m 0) := by
  intro x hx
  rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
  omega

theorem coeff_set_eq (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    coeff (xs.set i v) i = v := by
  rw [coeff_eq_get _ i (by rw [List.length_set]; exact hi), List.getElem_set_self]

theorem coeff_set_ne (xs : List Nat) (i v j : Nat) (hj : j < xs.length) (hne : i ≠ j) :
    coeff (xs.set i v) j = coeff xs j := by
  have hj' : j < (xs.set i v).length := by rw [List.length_set]; exact hj
  rw [coeff_eq_get _ j hj', List.getElem_set, if_neg hne, ← coeff_eq_get xs j hj]

theorem coeff_ge (xs : List Nat) (t : Nat) (h : xs.length ≤ t) : coeff xs t = 0 := by
  unfold coeff
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp

theorem coeff_replicate_zero (m i : Nat) : coeff (List.replicate m 0) i = 0 := by
  by_cases hi : i < m
  · rw [coeff_eq_get _ i (by simpa [List.length_replicate] using hi), List.getElem_replicate]
  · exact coeff_ge _ i (by simpa [List.length_replicate] using Nat.le_of_not_gt hi)

theorem stripAdd_coeff (xs ys : List Nat) (i : Nat) (hi : i < xs.length) :
    coeff (stripAdd xs ys) i = tritAdd (coeff xs i) (coeff ys i) := by
  rw [coeff_eq_get (stripAdd xs ys) i (by rw [stripAdd_length]; exact hi),
    stripAdd_get xs ys i hi]

theorem lists_coeff {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hc : ∀ i, coeff xs i = coeff ys i) : xs = ys := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi1 hi2
    rw [← coeff_eq_get xs i hi1, ← coeff_eq_get ys i hi2]
    exact hc i

theorem stripAdd_assoc (a b c : List Nat)
    (hb : b.length = a.length) (hc : c.length = a.length) :
    stripAdd (stripAdd a b) c = stripAdd a (stripAdd b c) := by
  refine lists_coeff (by simp [stripAdd_length, hb, hc]) ?_
  intro i
  by_cases hi : i < a.length
  · rw [stripAdd_coeff (stripAdd a b) c i (by rw [stripAdd_length]; exact hi),
      stripAdd_coeff a b i hi,
      stripAdd_coeff a (stripAdd b c) i hi,
      stripAdd_coeff b c i (by rw [hb]; exact hi), tritAdd_assoc]
  · rw [coeff_ge _ i (by rw [stripAdd_length, stripAdd_length]; exact Nat.le_of_not_gt hi),
      coeff_ge _ i (by rw [stripAdd_length]; exact Nat.le_of_not_gt hi)]

theorem stripAdd_diamond (a b c d : List Nat)
    (hb : b.length = a.length) (hc : c.length = a.length) (hd : d.length = a.length) :
    stripAdd (stripAdd a b) (stripAdd c d) =
      stripAdd (stripAdd a c) (stripAdd b d) := by
  refine lists_coeff (by simp [stripAdd_length, hb, hc, hd]) ?_
  intro i
  by_cases hi : i < a.length
  · rw [stripAdd_coeff (stripAdd a b) (stripAdd c d) i (by rw [stripAdd_length]; exact hi),
      stripAdd_coeff a b i hi, stripAdd_coeff c d i (by rw [hc]; exact hi),
      stripAdd_coeff (stripAdd a c) (stripAdd b d) i (by rw [stripAdd_length]; exact hi),
      stripAdd_coeff a c i hi, stripAdd_coeff b d i (by rw [hb]; exact hi), trit_diamond]
  · rw [coeff_ge _ i (by rw [stripAdd_length, stripAdd_length]; exact Nat.le_of_not_gt hi),
      coeff_ge _ i (by rw [stripAdd_length, stripAdd_length]; exact Nat.le_of_not_gt hi)]

theorem stripAdd_left_zero (xs : List Nat) (ht : allTritList xs) :
    stripAdd (List.replicate xs.length 0) xs = xs := by
  rw [stripAdd_comm (List.replicate xs.length 0) xs (by simp [List.length_replicate]),
    stripAdd_zero xs ht]

theorem splat_len (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat) :
    (splat n k hn hk c e).length = n := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    unfold splat
    split
    · simp
    · rw [stripAdd_length, ih (e - n) (by omega)]

theorem splat_lt (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat) (he : e < n) :
    splat n k hn hk c e = (List.replicate n 0).set e c := by
  unfold splat
  simp [he]

theorem splat_ge (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat) (he : ¬ e < n) :
    splat n k hn hk c e =
      stripAdd (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k)) := by
  conv =>
    lhs
    unfold splat
  rw [dif_neg he]

theorem splat_zero (n k : Nat) (hn : 0 < n) (hk : k < n) (e : Nat) :
    splat n k hn hk 0 e = List.replicate n 0 := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · rw [splat_lt n k hn hk 0 e he]
      apply List.ext_getElem
      · simp
      · intro i hi _
        by_cases h : e = i
        · subst h
          simp [List.getElem_set_self, List.getElem_replicate]
        · have hi0 : i < (List.replicate n 0).length := by simpa using hi
          simp [List.getElem_set_ne h, List.getElem_replicate]
    · rw [splat_ge n k hn hk 0 e he, ih (e - n) (by omega), ih (e - n + k) (by omega)]
      simpa [List.length_replicate] using
        stripAdd_zero (List.replicate n 0) (replicate_trits n)

theorem splat_trits (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat) (hc : c ≤ 2) :
    allTritList (splat n k hn hk c e) := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · rw [splat_lt n k hn hk c e he]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      by_cases h : i = e
      · subst h
        rw [List.getElem_set_self]
        exact hc
      · rw [List.getElem_set_ne (Ne.symm h), List.getElem_replicate]
        omega
    · rw [splat_ge n k hn hk c e he]
      exact stripAdd_trits _ _

theorem splat_add (n k : Nat) (hn : 0 < n) (hk : k < n) (c d e : Nat)
    (hc : c ≤ 2) (hd : d ≤ 2) :
    splat n k hn hk (tritAdd c d) e =
      stripAdd (splat n k hn hk c e) (splat n k hn hk d e) := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · rw [splat_lt n k hn hk (tritAdd c d) e he, splat_lt n k hn hk c e he,
        splat_lt n k hn hk d e he]
      rw [stripAdd_set (List.replicate n 0) (List.replicate n 0) e c d
        (by simpa [List.length_replicate] using he) (by simp [List.length_replicate])]
      have hz := stripAdd_zero (List.replicate n 0) (replicate_trits n)
      simp only [List.length_replicate] at hz
      rw [hz]
    · rw [splat_ge n k hn hk (tritAdd c d) e he, splat_ge n k hn hk c e he,
        splat_ge n k hn hk d e he, ih (e - n) (by omega), ih (e - n + k) (by omega)]
      exact stripAdd_diamond _ _ _ _
        (by simp [splat_len]) (by simp [splat_len]) (by simp [splat_len])

/-- Multiply every hole by one trit. -/
def scaleList (n c : Nat) (xs : List Nat) : List Nat :=
  (List.range n).map fun i => tritMul c (coeff xs i)

theorem scaleList_len (n c : Nat) (xs : List Nat) : (scaleList n c xs).length = n := by
  simp [scaleList, List.length_map, List.length_range]

theorem scaleList_get (n c : Nat) (xs : List Nat) (i : Nat) (hi : i < n) :
    (scaleList n c xs)[i]'(by rw [scaleList_len]; exact hi) = tritMul c (coeff xs i) := by
  simp [scaleList, List.getElem_map, List.getElem_range, hi]

theorem scaleList_zero (n : Nat) (xs : List Nat) :
    scaleList n 0 xs = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [scaleList_len, List.length_replicate]
  · intro i hi _
    rw [scaleList_get n 0 xs i (by simpa [scaleList_len] using hi), tritMul_zero_left,
      List.getElem_replicate]

theorem scaleList_coeff (n c : Nat) (xs : List Nat) (i : Nat) (hi : i < n) :
    coeff (scaleList n c xs) i = tritMul c (coeff xs i) := by
  rw [coeff_eq_get _ i (by rw [scaleList_len]; exact hi), scaleList_get n c xs i hi]

theorem tritMul_left_dist (c a b : Nat) (hc : c ≤ 2) (ha : a ≤ 2) (hb : b ≤ 2) :
    tritMul c (tritAdd a b) = tritAdd (tritMul c a) (tritMul c b) := by
  rw [tritMul_comm c (tritAdd a b) hc (tritAdd_le a b),
    tritMul_add_left a b c ha hb hc,
    tritMul_comm a c ha hc, tritMul_comm b c hb hc]

theorem scale_stripAdd (n c : Nat) (a b : List Nat) (hc : c ≤ 2)
    (ha : allTritList a) (hb : allTritList b) (hlen : b.length = a.length)
    (hn : a.length = n) :
    scaleList n c (stripAdd a b) = stripAdd (scaleList n c a) (scaleList n c b) := by
  refine lists_coeff (by simp [scaleList_len, stripAdd_length]) ?_
  intro i
  by_cases hi : i < n
  · have haL : i < a.length := by rw [hn]; exact hi
    have hbL : i < b.length := by rw [hlen]; exact haL
    rw [scaleList_coeff n c (stripAdd a b) i hi, stripAdd_coeff a b i haL,
      stripAdd_coeff (scaleList n c a) (scaleList n c b) i (by rw [scaleList_len]; exact hi),
      scaleList_coeff n c a i hi, scaleList_coeff n c b i hi]
    exact tritMul_left_dist c (coeff a i) (coeff b i) hc
      (by rw [coeff_eq_get a i haL]; exact ha _ (List.getElem_mem haL))
      (by rw [coeff_eq_get b i hbL]; exact hb _ (List.getElem_mem hbL))
  · rw [coeff_ge _ i (by rw [scaleList_len]; exact Nat.le_of_not_gt hi),
      coeff_ge _ i (by rw [stripAdd_length, scaleList_len]; exact Nat.le_of_not_gt hi)]

theorem splat_scale (n k : Nat) (hn : 0 < n) (hk : k < n) (c d e : Nat)
    (hc : c ≤ 2) (hd : d ≤ 2) :
    splat n k hn hk (tritMul c d) e = scaleList n c (splat n k hn hk d e) := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · rw [splat_lt n k hn hk (tritMul c d) e he, splat_lt n k hn hk d e he]
      refine lists_coeff (by simp [scaleList_len, List.length_set, List.length_replicate]) ?_
      intro i
      by_cases hi : i < n
      · rw [scaleList_coeff n c ((List.replicate n 0).set e d) i hi]
        by_cases h : i = e
        · rw [h, coeff_set_eq (List.replicate n 0) e d
              (by simpa [List.length_replicate] using he),
            coeff_eq_get ((List.replicate n 0).set e (tritMul c d)) e
              (by simpa [List.length_set, List.length_replicate] using he),
            List.getElem_set_self]
        · rw [coeff_set_ne (List.replicate n 0) e d i
              (by simpa [List.length_replicate] using hi) (Ne.symm h),
            coeff_replicate_zero,
            coeff_eq_get ((List.replicate n 0).set e (tritMul c d)) i
              (by simpa [List.length_set, List.length_replicate] using hi),
            List.getElem_set_ne (Ne.symm h), List.getElem_replicate, tritMul_zero_right c hc]
      · rw [coeff_ge _ i (by rw [List.length_set, List.length_replicate]; exact Nat.le_of_not_gt hi),
          coeff_ge _ i (by rw [scaleList_len]; exact Nat.le_of_not_gt hi)]
    · rw [splat_ge n k hn hk (tritMul c d) e he, splat_ge n k hn hk d e he,
        ih (e - n) (by omega), ih (e - n + k) (by omega)]
      exact (scale_stripAdd n c _ _ hc
        (splat_trits n k hn hk d (e - n) hd)
        (splat_trits n k hn hk d (e - n + k) hd)
        (by simp [splat_len]) (by simp [splat_len])).symm

end EcbsLink2.Link2

