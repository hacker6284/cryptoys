/-
  The schoolbook adds onto its strip: starting from a sum is the sum of
  starting from the first summand. `onto` uses that. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.Lane
import EcbsLink2.Link2.FieldComm

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem tritAdd_left (a b c : Nat) :
    tritAdd (tritAdd a b) c = tritAdd (tritAdd a c) b := by
  rw [tritAdd_assoc, tritAdd_comm b c, ← tritAdd_assoc]

def stripAdd (xs ys : List Nat) : List Nat :=
  (List.range xs.length).map fun i => tritAdd (coeff xs i) (coeff ys i)

theorem stripAdd_length (xs ys : List Nat) : (stripAdd xs ys).length = xs.length := by
  simp [stripAdd, List.length_map, List.length_range]

theorem stripAdd_get (xs ys : List Nat) (i : Nat) (hi : i < xs.length) :
    (stripAdd xs ys)[i]'(by rw [stripAdd_length]; exact hi) =
      tritAdd (coeff xs i) (coeff ys i) := by
  simp [stripAdd, List.getElem_map, List.getElem_range, hi]

theorem stripAdd_trits (xs ys : List Nat) : allTritList (stripAdd xs ys) := by
  intro x hx
  simp only [stripAdd, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩
  unfold tritAdd
  exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))

theorem stripAdd_zero (xs : List Nat) (ht : allTritList xs) :
    stripAdd xs (List.replicate xs.length 0) = xs := by
  apply List.ext_getElem
  · simp [stripAdd_length, List.length_replicate]
  · intro i hi _
    have hi0 : i < xs.length := by rw [stripAdd_length] at hi; exact hi
    rw [stripAdd_get xs _ i hi0, coeff_eq_get xs i hi0,
      coeff_eq_get (List.replicate xs.length 0) i (by simp [List.length_replicate]; exact hi0)]
    have hx : xs[i] < 3 := by
      have hle : xs[i] ≤ 2 := ht _ (List.getElem_mem hi0)
      omega
    simp [List.getElem_replicate, tritAdd, Nat.mod_eq_of_lt hx]

private theorem coeff_set_eq (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    coeff (xs.set i v) i = v := by
  rw [coeff_eq_get _ i (by rw [List.length_set]; exact hi), List.getElem_set_self]

private theorem coeff_set_ne (xs : List Nat) (i v j : Nat) (hj : j < xs.length) (hne : i ≠ j) :
    coeff (xs.set i v) j = coeff xs j := by
  have hj' : j < (xs.set i v).length := by rw [List.length_set]; exact hj
  rw [coeff_eq_get _ j hj', List.getElem_set, if_neg hne, ← coeff_eq_get xs j hj]

private theorem list_set_id (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.set i xs[i] = xs := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    by_cases h : j = i
    · subst h
      simp
    · simp [List.getElem_set_ne (Ne.symm h)]

theorem stripAdd_set (xs ys : List Nat) (i v w : Nat)
    (hi : i < xs.length) (hlen : ys.length = xs.length) :
    stripAdd (xs.set i v) (ys.set i w) = (stripAdd xs ys).set i (tritAdd v w) := by
  apply List.ext_getElem
  · simp [stripAdd_length, List.length_set]
  · intro j hj1 _
    have hj : j < xs.length := by
      rw [stripAdd_length, List.length_set] at hj1
      exact hj1
    rw [stripAdd_get (xs.set i v) (ys.set i w) j (by rw [List.length_set]; exact hj)]
    by_cases hji : j = i
    · subst hji
      rw [coeff_set_eq xs j v hi, coeff_set_eq ys j w (by rw [hlen]; exact hi),
        List.getElem_set_self]
    · have hne : i ≠ j := Ne.symm hji
      rw [coeff_set_ne xs i v j hj hne, coeff_set_ne ys i w j (by rw [hlen]; exact hj) hne,
        List.getElem_set_ne hne, stripAdd_get xs ys j hj]

theorem lay_strip (xs ys : List Nat) (idx d : Nat)
    (hi : idx < xs.length) (hlen : ys.length = xs.length) :
    layCell (stripAdd xs ys) idx d = stripAdd (layCell xs idx d) ys := by
  have hcy : coeff ys idx = ys[idx]'(by rw [hlen]; exact hi) :=
    coeff_eq_get ys idx (by rw [hlen]; exact hi)
  have hget : coeff (stripAdd xs ys) idx = tritAdd (coeff xs idx) (coeff ys idx) := by
    rw [coeff_eq_get _ idx (by rw [stripAdd_length]; exact hi), stripAdd_get _ _ _ hi]
  unfold layCell
  rw [hget, tritAdd_left]
  rw [← stripAdd_set xs ys idx (tritAdd (coeff xs idx) d) (coeff ys idx) hi hlen]
  congr 1
  rw [hcy, list_set_id ys idx (by rw [hlen]; exact hi)]

theorem schoolStep_strip (a xs ys : List Nat) (i j : Nat) (mir : Bool)
    (hlen : ys.length = xs.length)
    (hidx : coeff a j = 0 ∨ i + j < xs.length) :
    schoolStep a i mir (stripAdd xs ys) j = stripAdd (schoolStep a i mir xs j) ys := by
  unfold schoolStep
  by_cases hz : coeff a j = 0
  · simp [hz]
  · simp [hz]
    rcases hidx with h0 | hi
    · exact absurd h0 hz
    · exact lay_strip xs ys (i + j) _ hi hlen

private theorem rowAt_len (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) :
    ∀ k, (rowAt a i mir strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by
    rw [rowAt_succ]
    have hstep : (schoolStep a i mir (rowAt a i mir strip k) k).length =
        (rowAt a i mir strip k).length := by
      unfold schoolStep layCell
      by_cases hz : coeff a k = 0
      · simp [hz]
      · cases mir <;> simp [hz, List.length_set]
    rw [hstep, rowAt_len a i mir strip k]

private theorem rowAt_strip (a xs ys : List Nat) (i : Nat) (mir : Bool)
    (hlen : ys.length = xs.length) :
    ∀ k, (∀ j, j < k → coeff a j = 0 ∨ i + j < xs.length) →
      rowAt a i mir (stripAdd xs ys) k = stripAdd (rowAt a i mir xs k) ys
  | 0, _ => by simp [rowAt]
  | k + 1, hspan => by
    rw [rowAt_succ, rowAt_succ,
      rowAt_strip a xs ys i mir hlen k (fun j hj => hspan j (Nat.lt_succ_of_lt hj))]
    exact schoolStep_strip a (rowAt a i mir xs k) ys i k mir
      (by rw [rowAt_len]; exact hlen)
      (by
        rcases hspan k (Nat.lt_succ_self k) with h0 | hi
        · exact Or.inl h0
        · exact Or.inr (by rw [rowAt_len]; exact hi))

theorem schoolRow_strip (n : Nat) (a xs ys : List Nat) (i : Nat) (mir : Bool)
    (hlen : ys.length = xs.length)
    (hspan : ∀ j, j < n → i + j < xs.length) :
    schoolRow n a i mir (stripAdd xs ys) = stripAdd (schoolRow n a i mir xs) ys := by
  rw [schoolRow_eq_rowAt, schoolRow_eq_rowAt,
    rowAt_strip a xs ys i mir hlen n (fun j hj => Or.inr (hspan j hj))]

theorem schoolAt_length (n : Nat) (a b z : List Nat) (i : Nat) (mir : Bool) :
    (schoolAt n a b mir i z).length = z.length := by
  unfold schoolAt
  by_cases hz : coeff b i = 0
  · simp [hz]
  · simp [hz, schoolRow_eq_rowAt, rowAt_len]

theorem schoolAt_strip (n : Nat) (a b xs ys : List Nat) (i : Nat) (mir : Bool)
    (hlen : xs.length = ys.length)
    (hspan : ∀ j, j < n → i + j < xs.length) :
    schoolAt n a b mir i (stripAdd xs ys) = stripAdd (schoolAt n a b mir i xs) ys := by
  unfold schoolAt
  by_cases hz : coeff b i = 0
  · simp [hz]
  · simp [hz]
    exact schoolRow_strip n a xs ys i _ hlen.symm hspan

private theorem foldr_len (n : Nat) (a b : List Nat) (mir : Bool) (ysLen : Nat) :
    ∀ (is : List Nat) (xs : List Nat), xs.length = ysLen →
      (List.foldr (schoolAt n a b mir) xs is).length = ysLen := by
  intro is
  induction is with
  | nil => intro xs hx; simpa using hx
  | cons t ts ih =>
    intro xs hx
    rw [List.foldr_cons, schoolAt_length]
    exact ih xs hx

private theorem foldr_strip (n : Nat) (a b ys : List Nat) (mir : Bool) :
    ∀ (is : List Nat) (xs : List Nat), xs.length = ys.length →
      (∀ i, i ∈ is → ∀ j, j < n → i + j < ys.length) →
      List.foldr (schoolAt n a b mir) (stripAdd xs ys) is =
        stripAdd (List.foldr (schoolAt n a b mir) xs is) ys := by
  intro is
  induction is with
  | nil =>
    intro xs hlen _
    simp
  | cons i is ih =>
    intro xs hlen hspan
    rw [List.foldr_cons, List.foldr_cons]
    have hrec := ih xs hlen (fun t ht j hj => hspan t (by simp [ht]) j hj)
    rw [hrec]
    have hlenF : (List.foldr (schoolAt n a b mir) xs is).length = ys.length :=
      foldr_len n a b mir ys.length is xs hlen
    exact schoolAt_strip n a b _ ys i mir hlenF (fun j hj => by
      rw [hlenF]
      exact hspan i (by simp) j hj)

/-- Starting the schoolbook from a sum lays the same rows onto the first summand. -/
theorem school_strip (n : Nat) (a b xs ys : List Nat) (mir : Bool)
    (hlen : xs.length = ys.length)
    (hspan : 2 * (n - 1) < ys.length ∨ n = 0) :
    school n a b (stripAdd xs ys) mir = stripAdd (school n a b xs mir) ys := by
  have hfold : ∀ strip, school n a b strip mir =
      (List.range n).foldr (schoolAt n a b mir) strip := by
    intro strip
    unfold school schoolAt
    rfl
  rw [hfold, hfold]
  apply foldr_strip n a b ys mir (List.range n) xs hlen
  intro i hi j hj
  have hin : i < n := by simpa [List.mem_range] using hi
  rcases hspan with hsp | hz
  · have hle : i + j ≤ 2 * (n - 1) := by
      have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hin
      have hj' : j ≤ n - 1 := Nat.le_sub_one_of_lt hj
      omega
    omega
  · omega

theorem stripAdd_comm (xs ys : List Nat) (hlen : xs.length = ys.length) :
    stripAdd xs ys = stripAdd ys xs := by
  apply List.ext_getElem
  · simp [stripAdd_length, hlen]
  · intro i hi _
    have hix : i < xs.length := by rw [stripAdd_length] at hi; exact hi
    have hiy : i < ys.length := by rw [← hlen]; exact hix
    rw [stripAdd_get xs ys i hix, stripAdd_get ys xs i hiy, tritAdd_comm]

/-- Laying onto `pad` is the product laid onto zeros, added to `pad`. -/
theorem school_onto (n : Nat) (a b pad : List Nat) (mir : Bool)
    (ht : allTritList pad) (hspan : 2 * (n - 1) < pad.length ∨ n = 0) :
    school n a b pad mir =
      stripAdd (school n a b (List.replicate pad.length 0) mir) pad := by
  have hlen0 : (List.replicate pad.length 0).length = pad.length := by simp
  have hsum : stripAdd (List.replicate pad.length 0) pad = pad := by
    rw [stripAdd_comm _ _ hlen0, stripAdd_zero pad ht]
  have hsch := school_strip n a b (List.replicate pad.length 0) pad mir hlen0 hspan
  rw [hsum] at hsch
  exact hsch

private theorem trit_le (a b : Nat) : tritAdd a b ≤ 2 := by
  unfold tritAdd
  exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))

private theorem tritAdd_right (a : Nat) (ha : a ≤ 2) : tritAdd a 0 = a := by
  have hlt : a < 3 := by omega
  simp [tritAdd, Nat.mod_eq_of_lt hlt]

/-- Adding `c` at one hole of a sum adds `c` on the first summand. -/
theorem stripAdd_addAt (xs ys : List Nat) (j c : Nat)
    (hj : j < xs.length) (_ : ys.length = xs.length) :
    (stripAdd xs ys).set j (tritAdd (coeff (stripAdd xs ys) j) c) =
      stripAdd (xs.set j (tritAdd (coeff xs j) c)) ys := by
  apply List.ext_getElem
  · simp [stripAdd_length, List.length_set]
  · intro i hi _
    have hi0 : i < xs.length := by
      have hlenSet : ((stripAdd xs ys).set j (tritAdd (coeff (stripAdd xs ys) j) c)).length =
          xs.length := by simp [stripAdd_length, List.length_set]
      rw [hlenSet] at hi
      exact hi
    have hjs : j < (stripAdd xs ys).length := by rw [stripAdd_length]; exact hj
    by_cases h : i = j
    · cases h
      rw [List.getElem_set_self (h := by rw [List.length_set]; exact hjs),
        coeff_eq_get _ j hjs, stripAdd_get xs ys j hj, tritAdd_left,
        stripAdd_get (xs.set j (tritAdd (coeff xs j) c)) ys j
          (by rw [List.length_set]; exact hj),
        coeff_set_eq xs j _ hj]
    · have hne : j ≠ i := Ne.symm h
      rw [List.getElem_set_ne hne, stripAdd_get xs ys i hi0,
        stripAdd_get (xs.set j _) ys i (by rw [List.length_set]; exact hi0),
        coeff_set_ne xs j _ i hi0 hne]

/-- Folding a sum whose second summand is empty at this high hole moves only
    the first summand's peg. -/
theorem foldHigh_pad (n gap e : Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs)
    (hy0 : n ≤ e → coeff ys e = 0) (hg : gap ≤ n) :
    foldHigh n gap e (stripAdd xs ys) = stripAdd (foldHigh n gap e xs) ys := by
  by_cases hlt : e < n
  · simp [foldHigh, hlt]
  · have hge : n ≤ e := by omega
    by_cases he : e < xs.length
    · have hye : coeff ys e = 0 := hy0 hge
      have htr : coeff xs e ≤ 2 := by
        rw [coeff_eq_get xs e he]
        exact htx _ (List.getElem_mem he)
      have hcs : coeff (stripAdd xs ys) e = coeff xs e := by
        rw [coeff_eq_get _ e (by rw [stripAdd_length]; exact he), stripAdd_get xs ys e he,
          hye, tritAdd_right _ htr]
      by_cases hz : coeff xs e = 0
      · simp [foldHigh, hcs, hz]
      · have hn0 : e - n < xs.length := by omega
        have hg0 : e - gap < xs.length := by
          have hgle : gap ≤ e := by omega
          omega
        have hys0 : ys.set e 0 = ys := by
          have hyel : ys[e]'(by rw [hlen]; exact he) = 0 := by
            rw [← coeff_eq_get ys e (by rw [hlen]; exact he), hye]
          rw [← hyel, list_set_id ys e (by rw [hlen]; exact he)]
        have hclear : (stripAdd xs ys).set e 0 = stripAdd (xs.set e 0) ys := by
          have hset := stripAdd_set xs ys e 0 0 he hlen
          rw [hys0] at hset
          simpa [tritAdd] using hset.symm
        unfold foldHigh
        simp only [hcs, hz, hlt, false_or, ite_false]
        rw [hclear]
        rw [stripAdd_addAt (xs.set e 0) ys (e - n) (coeff xs e)
          (by rw [List.length_set]; exact hn0) (by rw [List.length_set]; exact hlen)]
        rw [stripAdd_addAt ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) (coeff xs e)))
          ys (e - gap) (coeff xs e) (by simp [List.length_set]; exact hg0)
          (by simp [List.length_set]; exact hlen)]
    · have hge2 : xs.length ≤ e := by omega
      have hcx : coeff xs e = 0 := by
        unfold coeff
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
        rfl
      have hcs : coeff (stripAdd xs ys) e = 0 := by
        unfold coeff
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [stripAdd_length]; exact hge2)]
        simp [tritAdd]
      simp [foldHigh, hcs, hcx]

end EcbsLink2.Link2
