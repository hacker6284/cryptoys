/-
  A trit list is the remainder of its schoolbook product. `polyVal` sends a
  strip to that remainder, and one lane-fold step does not change it.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldRing

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem trit_move (a b c t : Nat) :
    tritAdd a (tritAdd (tritAdd b c) t) = tritAdd (tritAdd a (tritAdd b t)) c := by
  rw [tritAdd_assoc b c t, ← tritAdd_assoc a b (tritAdd c t), tritAdd_comm c t,
    ← tritAdd_assoc (tritAdd a b) t c, tritAdd_assoc a b t]

theorem coeff_le {xs : List Nat} (h : allTritList xs) (i : Nat) : coeff xs i ≤ 2 := by
  by_cases hi : i < xs.length
  · rw [coeff_eq_get xs i hi]
    exact h _ (List.getElem_mem hi)
  · rw [coeff_ge xs i (Nat.le_of_not_gt hi)]
    omega

theorem stripAdd_replicate (m : Nat) :
    stripAdd (List.replicate m 0) (List.replicate m 0) = List.replicate m 0 := by
  simpa [List.length_replicate] using
    stripAdd_zero (List.replicate m 0) (replicate_trits m)

/-- The first `m` powers, reduced. -/
def polyFold (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (m : Nat) : List Nat :=
  (List.range m).foldl
    (fun acc i => stripAdd acc (splat n k hn hk (coeff xs i) i))
    (List.replicate n 0)

theorem polyFold_zero (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) :
    polyFold n k hn hk xs 0 = List.replicate n 0 := by
  simp [polyFold]

theorem polyFold_succ (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (m : Nat) :
    polyFold n k hn hk xs (m + 1) =
      stripAdd (polyFold n k hn hk xs m) (splat n k hn hk (coeff xs m) m) := by
  unfold polyFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem polyFold_len (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (m : Nat) :
    (polyFold n k hn hk xs m).length = n := by
  induction m with
  | zero => simp [polyFold]
  | succ m ih => rw [polyFold_succ, stripAdd_length, ih]

theorem polyFold_trits (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) (m : Nat) : allTritList (polyFold n k hn hk xs m) := by
  induction m with
  | zero => exact replicate_trits n
  | succ m ih =>
    rw [polyFold_succ]
    exact stripAdd_trits _ _

/-- Powers from `s` upward, reduced. -/
def polyFrom (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (s : Nat) : List Nat :=
  if h : xs.length ≤ s then List.replicate n 0
  else
    have hs : s < xs.length := Nat.lt_of_not_le h
    have hpos : 0 < xs.length - s := Nat.sub_pos_of_lt hs
    have heq : xs.length - (s + 1) = xs.length - s - 1 := (Nat.sub_sub xs.length s 1).symm
    have hlt : xs.length - (s + 1) < xs.length - s := by
      rw [heq]
      exact Nat.sub_lt hpos (by decide)
    stripAdd (splat n k hn hk (coeff xs s) s) (polyFrom n k hn hk xs (s + 1))
termination_by xs.length - s

theorem polyFrom_empty (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (s : Nat)
    (hs : xs.length ≤ s) : polyFrom n k hn hk xs s = List.replicate n 0 := by
  unfold polyFrom
  rw [dif_pos hs]

theorem polyFrom_succ (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (s : Nat)
    (hs : ¬ xs.length ≤ s) :
    polyFrom n k hn hk xs s =
      stripAdd (splat n k hn hk (coeff xs s) s) (polyFrom n k hn hk xs (s + 1)) := by
  conv =>
    lhs
    unfold polyFrom
  rw [dif_neg hs]

theorem polyFrom_len (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (s : Nat) :
    (polyFrom n k hn hk xs s).length = n := by
  by_cases hs : xs.length ≤ s
  · rw [polyFrom_empty n k hn hk xs s hs]
    simp
  · rw [polyFrom_succ n k hn hk xs s hs, stripAdd_length, splat_len]

/-- The reduced value of every power in `xs`. -/
def polyVal (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) : List Nat :=
  polyFold n k hn hk xs xs.length

theorem polyVal_len (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) :
    (polyVal n k hn hk xs).length = n :=
  polyFold_len n k hn hk xs xs.length

theorem polyVal_trits (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) : allTritList (polyVal n k hn hk xs) :=
  polyFold_trits n k hn hk xs ht xs.length

theorem poly_join (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (s : Nat)
    (hs : s ≤ xs.length) (ht : allTritList xs) :
    polyVal n k hn hk xs =
      stripAdd (polyFold n k hn hk xs s) (polyFrom n k hn hk xs s) := by
  unfold polyVal
  suffices ∀ fuel s, s ≤ xs.length → xs.length - s ≤ fuel →
      polyFold n k hn hk xs xs.length =
        stripAdd (polyFold n k hn hk xs s) (polyFrom n k hn hk xs s) from
    this (xs.length - s) s hs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro s hs0 hfuel
    have hsEq : s = xs.length := by omega
    rw [hsEq, polyFrom_empty n k hn hk xs xs.length (Nat.le_refl _)]
    have hz := stripAdd_zero (polyFold n k hn hk xs xs.length)
      (polyFold_trits n k hn hk xs ht xs.length)
    simp only [polyFold_len] at hz
    exact hz.symm
  | succ fuel ih =>
    intro s hs0 hfuel
    by_cases hdone : xs.length ≤ s
    · have hsEq : s = xs.length := by omega
      rw [hsEq, polyFrom_empty n k hn hk xs xs.length (Nat.le_refl _)]
      have hz := stripAdd_zero (polyFold n k hn hk xs xs.length)
        (polyFold_trits n k hn hk xs ht xs.length)
      simp only [polyFold_len] at hz
      exact hz.symm
    · have hs1 : s + 1 ≤ xs.length := by omega
      have hfuel1 : xs.length - (s + 1) ≤ fuel := by omega
      rw [polyFrom_succ n k hn hk xs s hdone, ih (s + 1) hs1 hfuel1, polyFold_succ]
      exact stripAdd_assoc (polyFold n k hn hk xs s)
        (splat n k hn hk (coeff xs s) s) (polyFrom n k hn hk xs (s + 1))
        (by rw [splat_len, polyFold_len]) (by rw [polyFrom_len, polyFold_len])

theorem polyFold_set_lo (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (i v m : Nat) (hm : m ≤ i) :
    polyFold n k hn hk (xs.set i v) m = polyFold n k hn hk xs m := by
  induction m with
  | zero => simp [polyFold]
  | succ m ih =>
    rw [polyFold_succ, polyFold_succ, ih (by omega)]
    have hne : i ≠ m := by omega
    by_cases hmL : m < xs.length
    · rw [coeff_set_ne xs i v m hmL hne]
    · rw [coeff_ge (xs.set i v) m (by simp [List.length_set]; exact Nat.le_of_not_gt hmL),
        coeff_ge xs m (Nat.le_of_not_gt hmL)]

theorem polyFrom_set_hi (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (i v s : Nat) (hs : i < s) :
    polyFrom n k hn hk (xs.set i v) s = polyFrom n k hn hk xs s := by
  suffices ∀ fuel s, i < s → xs.length - s ≤ fuel →
      polyFrom n k hn hk (xs.set i v) s = polyFrom n k hn hk xs s from
    this (xs.length - s) s hs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro s hs0 hfuel
    have hlen : (xs.set i v).length = xs.length := by simp
    rw [polyFrom_empty n k hn hk (xs.set i v) s (by rw [hlen]; omega),
      polyFrom_empty n k hn hk xs s (by omega)]
  | succ fuel ih =>
    intro s hs0 hfuel
    by_cases hdone : xs.length ≤ s
    · have hlen : (xs.set i v).length = xs.length := by simp
      rw [polyFrom_empty n k hn hk (xs.set i v) s (by rw [hlen]; exact hdone),
        polyFrom_empty n k hn hk xs s hdone]
    · have hneS : ¬ (xs.set i v).length ≤ s := by
        simp only [List.length_set]
        exact hdone
      rw [polyFrom_succ n k hn hk (xs.set i v) s hneS, polyFrom_succ n k hn hk xs s hdone]
      have hidx : i ≠ s := by omega
      rw [coeff_set_ne xs i v s (by omega) hidx, ih (s + 1) (Nat.lt_of_lt_of_le hs0 (Nat.le_succ _))
        (by omega)]

theorem tritList_set (xs : List Nat) (h : allTritList xs) (i v : Nat) (hv : v ≤ 2) :
    allTritList (xs.set i v) := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  by_cases he : j = i
  · subst he
    rw [List.getElem_set_self]
    exact hv
  · rw [List.getElem_set_ne (Ne.symm he)]
    exact h _ (List.getElem_mem (by simpa [List.length_set] using hj))

/-- Writing `old + d` at one hole adds `d · X^i` to the remainder. -/
theorem polyVal_set_add (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (i d : Nat) (hi : i < xs.length) (ht : allTritList xs) (hd : d ≤ 2) :
    polyVal n k hn hk (xs.set i (tritAdd (coeff xs i) d)) =
      stripAdd (polyVal n k hn hk xs) (splat n k hn hk d i) := by
  let ys := xs.set i (tritAdd (coeff xs i) d)
  have htY : allTritList ys := tritList_set xs ht i _ (tritAdd_le _ _)
  have hFi : polyFold n k hn hk ys i = polyFold n k hn hk xs i :=
    polyFold_set_lo n k hn hk xs i _ i (Nat.le_refl _)
  have hTi : polyFrom n k hn hk ys (i + 1) = polyFrom n k hn hk xs (i + 1) :=
    polyFrom_set_hi n k hn hk xs i _ (i + 1) (Nat.lt_succ_self _)
  have hcy : coeff ys i = tritAdd (coeff xs i) d :=
    coeff_set_eq xs i _ hi
  have hys := poly_join n k hn hk ys i (by simp [ys, List.length_set]; omega) htY
  have hxs := poly_join n k hn hk xs i (Nat.le_of_lt hi) ht
  have hsplitY := polyFrom_succ n k hn hk ys i (by simp [ys, List.length_set]; omega)
  have hsplitX := polyFrom_succ n k hn hk xs i (by omega)
  rw [hys, hsplitY, hcy, splat_add n k hn hk (coeff xs i) d i (coeff_le ht i) hd,
    hFi, hTi, hxs, hsplitX]
  refine lists_coeff (by simp [stripAdd_length, polyFold_len, splat_len, polyFrom_len]) ?_
  intro j
  by_cases hj : j < n
  · have hA : j < (polyFold n k hn hk xs i).length := by rw [polyFold_len]; exact hj
    have hS : j < (splat n k hn hk (coeff xs i) i).length := by rw [splat_len]; exact hj
    have hD : j < (splat n k hn hk d i).length := by rw [splat_len]; exact hj
    have hT : j < (polyFrom n k hn hk xs (i + 1)).length := by rw [polyFrom_len]; exact hj
    rw [stripAdd_coeff (polyFold n k hn hk xs i)
        (stripAdd (stripAdd (splat n k hn hk (coeff xs i) i) (splat n k hn hk d i))
          (polyFrom n k hn hk xs (i + 1))) j hA,
      stripAdd_coeff (stripAdd (splat n k hn hk (coeff xs i) i) (splat n k hn hk d i))
        (polyFrom n k hn hk xs (i + 1)) j (by rw [stripAdd_length]; exact hS),
      stripAdd_coeff (splat n k hn hk (coeff xs i) i) (splat n k hn hk d i) j hS,
      stripAdd_coeff
        (stripAdd (polyFold n k hn hk xs i)
          (stripAdd (splat n k hn hk (coeff xs i) i) (polyFrom n k hn hk xs (i + 1))))
        (splat n k hn hk d i) j (by rw [stripAdd_length]; exact hA),
      stripAdd_coeff (polyFold n k hn hk xs i)
        (stripAdd (splat n k hn hk (coeff xs i) i) (polyFrom n k hn hk xs (i + 1))) j hA,
      stripAdd_coeff (splat n k hn hk (coeff xs i) i) (polyFrom n k hn hk xs (i + 1)) j hS]
    exact trit_move _ _ _ _
  · rw [coeff_ge _ j (by rw [stripAdd_length, polyFold_len]; exact Nat.le_of_not_gt hj),
      coeff_ge _ j (by rw [stripAdd_length, stripAdd_length, polyFold_len]; exact Nat.le_of_not_gt hj)]

end EcbsLink2.Link2
