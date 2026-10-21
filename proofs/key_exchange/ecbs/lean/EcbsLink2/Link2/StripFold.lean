/-
  The lane fold of a sum is the sum of the folds, when the second summand
  has no peg at or above hole `n`. An `onto` schoolbook starts from that
  sum, so its folded prefix is `fieldAdd` of the home and `fieldMul`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.StripLin
import EcbsLink2.Link2.Lists
import EcbsLink2.SpecCurve

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem trit_le (a b : Nat) : tritAdd a b ≤ 2 := by
  unfold tritAdd
  exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))

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

/-- One high peg keeps the strip a list of trits. -/
private theorem foldHigh_keeps (n gap e : Nat) (strip : List Nat)
    (hs : allTritList strip) :
    allTritList (foldHigh n gap e strip) := by
  unfold foldHigh
  by_cases hif : coeff strip e = 0 ∨ e < n
  · simp [hif, hs]
  · simp only [hif, ite_false]
    let cleared := strip.set e 0
    have hcleared : allTritList cleared :=
      tritList_set_local strip hs e 0 (Nat.zero_le 2)
    let once := cleared.set (e - n) (tritAdd (coeff cleared (e - n)) (coeff strip e))
    have honce : allTritList once :=
      tritList_set_local cleared hcleared (e - n) _ (trit_le _ _)
    exact tritList_set_local once honce (e - gap) _ (trit_le _ _)

private theorem foldrHigh_len (n gap : Nat) (ds : List Nat) (xs : List Nat) :
    (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs).length = xs.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [foldHigh_len, ih]

private theorem foldrHigh_trits (n gap : Nat) (ds : List Nat) (xs : List Nat)
    (ht : allTritList xs) :
    allTritList (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs) := by
  induction ds with
  | nil => exact ht
  | cons d ds ih =>
    simp only [List.foldr_cons]
    exact foldHigh_keeps n gap (n + d) _ ih

/-- Folding a list of high holes distributes over a sum whose second
    summand is empty at every hole the fold touches. -/
theorem foldrHigh_pad (n gap : Nat) (ds : List Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs)
    (hy : ∀ e, n ≤ e → coeff ys e = 0) (hg : gap ≤ n) :
    ds.foldr (fun d st => foldHigh n gap (n + d) st) (stripAdd xs ys) =
      stripAdd (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs) ys := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact foldHigh_pad n gap (n + d)
      (ds.foldr (fun d st => foldHigh n gap (n + d) st) xs) ys
      (by rw [foldrHigh_len, hlen])
      (foldrHigh_trits n gap ds xs htx)
      (fun _ => hy (n + d) (Nat.le_add_right n d)) hg

/-- The lane fold of a sum is the sum of the folds, when `ys` has no peg
    at or above hole `n`. -/
theorem reduceStrip_pad (n gap : Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs)
    (hy : ∀ e, n ≤ e → coeff ys e = 0) (hg : gap ≤ n) :
    reduceStrip n gap (stripAdd xs ys) = stripAdd (reduceStrip n gap xs) ys := by
  unfold reduceStrip
  rw [stripAdd_length]
  exact foldrHigh_pad n gap (List.range (xs.length - n)) xs ys hlen htx hy hg

theorem laneFold_pad (n gap : Nat) (xs ys : List Nat)
    (hlen : ys.length = xs.length) (htx : allTritList xs)
    (hy : ∀ e, n ≤ e → coeff ys e = 0) (hg : gap ≤ n) :
    laneFold n gap (stripAdd xs ys) = stripAdd (laneFold n gap xs) ys := by
  unfold laneFold
  exact reduceStrip_pad n gap xs ys hlen htx hy hg

private theorem zero_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

/-- Laying onto `pad` and folding is the folded product added to `pad`,
    when `pad` has no peg at or above hole `n`. -/
theorem laneFold_onto (n gap : Nat) (a b pad : List Nat) (mir : Bool)
    (ht : allTritList pad)
    (hspan : 2 * (n - 1) < pad.length ∨ n = 0)
    (hy : ∀ e, n ≤ e → coeff pad e = 0) (hg : gap ≤ n) :
    laneFold n gap (school n a b pad mir) =
      stripAdd (laneFold n gap (school n a b (List.replicate pad.length 0) mir)) pad := by
  have hbench : ∀ i, i < n → i + (n - 1) < pad.length := by
    intro i hi
    rcases hspan with hsp | hz
    · have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
      omega
    · omega
  have htx := school_trits a b (List.replicate pad.length 0) mir n (zero_trits _)
    (by simpa [List.length_replicate] using hbench)
  have hlenSch : (school n a b (List.replicate pad.length 0) mir).length = pad.length := by
    simpa [List.length_replicate] using school_length a b (List.replicate pad.length 0) mir n
  rw [school_onto n a b pad mir ht hspan, laneFold]
  exact reduceStrip_pad n gap _ pad hlenSch.symm htx hy hg

theorem stripAdd_take (n : Nat) (xs ys : List Nat) (hn : n ≤ xs.length) :
    (stripAdd xs ys).take n = fieldAdd n xs ys := by
  apply List.ext_getElem
  · simp [stripAdd_length, fieldAdd, List.length_map, List.length_range, List.length_take,
      Nat.min_eq_left hn]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [fieldAdd, List.length_map, List.length_range] using hi2
    have hix : i < xs.length := by omega
    rw [List.getElem_take, stripAdd_get xs ys i hix]
    simp [fieldAdd, List.getElem_map, List.getElem_range]

theorem fieldAdd_comm (n : Nat) (xs ys : List Nat) :
    fieldAdd n xs ys = fieldAdd n ys xs := by
  apply List.ext_getElem
  · simp [fieldAdd, List.length_map, List.length_range]
  · intro i hi _
    simp [fieldAdd, List.getElem_map, List.getElem_range, tritAdd_comm]

theorem fieldAdd_coeff (n : Nat) (a b c d : List Nat)
    (ha : ∀ i, i < n → coeff a i = coeff c i)
    (hb : ∀ i, i < n → coeff b i = coeff d i) :
    fieldAdd n a b = fieldAdd n c d := by
  apply List.ext_getElem
  · simp [fieldAdd, List.length_map, List.length_range]
  · intro i hi _
    have hi' : i < n := by
      simpa [fieldAdd, List.length_map, List.length_range] using hi
    simp [fieldAdd, List.getElem_map, List.getElem_range, ha i hi', hb i hi']

theorem fieldAdd_right_take (n : Nat) (xs ys : List Nat) (hn : n ≤ ys.length) :
    fieldAdd n xs (ys.take n) = fieldAdd n xs ys := by
  apply fieldAdd_coeff
  · intro _ _; rfl
  · intro i hi
    have hi' : i < (ys.take n).length := by
      rw [List.length_take, Nat.min_eq_left hn]; exact hi
    rw [coeff_eq_get _ i hi', coeff_eq_get ys i (by omega), List.getElem_take]

/-- Hole `i` below `n` in the copied home is the home's own trit. -/
theorem pref_coeff_lo (xs : List Nat) (m n i : Nat)
    (hn : n ≤ m) (hx : n ≤ xs.length) (hi : i < n) :
    coeff (pref xs m n) i = coeff xs i := by
  have hlen := pref_length hn hx
  have hiP : i < (pref xs m n).length := by rw [hlen]; omega
  have htake : i < (xs.take n).length := by
    rw [List.length_take, Nat.min_eq_left hx]; omega
  rw [coeff_eq_get _ i hiP]
  unfold pref
  rw [List.getElem_append_left htake, List.getElem_take, ← coeff_eq_get xs i (by omega)]

/-- A copied home has no peg at or above hole `n`. -/
theorem pref_coeff_hi (xs : List Nat) (m n e : Nat)
    (hn : n ≤ m) (hx : n ≤ xs.length) (he : n ≤ e) :
    coeff (pref xs m n) e = 0 := by
  by_cases hlt : e < m
  · have hi : e < (pref xs m n).length := by rw [pref_length hn hx]; exact hlt
    have htake : (xs.take n).length ≤ e := by
      rw [List.length_take, Nat.min_eq_left hx]; omega
    rw [coeff_eq_get _ e hi]
    unfold pref
    rw [List.getElem_append_right htake, List.getElem_replicate]
  · rw [coeff, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [pref_length hn hx]; omega)]
    rfl

theorem pref_trits (xs : List Nat) (m n : Nat)
    (ht : allTritList xs) (hn : n ≤ m) (hx : n ≤ xs.length) :
    allTritList (pref xs m n) := by
  intro x hxmem
  rw [List.mem_iff_getElem] at hxmem
  obtain ⟨i, hi, rfl⟩ := hxmem
  have hlen := pref_length hn hx
  have hi' : i < m := by rw [hlen] at hi; exact hi
  by_cases hlt : i < n
  · have htake : i < (xs.take n).length := by
      rw [List.length_take, Nat.min_eq_left hx]; omega
    unfold pref
    rw [List.getElem_append_left htake, List.getElem_take]
    exact ht _ (List.getElem_mem (by omega))
  · have hge : n ≤ i := Nat.le_of_not_gt hlt
    rw [← coeff_eq_get (pref xs m n) i hi, pref_coeff_hi xs m n i hn hx hge]
    exact Nat.zero_le _

/-- The `onto` product, folded: the length-`n` prefix is the home plus
    `fieldMul` of the two factors. -/
theorem onto_add (n k bench : Nat) (a b home : List Nat)
    (ht : allTritList home) (hlen : home.length = n)
    (hspan : 2 * (n - 1) < bench ∨ n = 0)
    (hnb : n ≤ bench) :
    (laneFold n (n - k) (school n a b (pref home bench n) false)).take n =
      fieldAdd n home (fieldMul n k bench a b) := by
  have hx : n ≤ home.length := by omega
  have hpadLen : (pref home bench n).length = bench := pref_length hnb hx
  have hpadT : allTritList (pref home bench n) := pref_trits home bench n ht hnb hx
  have hy : ∀ e, n ≤ e → coeff (pref home bench n) e = 0 :=
    fun e he => pref_coeff_hi home bench n e hnb hx he
  have hspanP : 2 * (n - 1) < (pref home bench n).length ∨ n = 0 := by
    rw [hpadLen]
    exact hspan
  have hfold := laneFold_onto n (n - k) a b (pref home bench n) false hpadT hspanP hy
    (Nat.sub_le n k)
  rw [hfold, hpadLen]
  have hschLen : (school n a b (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using school_length a b (List.replicate bench 0) false n
  have hlfLen : (laneFold n (n - k) (school n a b (List.replicate bench 0) false)).length =
      bench := by
    rw [laneFold_length _ _ _ (by rw [hschLen]; exact hnb), hschLen]
  rw [stripAdd_take n _ _ (by rw [hlfLen]; exact hnb)]
  rw [fieldAdd_comm]
  have hlo : ∀ i, i < n → coeff (pref home bench n) i = coeff home i :=
    fun i hi => pref_coeff_lo home bench n i hnb hx hi
  rw [fieldAdd_coeff n (pref home bench n)
      (laneFold n (n - k) (school n a b (List.replicate bench 0) false))
      home (laneFold n (n - k) (school n a b (List.replicate bench 0) false))
      hlo (fun _ _ => rfl)]
  have hmul : (laneFold n (n - k) (school n a b (List.replicate bench 0) false)).take n =
      fieldMul n k bench a b := by
    unfold fieldMul laneFold
    rfl
  rw [← fieldAdd_right_take n home _ (by rw [hlfLen]; exact hnb), hmul]

end EcbsLink2.Link2
