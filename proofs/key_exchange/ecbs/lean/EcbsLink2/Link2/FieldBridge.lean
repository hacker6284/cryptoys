/-
  `fieldMul` is the reduced schoolbook `mulVal`. The schoolbook lays the
  rows `mulVal` sums, and the lane fold does not change that remainder.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldAssoc

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem polyVal_replicate (n k : Nat) (hn : 0 < n) (hk : k < n) (L : Nat) :
    polyVal n k hn hk (List.replicate L 0) = List.replicate n 0 := by
  unfold polyVal
  rw [List.length_replicate]
  suffices ∀ m, polyFold n k hn hk (List.replicate L 0) m = List.replicate n 0 by
    exact this L
  intro m
  induction m with
  | zero => simp [polyFold]
  | succ m ih =>
    rw [polyFold_succ, ih, coeff_replicate_zero, splat_zero, stripAdd_replicate]

private theorem bne_false (b : Bool) : (b != false) = b := by
  cases b <;> rfl

private theorem trit_laid (c d : Nat) (hc : c = 1 ∨ c = 2) (hd : d ≤ 2) :
    laidTrit d (decide (c = 2)) = tritMul c d := by
  rcases hc with rfl | rfl
  · simp [laidTrit, tritMul, flipTrit]
  · simp [laidTrit, tritMul, flipTrit]

private theorem laid_zero (mir : Bool) : laidTrit 0 mir = 0 := by
  simp [laidTrit, flipTrit]

private theorem laid_le (d : Nat) (mir : Bool) (hd : d ≤ 2) : laidTrit d mir ≤ 2 := by
  simp [laidTrit]
  split
  · exact flipTrit_le d
  · exact hd

private theorem zeroFold_len (n : Nat) (g : Nat → List Nat) (m : Nat) :
    ((List.range m).foldl (fun acc i => stripAdd acc (g i)) (List.replicate n 0)).length = n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

/-- Adding `c` on the left of a sum is the sum that starts from `c`. -/
private theorem add_left_fold (n k : Nat) (hn : 0 < n) (hk : k < n)
    (c : List Nat) (g : Nat → List Nat) (m : Nat)
    (hcL : c.length = n) (hcT : allTritList c)
    (hgL : ∀ i, i < m → (g i).length = n)
    (hgT : ∀ i, i < m → allTritList (g i)) :
    stripAdd c ((List.range m).foldl (fun acc i => stripAdd acc (g i)) (List.replicate n 0)) =
      (List.range m).foldl (fun acc i => stripAdd acc (g i)) c := by
  induction m with
  | zero =>
    simp
    exact stripAdd_right_zero c hcT hcL
  | succ m ih =>
    have hgLm : (g m).length = n := hgL m (Nat.lt_succ_self _)
    have hgTm : allTritList (g m) := hgT m (Nat.lt_succ_self _)
    have hfoldL : ((List.range m).foldl (fun acc i => stripAdd acc (g i))
        (List.replicate n 0)).length = n := zeroFold_len n g m
    conv =>
      lhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← stripAdd_assoc c _ (g m) (by rw [hfoldL]; exact hcL.symm) (by rw [hgLm]; exact hcL.symm),
      ih (fun i hi => hgL i (Nat.lt_succ_of_lt hi)) (fun i hi => hgT i (Nat.lt_succ_of_lt hi))]

private theorem foldl_succ_re (g : Nat → List Nat) (p m : Nat) (acc : List Nat) :
    ((List.range m).map Nat.succ).foldl (fun acc t => stripAdd acc (g (p - t))) acc =
      (List.range m).foldl (fun acc j => stripAdd acc (g (p - 1 - j))) acc := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
    conv =>
      lhs
      rw [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil]
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]
    have hstep : p - Nat.succ m = p - 1 - m := by
      rw [Nat.succ_eq_add_one, Nat.add_comm, ← Nat.sub_sub]
    rw [hstep]

private theorem range_head (m : Nat) :
    List.range (m + 1) = 0 :: (List.range m).map Nat.succ := by
  induction m with
  | zero =>
    rw [List.range_succ, List.range_zero]
    simp
  | succ m ih =>
    conv =>
      lhs
      rw [List.range_succ, ih]
    conv =>
      rhs
      rw [List.range_succ]
    rw [List.map_append]
    simp [Nat.succ_eq_add_one]

private theorem rev_step (n k : Nat) (hn : 0 < n) (hk : k < n)
    (f : Nat → List Nat) (m : Nat)
    (hfL : ∀ i, i < m + 1 → (f i).length = n)
    (hfT : ∀ i, i < m + 1 → allTritList (f i)) :
    (List.range (m + 1)).foldl (fun acc t => stripAdd acc (f (m - t))) (List.replicate n 0) =
      stripAdd (f m) ((List.range m).foldl
        (fun acc t => stripAdd acc (f (m - 1 - t))) (List.replicate n 0)) := by
  rw [range_head]
  simp only [List.foldl_cons]
  have hz := stripAdd_left_zero (f m) (hfT m (Nat.lt_succ_self _))
  simp only [hfL m (Nat.lt_succ_self _)] at hz
  rw [show m - 0 = m from by omega, hz, foldl_succ_re (fun t => f t) m m (f m)]
  exact (add_left_fold n k hn hk (f m) (fun j => f (m - 1 - j)) m
    (hfL m (Nat.lt_succ_self _)) (hfT m (Nat.lt_succ_self _))
    (fun j hj => hfL (m - 1 - j) (by omega))
    (fun j hj => hfT (m - 1 - j) (by omega))).symm

/-- The sum of `f 0` through `f (m - 1)` does not depend on the end it starts from. -/
private theorem sum_rev (n k : Nat) (hn : 0 < n) (hk : k < n)
    (f : Nat → List Nat) (m : Nat)
    (hfL : ∀ i, i < m → (f i).length = n)
    (hfT : ∀ i, i < m → allTritList (f i)) :
    (List.range m).foldl (fun acc i => stripAdd acc (f i)) (List.replicate n 0) =
      (List.range m).foldl (fun acc t => stripAdd acc (f (m - 1 - t))) (List.replicate n 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfL' : ∀ i, i < m → (f i).length = n := fun i hi => hfL i (Nat.lt_succ_of_lt hi)
    have hfT' : ∀ i, i < m → allTritList (f i) := fun i hi => hfT i (Nat.lt_succ_of_lt hi)
    have ih' := ih hfL' hfT'
    have hfLm : (f m).length = n := hfL m (Nat.lt_succ_self _)
    have hfTm : allTritList (f m) := hfT m (Nat.lt_succ_self _)
    have hS : (List.range (m + 1)).foldl (fun acc i => stripAdd acc (f i)) (List.replicate n 0) =
        stripAdd ((List.range m).foldl (fun acc i => stripAdd acc (f i)) (List.replicate n 0))
          (f m) := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hrange : List.range (m + 1) = 0 :: (List.range m).map Nat.succ := range_head m
    have hT : (List.range (m + 1)).foldl
        (fun acc t => stripAdd acc (f ((m + 1) - 1 - t))) (List.replicate n 0) =
        stripAdd (f m) ((List.range m).foldl
          (fun acc t => stripAdd acc (f (m - 1 - t))) (List.replicate n 0)) := by
      have hstep := rev_step n k hn hk f m hfL hfT
      have hsub : ∀ t, (m + 1) - 1 - t = m - t := by intro t; omega
      simp only [hsub] at hstep
      exact hstep
    rw [hS, hT, ih', stripAdd_comm _ _ (by
      rw [zeroFold_len n (fun t => f (m - 1 - t)) m, hfLm])]

private theorem step_poly (n k : Nat) (hn : 0 < n) (hk : k < n)
    (a strip : List Nat) (i j : Nat) (mir : Bool)
    (hidx : i + j < strip.length) (ht : allTritList strip) (ha : allTritList a) :
    polyVal n k hn hk (schoolStep a i mir strip j) =
      stripAdd (polyVal n k hn hk strip)
        (splat n k hn hk (laidTrit (coeff a j) mir) (i + j)) ∧
    allTritList (schoolStep a i mir strip j) ∧
    (schoolStep a i mir strip j).length = strip.length := by
  unfold schoolStep
  by_cases hd : coeff a j = 0
  · simp only [hd, ite_true]
    refine ⟨?_, ht, trivial⟩
    rw [laid_zero, splat_zero]
    exact (stripAdd_right_zero _ (polyVal_trits n k hn hk strip ht)
      (polyVal_len n k hn hk strip)).symm
  · simp only [hd, ite_false]
    have hlaid : laidTrit (coeff a j) mir ≤ 2 := laid_le _ _ (coeff_le ha j)
    have hset : layCell strip (i + j) (if mir then flipTrit (coeff a j) else coeff a j) =
        strip.set (i + j) (tritAdd (coeff strip (i + j)) (laidTrit (coeff a j) mir)) := by
      unfold layCell laidTrit
      rfl
    rw [hset]
    refine ⟨polyVal_set_add n k hn hk strip (i + j) (laidTrit (coeff a j) mir) hidx ht hlaid,
      tritList_set strip ht (i + j) _ (tritAdd_le _ _), ?_⟩
    simp [List.length_set]

private theorem row_fold_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (a : List Nat) (i steps : Nat) (mir : Bool) :
    ((List.range steps).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (laidTrit (coeff a j) mir) (i + j)))
      (List.replicate n 0)).length = n := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

private theorem rowAt_poly (n k : Nat) (hn : 0 < n) (hk : k < n)
    (a strip : List Nat) (i steps : Nat) (mir : Bool)
    (hspan : ∀ j, j < steps → i + j < strip.length)
    (ht : allTritList strip) (ha : allTritList a) :
    polyVal n k hn hk (rowAt a i mir strip steps) =
      stripAdd (polyVal n k hn hk strip)
        ((List.range steps).foldl (fun acc j =>
          stripAdd acc (splat n k hn hk (laidTrit (coeff a j) mir) (i + j)))
          (List.replicate n 0)) ∧
    allTritList (rowAt a i mir strip steps) ∧
    (rowAt a i mir strip steps).length = strip.length := by
  induction steps with
  | zero =>
    refine ⟨?_, ht, rfl⟩
    simp [rowAt]
    exact (stripAdd_right_zero _ (polyVal_trits n k hn hk strip ht)
      (polyVal_len n k hn hk strip)).symm
  | succ steps ih =>
    have hspan' : ∀ j, j < steps → i + j < strip.length :=
      fun j hj => hspan j (Nat.lt_succ_of_lt hj)
    obtain ⟨hp, htR, hlenR⟩ := ih hspan'
    rw [rowAt_succ]
    have hidx : i + steps < (rowAt a i mir strip steps).length := by
      rw [hlenR]; exact hspan steps (Nat.lt_succ_self _)
    obtain ⟨hs, htS, hlenS⟩ := step_poly n k hn hk a (rowAt a i mir strip steps) i steps mir
      hidx htR ha
    refine ⟨?_, htS, by rw [hlenS, hlenR]⟩
    rw [hs, hp, stripAdd_assoc (polyVal n k hn hk strip) _ _
      (by rw [row_fold_len, polyVal_len]) (by rw [splat_len, polyVal_len])]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem row_match (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i c : Nat) (hx : allTritList x) (hc : c = 1 ∨ c = 2) :
    (List.range n).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (laidTrit (coeff x j) (decide (c = 2))) (i + j)))
      (List.replicate n 0) = rowSplat n k hn hk x i c := by
  unfold rowSplat
  suffices ∀ m, m ≤ n →
      (List.range m).foldl (fun acc j =>
          stripAdd acc (splat n k hn hk (laidTrit (coeff x j) (decide (c = 2))) (i + j)))
        (List.replicate n 0) =
      (List.range m).foldl (fun acc j =>
          stripAdd acc (splat n k hn hk (tritMul c (coeff x j)) (i + j)))
        (List.replicate n 0) by
    exact this n (Nat.le_refl _)
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    conv =>
      lhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega), trit_laid c (coeff x m) hc (coeff_le hx m)]

private theorem at_poly (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (x y strip : List Nat) (i : Nat) (hx : allTritList x) (hy : allTritList y)
    (ht : allTritList strip) (hi : i < n)
    (hspan : ∀ j, j < n → i + j < strip.length) :
    polyVal n k hn hk (schoolAt n x y false i strip) =
      stripAdd (polyVal n k hn hk strip) (rowSplat n k hn hk x i (coeff y i)) ∧
    allTritList (schoolAt n x y false i strip) ∧
    (schoolAt n x y false i strip).length = strip.length := by
  unfold schoolAt
  by_cases hc0 : coeff y i = 0
  · simp only [hc0, ite_true]
    refine ⟨?_, ht, trivial⟩
    rw [rowSplat_zero]
    exact (stripAdd_right_zero _ (polyVal_trits n k hn hk strip ht)
      (polyVal_len n k hn hk strip)).symm
  · simp only [hc0, ite_false]
    rw [bne_false]
    have hc : coeff y i = 1 ∨ coeff y i = 2 := by
      have hle := coeff_le hy i
      omega
    obtain ⟨hp, htR, hlenR⟩ := rowAt_poly n k hn hk x strip i n (decide (coeff y i = 2))
      hspan ht hx
    rw [schoolRow_eq_rowAt]
    refine ⟨?_, htR, hlenR⟩
    rw [hp, row_match n k hn hk x i (coeff y i) hx hc]

private theorem down_inv (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (steps : Nat) (hx : allTritList x) (hy : allTritList y)
    (hspan : 2 * (n - 1) < bench) (hs : steps ≤ n) :
    let b := schoolDown x y false n (List.replicate bench 0) steps
    b.length = bench ∧ allTritList b ∧
    polyVal n k hn hk b =
      (List.range steps).foldl (fun acc t =>
        stripAdd acc (rowSplat n k hn hk x (n - 1 - t) (coeff y (n - 1 - t))))
        (List.replicate n 0) := by
  induction steps with
  | zero =>
    refine ⟨by simp [schoolDown, List.length_replicate], replicate_trits _, ?_⟩
    rw [schoolDown]
    simp [List.range_zero, List.foldl_nil]
    exact polyVal_replicate n k hn hk bench
  | succ steps ih =>
    have hs' : steps ≤ n := by omega
    obtain ⟨hlen, ht, hp⟩ := ih hs'
    have hidx : n - (steps + 1) < n := by omega
    have hspanI : ∀ j, j < n → n - (steps + 1) + j <
        (schoolDown x y false n (List.replicate bench 0) steps).length := by
      intro j hj
      rw [hlen]
      have hle : n - (steps + 1) + j ≤ 2 * (n - 1) := by omega
      omega
    obtain ⟨ha, htA, hlenA⟩ := at_poly n k bench hn hk x y
      (schoolDown x y false n (List.replicate bench 0) steps) (n - (steps + 1))
      hx hy ht hidx hspanI
    refine ⟨by rw [schoolDown, hlenA, hlen], by rw [schoolDown]; exact htA, ?_⟩
    rw [schoolDown, ha, hp]
    have hrow : n - (steps + 1) = n - 1 - steps := by omega
    rw [hrow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem polyFold_congr (n k : Nat) (hn : 0 < n) (hk : k < n)
    (xs ys : List Nat) (m : Nat) (h : ∀ i, i < m → coeff xs i = coeff ys i) :
    polyFold n k hn hk xs m = polyFold n k hn hk ys m := by
  induction m with
  | zero => simp [polyFold]
  | succ m ih =>
    rw [polyFold_succ, polyFold_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h m (Nat.lt_succ_self _)]

private theorem coeff_take_eq (xs : List Nat) (n i : Nat) (hi : i < n) (hnle : n ≤ xs.length) :
    coeff (xs.take n) i = coeff xs i := by
  have hlen : i < (xs.take n).length := by
    rw [List.length_take, Nat.min_eq_left hnle]; exact hi
  rw [coeff_eq_get _ i hlen, List.getElem_take, coeff_eq_get xs i (by omega)]

private theorem polyFrom_zeros (n k : Nat) (hn : 0 < n) (hk : k < n)
    (xs : List Nat) (s : Nat) (h : ∀ i, s ≤ i → coeff xs i = 0) :
    polyFrom n k hn hk xs s = List.replicate n 0 := by
  suffices ∀ fuel s, (∀ i, s ≤ i → coeff xs i = 0) → xs.length - s ≤ fuel →
      polyFrom n k hn hk xs s = List.replicate n 0 from
    this (xs.length - s) s h (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro s hs0 hfuel
    rw [polyFrom_empty n k hn hk xs s (by omega)]
  | succ fuel ih =>
    intro s hs0 hfuel
    by_cases hdone : xs.length ≤ s
    · rw [polyFrom_empty n k hn hk xs s hdone]
    · rw [polyFrom_succ n k hn hk xs s hdone, hs0 s (Nat.le_refl _), splat_zero]
      have hrec := ih (s + 1) (fun i hi => hs0 i (by omega)) (by omega)
      rw [hrec, stripAdd_replicate]

private theorem foldHigh_trits (n gap : Nat) (xs : List Nat) (e : Nat) (ht : allTritList xs) :
    allTritList (foldHigh n gap e xs) := by
  unfold foldHigh
  by_cases hskip : coeff xs e = 0 ∨ e < n
  · simp only [hskip, ite_true]
    exact ht
  · simp only [hskip, ite_false]
    have hel : e < xs.length := by
      by_cases hge : e < xs.length
      · exact hge
      · exact absurd (coeff_ge xs e (Nat.le_of_not_gt hge)) (by
          intro hz; exact hskip (Or.inl hz))
    have hc : coeff xs e ≤ 2 := coeff_le ht e
    exact tritList_set _ (tritList_set _ (tritList_set xs ht e 0 (by omega))
      (e - n) _ (tritAdd_le _ _)) (e - gap) _ (tritAdd_le _ _)

private theorem reduce_poly (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) :
    polyVal n k hn hk (reduceStrip n (n - k) xs) = polyVal n k hn hk xs ∧
    allTritList (reduceStrip n (n - k) xs) := by
  unfold reduceStrip
  suffices ∀ ds, polyVal n k hn hk
        (List.foldr (fun d st => foldHigh n (n - k) (n + d) st) xs ds) = polyVal n k hn hk xs ∧
      allTritList (List.foldr (fun d st => foldHigh n (n - k) (n + d) st) xs ds) from
    this (List.range (xs.length - n))
  intro ds
  induction ds with
  | nil =>
    rw [List.foldr_nil]
    exact ⟨rfl, ht⟩
  | cons d ds ih =>
    simp only [List.foldr_cons]
    obtain ⟨hp, ht'⟩ := ih
    refine ⟨?_, foldHigh_trits n (n - k) _ (n + d) ht'⟩
    rw [foldHigh_poly n k hn hk _ (n + d) ht', hp]

private theorem polyVal_low (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) (hlen : n ≤ xs.length)
    (hhigh : ∀ i, n ≤ i → coeff xs i = 0) :
    polyVal n k hn hk xs = xs.take n := by
  have hjoin := poly_join n k hn hk xs n hlen ht
  have hfrom := polyFrom_zeros n k hn hk xs n hhigh
  have hfoldT := polyFold_trits n k hn hk xs ht n
  rw [hjoin, hfrom, stripAdd_right_zero _ hfoldT (polyFold_len n k hn hk xs n)]
  have hcong := polyFold_congr n k hn hk xs (xs.take n) n (fun i hi =>
    (coeff_take_eq xs n i hi hlen).symm)
  have htakeL : (xs.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hlen]
  have hself := polyVal_self n k hn hk (xs.take n) (allTritList_take ht n) htakeL
  unfold polyVal at hself
  rw [htakeL] at hself
  rw [← hself, hcong]

/-- SPEC.md §3 R4. The reduced schoolbook is `mulVal`. -/
theorem fieldMul_eq_mulVal (n k bench : Nat) (x y : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (hspan : 2 * (n - 1) < bench)
    (hx : allTritList x) (hy : allTritList y) :
    fieldMul n k bench x y = mulVal n k hn hk x y := by
  have hdown := down_inv n k bench hn hk x y n hx hy hspan (Nat.le_refl _)
  have hschool : schoolDown x y false n (List.replicate bench 0) n =
      school n x y (List.replicate bench 0) false :=
    schoolDown_school x y (List.replicate bench 0) false n
  have hp : polyVal n k hn hk (school n x y (List.replicate bench 0) false) =
      (List.range n).foldl (fun acc t =>
        stripAdd acc (rowSplat n k hn hk x (n - 1 - t) (coeff y (n - 1 - t))))
        (List.replicate n 0) := by
    rw [← hschool]
    exact hdown.2.2
  have hrev := sum_rev n k hn hk (fun i => rowSplat n k hn hk x i (coeff y i)) n
    (fun _ _ => rowSplat_len n k hn hk x _ _)
    (fun i _ => rowSplat_trits n k hn hk x hx i _ (coeff_le hy i))
  have hmul : mulVal n k hn hk x y =
      (List.range n).foldl (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
        (List.replicate n 0) := by
    unfold mulVal
    rfl
  have hschT : allTritList (school n x y (List.replicate bench 0) false) := by
    refine school_trits x y (List.replicate bench 0) false n (replicate_trits _) ?_
    intro i hi
    simp [List.length_replicate]
    omega
  obtain ⟨hred, htR⟩ := reduce_poly n k hn hk
    (school n x y (List.replicate bench 0) false) hschT
  have hlenS : (school n x y (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hlenR : (reduceStrip n (n - k) (school n x y (List.replicate bench 0) false)).length =
      bench := by
    rw [← laneFold, laneFold_length n (n - k) _ (by rw [hlenS]; exact hb), hlenS]
  have hhigh : ∀ i, n ≤ i →
      coeff (reduceStrip n (n - k) (school n x y (List.replicate bench 0) false)) i = 0 := by
    intro i hi
    by_cases hil : i < bench
    · have hcoe := laneFold_high n (n - k)
        (school n x y (List.replicate bench 0) false) i hn (by omega : 0 < n - k)
        (by rw [hlenS]; exact hb) hi (by rw [hlenS]; exact hil)
      simpa [laneFold] using hcoe
    · exact coeff_ge _ i (by rw [hlenR]; exact Nat.le_of_not_gt hil)
  have hlow := polyVal_low n k hn hk
    (reduceStrip n (n - k) (school n x y (List.replicate bench 0) false)) htR
    (by rw [hlenR]; exact hb) hhigh
  unfold fieldMul
  rw [← hlow, hred, hp, ← hrev, ← hmul]

end EcbsLink2.Link2
