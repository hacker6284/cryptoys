/-
  `(a · b)³ = a³ · b³`. Cubing places each peg at hole `3 i`, which is the
  field product of a list with itself twice, and that product is a
  homomorphism because multiplication associates and commutes.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldUnit

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem polyFold_congr (n k : Nat) (hn : 0 < n) (hk : k < n)
    (xs ys : List Nat) (m : Nat) (h : ∀ i, i < m → coeff xs i = coeff ys i) :
    polyFold n k hn hk xs m = polyFold n k hn hk ys m := by
  induction m with
  | zero => simp [polyFold]
  | succ m ih =>
    rw [polyFold_succ, polyFold_succ, ih (fun i hi => h i (by omega)), h m (by omega)]

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
      rw [ih (s + 1) (fun i hi => hs0 i (by omega)) (by omega), stripAdd_replicate]

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

private def combPart (bench : Nat) (x : List Nat) (m : Nat) : List Nat :=
  (List.range m).foldl (fun s i =>
      let c := coeff x i
      if c = 0 then s else s.set (3 * i) c)
    (List.replicate bench 0)

private theorem combPart_len (bench : Nat) (x : List Nat) (m : Nat) :
    (combPart bench x m).length = bench := by
  unfold combPart
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h0 : coeff x m = 0
    · simp [h0, ih]
    · simp [h0, List.length_set, ih]

private theorem combPart_succ (bench : Nat) (x : List Nat) (m : Nat) :
    combPart bench x (m + 1) =
      (if coeff x m = 0 then combPart bench x m
        else (combPart bench x m).set (3 * m) (coeff x m)) := by
  unfold combPart
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem combPart_trits (bench n : Nat) (x : List Nat) (hx : allTritList x)
    (hspan : 3 * (n - 1) < bench) (m : Nat) (hm : m ≤ n) :
    allTritList (combPart bench x m) := by
  induction m with
  | zero =>
    unfold combPart
    simp
    exact replicate_trits bench
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [combPart_succ]
    by_cases h0 : coeff x m = 0
    · simp [h0]
      exact ih hm'
    · simp [h0]
      have hidx : 3 * m < bench := by
        have hk' : m ≤ n - 1 := by omega
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 hk') hspan
      exact tritList_set _ (ih hm') (3 * m) (coeff x m) (coeff_le hx m)

private theorem combPart_fresh (bench : Nat) (x : List Nat) (i k : Nat)
    (h3 : 3 * i < bench) (hk : k ≤ i) :
    coeff (combPart bench x k) (3 * i) = 0 := by
  induction k with
  | zero =>
    unfold combPart
    rw [List.range_zero, List.foldl_nil, coeff_replicate_zero]
  | succ k ih =>
    have hk' : k < i := by omega
    rw [combPart_succ]
    by_cases h0 : coeff x k = 0
    · simp [h0]
      exact ih (by omega)
    · simp [h0]
      have hne : 3 * k ≠ 3 * i := by
        intro h
        exact Nat.ne_of_lt hk' (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h)
      rw [coeff_set_ne (combPart bench x k) (3 * k) (coeff x k) (3 * i)
          (by rw [combPart_len]; exact h3) hne]
      exact ih (by omega)

private def cubeFold (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) (m : Nat) : List Nat :=
  (List.range m).foldl (fun acc i =>
      stripAdd acc (splat n k hn hk (coeff x i) (3 * i)))
    (List.replicate n 0)

private theorem cubeFold_zero (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) :
    cubeFold n k hn hk x 0 = List.replicate n 0 := by
  simp [cubeFold]

private theorem cubeFold_succ (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) (m : Nat) :
    cubeFold n k hn hk x (m + 1) =
      stripAdd (cubeFold n k hn hk x m) (splat n k hn hk (coeff x m) (3 * m)) := by
  unfold cubeFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem cubeFold_len (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) (m : Nat) :
    (cubeFold n k hn hk x m).length = n := by
  induction m with
  | zero => simp [cubeFold]
  | succ m ih => rw [cubeFold_succ, stripAdd_length, ih]

private theorem cubeFold_trits (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat)
    (hx : allTritList x) (m : Nat) : allTritList (cubeFold n k hn hk x m) := by
  induction m with
  | zero =>
    simp [cubeFold]
    exact replicate_trits n
  | succ m ih =>
    rw [cubeFold_succ]
    exact stripAdd_trits _ _

private theorem comb_poly (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (hspan : 3 * (n - 1) < bench) (m : Nat) (hm : m ≤ n) :
    polyVal n k hn hk (combPart bench x m) = cubeFold n k hn hk x m := by
  induction m with
  | zero =>
    rw [cubeFold_zero,
      show combPart bench x 0 = List.replicate bench 0 by simp [combPart],
      polyVal_replicate]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hidx : 3 * m < bench := by
      have hk' : m ≤ n - 1 := by omega
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 hk') hspan
    have hfresh := combPart_fresh bench x m m hidx (Nat.le_refl _)
    rw [cubeFold_succ]
    by_cases h0 : coeff x m = 0
    · have hstep : combPart bench x (m + 1) = combPart bench x m := by
        rw [combPart_succ, if_pos h0]
      rw [hstep, ih hm', h0, splat_zero,
        stripAdd_right_zero _ (cubeFold_trits n k hn hk x hx m) (cubeFold_len n k hn hk x m)]
    · have hstep : combPart bench x (m + 1) =
          (combPart bench x m).set (3 * m)
            (tritAdd (coeff (combPart bench x m) (3 * m)) (coeff x m)) := by
        rw [combPart_succ, if_neg h0, hfresh, tritAdd_zero_left (coeff x m) (coeff_le hx m)]
      have ht := combPart_trits bench n x hx hspan m hm'
      rw [hstep, polyVal_set_add n k hn hk (combPart bench x m) (3 * m) (coeff x m)
          (by rw [combPart_len]; exact hidx) ht (coeff_le hx m), ih hm']

private theorem comb_full (bench : Nat) (x : List Nat) (n : Nat) :
    combPart bench x n = combStrip n bench x := by
  unfold combPart combStrip
  rfl

/-- `fieldCube` is the sum of the pegs moved to hole `3 i`. -/
private theorem fieldCube_fold (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 3 * (n - 1) < bench) (x : List Nat) (hx : allTritList x) :
    fieldCube n k bench x = cubeFold n k hn hk x n := by
  have ht := combStrip_trits x n bench hx hspan
  have hlen : n ≤ (combStrip n bench x).length := by rw [combStrip_length]; exact hb
  have hred := reduce_poly n k hn hk (combStrip n bench x) ht
  have hredL : (reduceStrip n (n - k) (combStrip n bench x)).length =
      (combStrip n bench x).length := by
    rw [← laneFold]
    exact laneFold_length n (n - k) (combStrip n bench x) hlen
  have hhigh : ∀ i, n ≤ i → coeff (reduceStrip n (n - k) (combStrip n bench x)) i = 0 := by
    intro i hi
    by_cases hib : i < (combStrip n bench x).length
    · have hgap : 0 < n - k := by omega
      rw [← laneFold, laneFold_high n (n - k) (combStrip n bench x) i hn hgap hlen hi hib]
    · exact coeff_ge _ i (by rw [hredL]; exact Nat.le_of_not_gt hib)
  have hlow := polyVal_low n k hn hk (reduceStrip n (n - k) (combStrip n bench x)) hred.2
    (by rw [hredL]; exact hlen) hhigh
  unfold fieldCube
  rw [← hlow, hred.1, ← comb_full, comb_poly n k bench hn hk x hx hspan n (Nat.le_refl _)]

private theorem mulVal_comm (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (x y : List Nat) (hx : allTritList x) (hy : allTritList y) :
    mulVal n k hn hk x y = mulVal n k hn hk y x := by
  rw [← fieldMul_eq_mulVal n k bench x y hn hk hb hspan hx hy,
    ← fieldMul_eq_mulVal n k bench y x hn hk hb hspan hy hx,
    fieldMul_comm n k bench x y hx hy]

private theorem mul_left (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (a b x : List Nat) (ha : allTritList a) (hbT : allTritList b) (hx : allTritList x)
    (haL : a.length = n) (hbL : b.length = n) :
    mulVal n k hn hk (stripAdd a b) x =
      stripAdd (mulVal n k hn hk a x) (mulVal n k hn hk b x) := by
  have hsT : allTritList (stripAdd a b) := stripAdd_trits _ _
  have hsL : (stripAdd a b).length = n := by rw [stripAdd_length, haL]
  rw [mulVal_comm n k bench hn hk hb hspan (stripAdd a b) x hsT hx,
    mulVal_add n k hn hk x a b hx haL hbL ha hbT,
    mulVal_comm n k bench hn hk hb hspan x a hx ha,
    mulVal_comm n k bench hn hk hb hspan x b hx hbT]

private theorem hot_row (n k : Nat) (hn : 0 < n) (hk : k < n)
    (e c shift d m : Nat) (he : e < n) (hc : c ≤ 2) (hd : d ≤ 2) (hm : m ≤ n) :
    (List.range m).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (tritMul d (coeff (splat n k hn hk c e) j)) (shift + j)))
      (List.replicate n 0) =
      if m ≤ e then List.replicate n 0 else splat n k hn hk (tritMul d c) (shift + e) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm',
      splat_lt n k hn hk c e he]
    by_cases hlt : m < e
    · have hle : m + 1 ≤ e := by omega
      rw [if_pos (Nat.le_of_lt hlt), if_pos hle,
        coeff_set_ne (List.replicate n 0) e c m
          (by simpa [List.length_replicate] using (by omega : m < n)) (by omega),
        coeff_replicate_zero, tritMul_zero_right d hd, splat_zero, stripAdd_replicate]
    · by_cases heq : m = e
      · have hgt : ¬ m + 1 ≤ e := by omega
        rw [if_pos (by omega : m ≤ e), if_neg hgt, heq,
          coeff_set_eq (List.replicate n 0) e c (by simpa [List.length_replicate] using he)]
        have hz := stripAdd_left_zero (splat n k hn hk (tritMul d c) (shift + e))
          (splat_trits n k hn hk _ _ (tritMul_le d c hd hc))
        simp only [splat_len] at hz
        exact hz
      · have hgt : ¬ m ≤ e := by omega
        have hgt1 : ¬ m + 1 ≤ e := by omega
        rw [if_neg hgt, if_neg hgt1,
          coeff_set_ne (List.replicate n 0) e c m
            (by simpa [List.length_replicate] using (by omega : m < n)) (by omega),
          coeff_replicate_zero, tritMul_zero_right d hd, splat_zero,
          stripAdd_right_zero _ (splat_trits n k hn hk _ _ (tritMul_le d c hd hc))
            (by rw [splat_len])]

private theorem row_hot (n k : Nat) (hn : 0 < n) (hk : k < n)
    (e c shift d : Nat) (he : e < n) (hc : c ≤ 2) (hd : d ≤ 2) :
    rowSplat n k hn hk (splat n k hn hk c e) shift d =
      splat n k hn hk (tritMul d c) (shift + e) := by
  unfold rowSplat
  rw [hot_row n k hn hk e c shift d n he hc hd (Nat.le_refl _),
    if_neg (by omega : ¬ n ≤ e)]

/-- One peg cubed is that peg at hole `3 e`. -/
private theorem splat_cube (n k : Nat) (hn : 0 < n) (hk : k < n)
    (c e : Nat) (hc : c ≤ 2) (he : e < n) :
    mulVal n k hn hk (splat n k hn hk c e)
        (mulVal n k hn hk (splat n k hn hk c e) (splat n k hn hk c e)) =
      splat n k hn hk c (3 * e) := by
  have hc2 : tritMul c c ≤ 2 := tritMul_le c c hc hc
  have hsq : mulVal n k hn hk (splat n k hn hk c e) (splat n k hn hk c e) =
      splat n k hn hk (tritMul c c) (e + e) := by
    rw [mulVal_splat n k hn hk (splat n k hn hk c e) (splat_trits n k hn hk c e hc) c e hc,
      row_hot n k hn hk e c e c he hc hc, tritMul_comm c c hc hc]
  rw [hsq, mulVal_splat n k hn hk (splat n k hn hk c e) (splat_trits n k hn hk c e hc)
      (tritMul c c) (e + e) hc2,
    row_hot n k hn hk e c (e + e) (tritMul c c) he hc hc2]
  have hmul := tritMul_assoc c c c hc hc hc
  have hcube := trit_cube c hc
  rw [hmul, hcube]
  have hexp : e + e + e = 3 * e := by omega
  rw [hexp]

private theorem trit8 (a x y b : Nat) (ha : a ≤ 2) (hx : x ≤ 2) (hy : y ≤ 2) (hb : b ≤ 2) :
    tritAdd (tritAdd (tritAdd a x) (tritAdd x y)) (tritAdd (tritAdd x y) (tritAdd y b)) =
      tritAdd (tritAdd a b) (tritAdd (tritAdd (tritAdd x x) x) (tritAdd (tritAdd y y) y)) := by
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hy3 : y = 0 ∨ y = 1 ∨ y = 2 := by omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha3 with rfl | rfl | rfl <;>
    rcases hx3 with rfl | rfl | rfl <;>
    rcases hy3 with rfl | rfl | rfl <;>
    rcases hb3 with rfl | rfl | rfl <;>
    rfl

private theorem strip_field (n : Nat) (u v : List Nat) (hu : u.length = n) :
    stripAdd u v = fieldAdd n u v := by
  unfold stripAdd fieldAdd
  rw [hu]

private theorem triple_zero (n : Nat) (x : List Nat) (hx : allTritList x) (hlen : x.length = n) :
    stripAdd (stripAdd x x) x = List.replicate n 0 := by
  rw [strip_field n (stripAdd x x) x (by rw [stripAdd_length, hlen]),
    strip_field n x x hlen, fieldAdd_triple n x hx hlen, zeroPeg]

private theorem coeff_left8 (n : Nat) (a3 x y b3 : List Nat) (i : Nat)
    (ha : a3.length = n) (hx : x.length = n) (hy : y.length = n) (hb : b3.length = n)
    (hi : i < n) :
    coeff (stripAdd (stripAdd (stripAdd a3 x) (stripAdd x y))
        (stripAdd (stripAdd x y) (stripAdd y b3))) i =
      tritAdd (tritAdd (tritAdd (coeff a3 i) (coeff x i)) (tritAdd (coeff x i) (coeff y i)))
        (tritAdd (tritAdd (coeff x i) (coeff y i)) (tritAdd (coeff y i) (coeff b3 i))) := by
  have hxL : i < x.length := by rw [hx]; exact hi
  have hyL : i < y.length := by rw [hy]; exact hi
  have haL : i < a3.length := by rw [ha]; exact hi
  have hxy : i < (stripAdd x y).length := by rw [stripAdd_length, hx]; exact hi
  have hyb : i < (stripAdd y b3).length := by rw [stripAdd_length, hy]; exact hi
  have hl : i < (stripAdd (stripAdd a3 x) (stripAdd x y)).length := by
    rw [stripAdd_length, stripAdd_length, ha]; exact hi
  have hax : i < (stripAdd a3 x).length := by rw [stripAdd_length, ha]; exact hi
  rw [stripAdd_coeff _ _ i hl, stripAdd_coeff _ _ i hax, stripAdd_coeff _ _ i hxL,
    stripAdd_coeff _ _ i hxy, stripAdd_coeff _ _ i hxL, stripAdd_coeff _ _ i hyL,
    stripAdd_coeff a3 x i haL]

private theorem coeff_right8 (n : Nat) (a3 x y b3 : List Nat) (i : Nat)
    (ha : a3.length = n) (hx : x.length = n) (hy : y.length = n) (hb : b3.length = n)
    (hi : i < n) :
    coeff (stripAdd (stripAdd a3 b3)
        (stripAdd (stripAdd (stripAdd x x) x) (stripAdd (stripAdd y y) y))) i =
      tritAdd (tritAdd (coeff a3 i) (coeff b3 i))
        (tritAdd (tritAdd (tritAdd (coeff x i) (coeff x i)) (coeff x i))
          (tritAdd (tritAdd (coeff y i) (coeff y i)) (coeff y i))) := by
  have haL : i < a3.length := by rw [ha]; exact hi
  have hxx : i < (stripAdd x x).length := by rw [stripAdd_length, hx]; exact hi
  have hyy : i < (stripAdd y y).length := by rw [stripAdd_length, hy]; exact hi
  have hx3 : i < (stripAdd (stripAdd x x) x).length := by
    rw [stripAdd_length, stripAdd_length, hx]; exact hi
  have hl : i < (stripAdd a3 b3).length := by rw [stripAdd_length, ha]; exact hi
  have hxL : i < x.length := by rw [hx]; exact hi
  have hyL : i < y.length := by rw [hy]; exact hi
  rw [stripAdd_coeff (stripAdd a3 b3)
      (stripAdd (stripAdd (stripAdd x x) x) (stripAdd (stripAdd y y) y)) i hl]
  rw [stripAdd_coeff a3 b3 i haL]
  rw [stripAdd_coeff (stripAdd (stripAdd x x) x) (stripAdd (stripAdd y y) y) i hx3]
  rw [stripAdd_coeff (stripAdd x x) x i hxx, stripAdd_coeff x x i hxL]
  rw [stripAdd_coeff (stripAdd y y) y i hyy, stripAdd_coeff y y i hyL]

private theorem oct_lists (n : Nat) (a3 x y b3 : List Nat)
    (haL : a3.length = n) (hxL : x.length = n) (hyL : y.length = n) (hbL : b3.length = n)
    (ha : allTritList a3) (hx : allTritList x) (hy : allTritList y) (hb : allTritList b3) :
    stripAdd (stripAdd (stripAdd a3 x) (stripAdd x y))
        (stripAdd (stripAdd x y) (stripAdd y b3)) =
      stripAdd (stripAdd a3 b3)
        (stripAdd (stripAdd (stripAdd x x) x) (stripAdd (stripAdd y y) y)) := by
  refine lists_coeff (by simp only [stripAdd_length, haL]) ?_
  intro i
  by_cases hi : i < n
  · rw [coeff_left8 n a3 x y b3 i haL hxL hyL hbL hi,
      coeff_right8 n a3 x y b3 i haL hxL hyL hbL hi]
    exact trit8 _ _ _ _ (coeff_le ha i) (coeff_le hx i) (coeff_le hy i) (coeff_le hb i)
  · have hle : n ≤ i := Nat.le_of_not_gt hi
    rw [coeff_ge _ i (by simp only [stripAdd_length, haL]; exact hle),
      coeff_ge _ i (by simp only [stripAdd_length, haL]; exact hle)]

private theorem cu_add (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (a b : List Nat) (ha : allTritList a) (hbT : allTritList b)
    (haL : a.length = n) (hbL : b.length = n) :
    mulVal n k hn hk (stripAdd a b) (mulVal n k hn hk (stripAdd a b) (stripAdd a b)) =
      stripAdd (mulVal n k hn hk a (mulVal n k hn hk a a))
        (mulVal n k hn hk b (mulVal n k hn hk b b)) := by
  have hsT : allTritList (stripAdd a b) := stripAdd_trits a b
  have hsL : (stripAdd a b).length = n := by rw [stripAdd_length, haL]
  have haaT := mulVal_trits n k hn hk a a ha ha
  have habT := mulVal_trits n k hn hk a b ha hbT
  have hbaT := mulVal_trits n k hn hk b a hbT ha
  have hbbT := mulVal_trits n k hn hk b b hbT hbT
  have haaL := mulVal_len n k hn hk a a
  have habL := mulVal_len n k hn hk a b
  have hbaL := mulVal_len n k hn hk b a
  have hbbL := mulVal_len n k hn hk b b
  have hsq : mulVal n k hn hk (stripAdd a b) (stripAdd a b) =
      stripAdd (stripAdd (mulVal n k hn hk a a) (mulVal n k hn hk b a))
        (stripAdd (mulVal n k hn hk a b) (mulVal n k hn hk b b)) := by
    rw [mulVal_add n k hn hk (stripAdd a b) a b hsT haL hbL ha hbT,
      mul_left n k bench hn hk hb hspan a b a ha hbT ha haL hbL,
      mul_left n k bench hn hk hb hspan a b b ha hbT hbT haL hbL]
  have hsqT : allTritList (mulVal n k hn hk (stripAdd a b) (stripAdd a b)) :=
    mulVal_trits n k hn hk _ _ hsT hsT
  have hsqL : (mulVal n k hn hk (stripAdd a b) (stripAdd a b)).length = n :=
    mulVal_len n k hn hk _ _
  rw [hsq]
  have hdist : mulVal n k hn hk (stripAdd a b)
        (stripAdd (stripAdd (mulVal n k hn hk a a) (mulVal n k hn hk b a))
          (stripAdd (mulVal n k hn hk a b) (mulVal n k hn hk b b))) =
      stripAdd
        (mulVal n k hn hk (stripAdd a b)
          (stripAdd (mulVal n k hn hk a a) (mulVal n k hn hk b a)))
        (mulVal n k hn hk (stripAdd a b)
          (stripAdd (mulVal n k hn hk a b) (mulVal n k hn hk b b))) := by
    exact mulVal_add n k hn hk (stripAdd a b) _ _ hsT
      (by rw [stripAdd_length, haaL]) (by rw [stripAdd_length, habL])
      (stripAdd_trits _ _) (stripAdd_trits _ _)
  rw [hdist]
  have hL : mulVal n k hn hk (stripAdd a b)
        (stripAdd (mulVal n k hn hk a a) (mulVal n k hn hk b a)) =
      stripAdd (mulVal n k hn hk (stripAdd a b) (mulVal n k hn hk a a))
        (mulVal n k hn hk (stripAdd a b) (mulVal n k hn hk b a)) :=
    mulVal_add n k hn hk _ _ _ hsT haaL hbaL haaT hbaT
  have hR : mulVal n k hn hk (stripAdd a b)
        (stripAdd (mulVal n k hn hk a b) (mulVal n k hn hk b b)) =
      stripAdd (mulVal n k hn hk (stripAdd a b) (mulVal n k hn hk a b))
        (mulVal n k hn hk (stripAdd a b) (mulVal n k hn hk b b)) :=
    mulVal_add n k hn hk _ _ _ hsT habL hbbL habT hbbT
  rw [hL, hR]
  rw [mul_left n k bench hn hk hb hspan a b (mulVal n k hn hk a a) ha hbT haaT haL hbL,
    mul_left n k bench hn hk hb hspan a b (mulVal n k hn hk b a) ha hbT hbaT haL hbL,
    mul_left n k bench hn hk hb hspan a b (mulVal n k hn hk a b) ha hbT habT haL hbL,
    mul_left n k bench hn hk hb hspan a b (mulVal n k hn hk b b) ha hbT hbbT haL hbL]
  -- Eight products. Each cross term is `(a·a)·b` or `a·(b·b)`.
  have e_baa : mulVal n k hn hk b (mulVal n k hn hk a a) =
      mulVal n k hn hk (mulVal n k hn hk a a) b :=
    mulVal_comm n k bench hn hk hb hspan b (mulVal n k hn hk a a) hbT haaT
  have e_aba : mulVal n k hn hk a (mulVal n k hn hk b a) =
      mulVal n k hn hk (mulVal n k hn hk a a) b := by
    rw [mulVal_comm n k bench hn hk hb hspan b a hbT ha,
      (mulVal_assoc n k hn hk a a b ha ha hbT).symm]
  have e_bba : mulVal n k hn hk b (mulVal n k hn hk b a) =
      mulVal n k hn hk a (mulVal n k hn hk b b) := by
    rw [(mulVal_assoc n k hn hk b b a hbT hbT ha).symm,
      mulVal_comm n k bench hn hk hb hspan (mulVal n k hn hk b b) a hbbT ha]
  have e_aab : mulVal n k hn hk a (mulVal n k hn hk a b) =
      mulVal n k hn hk (mulVal n k hn hk a a) b :=
    (mulVal_assoc n k hn hk a a b ha ha hbT).symm
  have e_bab : mulVal n k hn hk b (mulVal n k hn hk a b) =
      mulVal n k hn hk a (mulVal n k hn hk b b) := by
    rw [mulVal_comm n k bench hn hk hb hspan a b ha hbT,
      (mulVal_assoc n k hn hk b b a hbT hbT ha).symm,
      mulVal_comm n k bench hn hk hb hspan (mulVal n k hn hk b b) a hbbT ha]
  rw [e_baa, e_aba, e_bba, e_aab, e_bab]
  have hxT := mulVal_trits n k hn hk (mulVal n k hn hk a a) b haaT hbT
  have hyT := mulVal_trits n k hn hk a (mulVal n k hn hk b b) ha hbbT
  have hxL := mulVal_len n k hn hk (mulVal n k hn hk a a) b
  have hyL := mulVal_len n k hn hk a (mulVal n k hn hk b b)
  have ha3L := mulVal_len n k hn hk a (mulVal n k hn hk a a)
  have hb3L := mulVal_len n k hn hk b (mulVal n k hn hk b b)
  have ha3T := mulVal_trits n k hn hk a (mulVal n k hn hk a a) ha haaT
  have hb3T := mulVal_trits n k hn hk b (mulVal n k hn hk b b) hbT hbbT
  rw [oct_lists n (mulVal n k hn hk a (mulVal n k hn hk a a))
      (mulVal n k hn hk (mulVal n k hn hk a a) b)
      (mulVal n k hn hk a (mulVal n k hn hk b b))
      (mulVal n k hn hk b (mulVal n k hn hk b b))
      ha3L hxL hyL hb3L ha3T hxT hyT hb3T,
    triple_zero n _ hxT hxL, triple_zero n _ hyT hyL, stripAdd_replicate,
    stripAdd_right_zero _ (stripAdd_trits _ _) (by rw [stripAdd_length, ha3L])]

private theorem cu_poly (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (x : List Nat) (hx : allTritList x) (m : Nat) (hm : m ≤ n) :
    mulVal n k hn hk (polyFold n k hn hk x m)
        (mulVal n k hn hk (polyFold n k hn hk x m) (polyFold n k hn hk x m)) =
      cubeFold n k hn hk x m := by
  induction m with
  | zero =>
    simp [polyFold, cubeFold]
    rw [mulVal_zero n k hn hk (List.replicate n 0), mulVal_zero n k hn hk (List.replicate n 0)]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hc : coeff x m ≤ 2 := coeff_le hx m
    have hpfT := polyFold_trits n k hn hk x hx m
    have hpfL := polyFold_len n k hn hk x m
    have hspT := splat_trits n k hn hk (coeff x m) m hc
    rw [polyFold_succ, cubeFold_succ,
      cu_add n k bench hn hk hb hspan (polyFold n k hn hk x m) (splat n k hn hk (coeff x m) m)
        hpfT hspT hpfL (by rw [splat_len]),
      ih hm', splat_cube n k hn hk (coeff x m) m hc (by omega)]

private def peg (n : Nat) (x : List Nat) : List Nat :=
  (List.range n).map fun i => coeff x i

private theorem peg_len (n : Nat) (x : List Nat) : (peg n x).length = n := by
  simp [peg, List.length_map, List.length_range]

private theorem peg_coeff (n : Nat) (x : List Nat) (i : Nat) (hi : i < n) :
    coeff (peg n x) i = coeff x i := by
  rw [coeff_eq_get _ i (by rw [peg_len]; exact hi)]
  simp [peg, List.getElem_map, List.getElem_range]

private theorem peg_trits (n : Nat) (x : List Nat) (hx : allTritList x) : allTritList (peg n x) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  simp [peg, List.getElem_map, List.getElem_range]
  exact coeff_le hx _

private theorem row_coeff (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x p : List Nat) (h : ∀ j, j < n → coeff x j = coeff p j)
    (i c m : Nat) (hm : m ≤ n) :
    (List.range m).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (tritMul c (coeff x j)) (i + j))) (List.replicate n 0) =
      (List.range m).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (tritMul c (coeff p j)) (i + j))) (List.replicate n 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
      ih (by omega), h m (by omega)]

private theorem mul_coeff (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y p q : List Nat)
    (hx : ∀ i, i < n → coeff x i = coeff p i) (hy : ∀ i, i < n → coeff y i = coeff q i) :
    mulVal n k hn hk x y = mulVal n k hn hk p q := by
  unfold mulVal
  suffices ∀ m, m ≤ n →
      (List.range m).foldl (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
        (List.replicate n 0) =
      (List.range m).foldl (fun acc i => stripAdd acc (rowSplat n k hn hk p i (coeff q i)))
        (List.replicate n 0) by
    exact this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil, ih (by omega), hy m (by omega)]
    unfold rowSplat
    rw [row_coeff n k hn hk x p hx m (coeff q m) n (Nat.le_refl _)]

private theorem cube_coeff (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x p : List Nat) (h : ∀ i, i < n → coeff x i = coeff p i) (m : Nat) (hm : m ≤ n) :
    cubeFold n k hn hk x m = cubeFold n k hn hk p m := by
  induction m with
  | zero => simp [cubeFold]
  | succ m ih =>
    rw [cubeFold_succ, cubeFold_succ, ih (by omega), h m (by omega)]

/-- Cubing a trit list is the field product of the list with itself, twice. -/
theorem fieldCube_cu (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (x : List Nat) (hx : allTritList x) :
    fieldCube n k bench x =
      mulVal n k hn hk x (mulVal n k hn hk x x) := by
  have hpeg : ∀ i, i < n → coeff x i = coeff (peg n x) i := fun i hi => (peg_coeff n x i hi).symm
  have hfold := fieldCube_fold n k bench hn hk hb h3 x hx
  have hpoly : polyFold n k hn hk (peg n x) n = peg n x := by
    have hself := polyVal_self n k hn hk (peg n x) (peg_trits n x hx) (peg_len n x)
    unfold polyVal at hself
    rw [peg_len] at hself
    exact hself
  have hfrom : ∀ i, i < n → coeff (peg n x) i = coeff x i := fun i hi => peg_coeff n x i hi
  have hmul : mulVal n k hn hk (peg n x) (peg n x) = mulVal n k hn hk x x :=
    mul_coeff n k hn hk (peg n x) (peg n x) x x hfrom hfrom
  have hmul2 : mulVal n k hn hk (peg n x) (mulVal n k hn hk (peg n x) (peg n x)) =
      mulVal n k hn hk x (mulVal n k hn hk x x) :=
    mul_coeff n k hn hk (peg n x) (mulVal n k hn hk (peg n x) (peg n x)) x
      (mulVal n k hn hk x x) hfrom (fun i hi => by rw [hmul])
  rw [hfold, cube_coeff n k hn hk x (peg n x) hpeg n (Nat.le_refl _),
    ← cu_poly n k bench hn hk hb h2 (peg n x) (peg_trits n x hx) n (Nat.le_refl _),
    hpoly, hmul2]

private theorem cu_prod (n k bench : Nat) (hn : 0 < n) (hk : k < n)
    (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (a b : List Nat) (ha : allTritList a) (hbT : allTritList b) :
    mulVal n k hn hk (mulVal n k hn hk a b)
        (mulVal n k hn hk (mulVal n k hn hk a b) (mulVal n k hn hk a b)) =
      mulVal n k hn hk (mulVal n k hn hk a (mulVal n k hn hk a a))
        (mulVal n k hn hk b (mulVal n k hn hk b b)) := by
  have habT := mulVal_trits n k hn hk a b ha hbT
  have haaT := mulVal_trits n k hn hk a a ha ha
  have hbbT := mulVal_trits n k hn hk b b hbT hbT
  have habbT := mulVal_trits n k hn hk (mulVal n k hn hk a b) (mulVal n k hn hk a b) habT habT
  rw [mulVal_assoc n k hn hk a b (mulVal n k hn hk (mulVal n k hn hk a b) (mulVal n k hn hk a b))
      ha hbT habbT,
    mulVal_assoc n k hn hk a b (mulVal n k hn hk a b) ha hbT habT]
  rw [mulVal_comm n k bench hn hk hb hspan a b ha hbT]
  rw [(mulVal_assoc n k hn hk b b a hbT hbT ha).symm]
  rw [mulVal_comm n k bench hn hk hb hspan (mulVal n k hn hk b b) a hbbT ha]
  rw [(mulVal_assoc n k hn hk a a (mulVal n k hn hk b b) ha ha hbbT).symm]
  rw [(mulVal_assoc n k hn hk b (mulVal n k hn hk a a) (mulVal n k hn hk b b) hbT haaT hbbT).symm]
  rw [mulVal_comm n k bench hn hk hb hspan b (mulVal n k hn hk a a) hbT haaT]
  rw [mulVal_assoc n k hn hk (mulVal n k hn hk a a) b (mulVal n k hn hk b b) haaT hbT hbbT]
  rw [(mulVal_assoc n k hn hk a (mulVal n k hn hk a a) (mulVal n k hn hk b (mulVal n k hn hk b b))
      ha haaT (mulVal_trits n k hn hk b (mulVal n k hn hk b b) hbT hbbT)).symm]

/-- `(a · b)³ = a³ · b³`. The triple span is the room the comb needs to lay peg `i` at hole `3 i`. -/
theorem fieldCube_mul (n k bench : Nat) (a b : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench) (h3 : 3 * (n - 1) < bench)
    (ha : allTritList a) (hbT : allTritList b) :
    fieldCube n k bench (fieldMul n k bench a b) =
      fieldMul n k bench (fieldCube n k bench a) (fieldCube n k bench b) := by
  have habT : allTritList (fieldMul n k bench a b) := by
    rw [fieldMul_eq_mulVal n k bench a b hn hk hb h2 ha hbT]
    exact mulVal_trits n k hn hk a b ha hbT
  have hcaT := fieldCube_trits n k bench a ha h3 (Nat.le_of_lt hk)
  have hcbT := fieldCube_trits n k bench b hbT h3 (Nat.le_of_lt hk)
  rw [fieldCube_cu n k bench hn hk hb h2 h3 (fieldMul n k bench a b) habT,
    fieldMul_eq_mulVal n k bench a b hn hk hb h2 ha hbT,
    cu_prod n k bench hn hk hb h2 a b ha hbT,
    ← fieldCube_cu n k bench hn hk hb h2 h3 a ha,
    ← fieldCube_cu n k bench hn hk hb h2 h3 b hbT,
    ← fieldMul_eq_mulVal n k bench (fieldCube n k bench a) (fieldCube n k bench b)
        hn hk hb h2 hcaT hcbT]

end EcbsLink2.Link2
