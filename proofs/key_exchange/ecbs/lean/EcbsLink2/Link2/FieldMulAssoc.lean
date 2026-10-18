/-
  `fieldMul` associates. A product is a sum of reduced rows, a row is a
  sum of reduced powers, and shifting a power moves its exponent.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldBridge

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem mulVal_trits (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (_hx : allTritList x) (_hy : allTritList y) :
    allTritList (mulVal n k hn hk x y) := by
  unfold mulVal
  suffices ∀ m, m ≤ n → allTritList ((List.range m).foldl
      (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
      (List.replicate n 0)) by
    exact this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    simp
    exact replicate_trits n
  | succ m ih =>
    intro _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact stripAdd_trits _ _

private theorem shift_replicate (n k : Nat) (hn : 0 < n) (hk : k < n) (s : Nat) :
    shiftAdd n k hn hk s (List.replicate n 0) = List.replicate n 0 := by
  unfold shiftAdd
  suffices ∀ m, m ≤ n → (List.range m).foldl
      (fun acc t => stripAdd acc (splat n k hn hk (coeff (List.replicate n 0) t) (t + s)))
      (List.replicate n 0) = List.replicate n 0 by
    exact this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      coeff_replicate_zero, splat_zero, stripAdd_replicate]

private theorem scale_replicate (n c : Nat) (hc : c ≤ 2) :
    scaleList n c (List.replicate n 0) = List.replicate n 0 := by
  refine lists_coeff (by simp [scaleList_len, List.length_replicate]) ?_
  intro i
  by_cases hi : i < n
  · rw [scaleList_coeff n c (List.replicate n 0) i hi, coeff_replicate_zero,
      tritMul_zero_right c hc]
  · rw [coeff_ge _ i (by rw [scaleList_len]; exact Nat.le_of_not_gt hi),
      coeff_ge _ i (by simp [List.length_replicate]; exact Nat.le_of_not_gt hi)]

private theorem scaleList_trits (n c : Nat) (xs : List Nat) (hc : c ≤ 2) (hx : allTritList xs) :
    allTritList (scaleList n c xs) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hi' : i < n := by rw [scaleList_len] at hi; exact hi
  rw [scaleList_get n c xs i hi']
  exact tritMul_le c _ hc (coeff_le hx i)

private def rowPart (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d m : Nat) : List Nat :=
  (List.range m).foldl (fun acc j =>
      stripAdd acc (splat n k hn hk (tritMul d (coeff x j)) (i + j)))
    (List.replicate n 0)

private def scaledPart (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d c a m : Nat) : List Nat :=
  (List.range m).foldl (fun acc j =>
      stripAdd acc (splat n k hn hk (tritMul c (tritMul d (coeff x j))) (i + j + a)))
    (List.replicate n 0)

private theorem rowPart_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d m : Nat) : (rowPart n k hn hk x i d m).length = n := by
  unfold rowPart
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

private theorem rowPart_trits (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d m : Nat) :
    allTritList (rowPart n k hn hk x i d m) := by
  unfold rowPart
  induction m with
  | zero =>
    simp
    exact replicate_trits n
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact stripAdd_trits _ _

private theorem rowPart_succ (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d m : Nat) :
    rowPart n k hn hk x i d (m + 1) =
      stripAdd (rowPart n k hn hk x i d m)
        (splat n k hn hk (tritMul d (coeff x m)) (i + m)) := by
  unfold rowPart
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem scaledPart_succ (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d c a m : Nat) :
    scaledPart n k hn hk x i d c a (m + 1) =
      stripAdd (scaledPart n k hn hk x i d c a m)
        (splat n k hn hk (tritMul c (tritMul d (coeff x m))) (i + m + a)) := by
  unfold scaledPart
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem row_full (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (i d : Nat) :
    rowPart n k hn hk x i d n = rowSplat n k hn hk x i d := by
  unfold rowPart rowSplat
  rfl

/-- Scaling a row and shifting it scales each peg and moves the row. -/
private theorem row_scale_shift (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (i d c a m : Nat)
    (hd : d ≤ 2) (hc : c ≤ 2) (hm : m ≤ n) :
    shiftAdd n k hn hk a (scaleList n c (rowPart n k hn hk x i d m)) =
      scaledPart n k hn hk x i d c a m := by
  induction m with
  | zero =>
    rw [show rowPart n k hn hk x i d 0 = List.replicate n 0 by simp [rowPart]]
    rw [scale_replicate n c hc, shift_replicate n k hn hk a]
    simp [scaledPart]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hdx : tritMul d (coeff x m) ≤ 2 :=
      tritMul_le d (coeff x m) hd (coeff_le hx m)
    conv =>
      rhs
      rw [scaledPart_succ]
    rw [rowPart_succ]
    have hscale := scale_stripAdd n c (rowPart n k hn hk x i d m)
      (splat n k hn hk (tritMul d (coeff x m)) (i + m)) hc
      (rowPart_trits n k hn hk x i d m)
      (splat_trits n k hn hk _ _ hdx)
      (by rw [splat_len, rowPart_len]) (by rw [rowPart_len])
    rw [hscale]
    have hshift := shift_add n k hn hk a
      (scaleList n c (rowPart n k hn hk x i d m))
      (scaleList n c (splat n k hn hk (tritMul d (coeff x m)) (i + m)))
      (by rw [scaleList_len]) (by rw [scaleList_len])
      (scaleList_trits n c _ hc (rowPart_trits n k hn hk x i d m))
      (scaleList_trits n c _ hc (splat_trits n k hn hk _ _ hdx))
    rw [hshift, ih hm',
      ← splat_scale n k hn hk c (tritMul d (coeff x m)) (i + m) hc hdx,
      shift_splat n k hn hk (tritMul c (tritMul d (coeff x m))) (i + m) a
        (tritMul_le c _ hc hdx)]

private def prodPart (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) : List Nat :=
  (List.range m).foldl (fun acc i => stripAdd acc (rowPart n k hn hk x i (coeff y i) n))
    (List.replicate n 0)

private theorem prod_full (n k : Nat) (hn : 0 < n) (hk : k < n) (x y : List Nat) :
    prodPart n k hn hk x y n = mulVal n k hn hk x y := by
  unfold prodPart mulVal
  suffices ∀ m, m ≤ n →
      (List.range m).foldl (fun acc i => stripAdd acc (rowPart n k hn hk x i (coeff y i) n))
        (List.replicate n 0) =
      (List.range m).foldl (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
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
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
      ih (by omega), row_full]

private theorem prodPart_trits (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) :
    allTritList (prodPart n k hn hk x y m) := by
  unfold prodPart
  induction m with
  | zero =>
    simp
    exact replicate_trits n
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact stripAdd_trits _ _

private theorem prodPart_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) : (prodPart n k hn hk x y m).length = n := by
  unfold prodPart
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

private theorem prodPart_succ (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) :
    prodPart n k hn hk x y (m + 1) =
      stripAdd (prodPart n k hn hk x y m) (rowPart n k hn hk x m (coeff y m) n) := by
  unfold prodPart
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem row_as_shift (n k : Nat) (hn : 0 < n) (hk : k < n)
    (p : List Nat) (c a : Nat) (hp : p.length = n) (_hc : c ≤ 2) :
    rowSplat n k hn hk p a c = shiftAdd n k hn hk a (scaleList n c p) := by
  unfold rowSplat shiftAdd
  suffices ∀ m, m ≤ n →
      (List.range m).foldl (fun acc j =>
          stripAdd acc (splat n k hn hk (tritMul c (coeff p j)) (a + j)))
        (List.replicate n 0) =
      (List.range m).foldl (fun acc t =>
          stripAdd acc (splat n k hn hk (coeff (scaleList n c p) t) (t + a)))
        (List.replicate n 0) by
    exact this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    conv =>
      lhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega), scaleList_coeff n c p m (by omega), Nat.add_comm a m]

private theorem fold_strip_congr (n : Nat) (f g : Nat → List Nat) (m : Nat)
    (h : ∀ i, i < m → f i = g i) :
    (List.range m).foldl (fun acc i => stripAdd acc (f i)) (List.replicate n 0) =
      (List.range m).foldl (fun acc i => stripAdd acc (g i)) (List.replicate n 0) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
      ih (fun i hi => h i (by omega)), h m (by omega)]

/-- The rows of `z`, each one the scaled shifted product `x · y`. -/
private def triRows (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (a : Nat) : List Nat :=
  (List.range n).foldl (fun acc i =>
      stripAdd acc (scaledPart n k hn hk x i (coeff y i) (coeff z a) a n))
    (List.replicate n 0)

private def triAll (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) : List Nat :=
  (List.range n).foldl (fun acc a => stripAdd acc (triRows n k hn hk x y z a))
    (List.replicate n 0)

private theorem shift_scale_prod (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (hx : allTritList x) (hy : allTritList y)
    (a c m : Nat) (hc : c ≤ 2) (hm : m ≤ n) :
    shiftAdd n k hn hk a (scaleList n c (prodPart n k hn hk x y m)) =
      (List.range m).foldl (fun acc i =>
          stripAdd acc (scaledPart n k hn hk x i (coeff y i) c a n))
        (List.replicate n 0) := by
  induction m with
  | zero =>
    rw [show prodPart n k hn hk x y 0 = List.replicate n 0 by simp [prodPart]]
    rw [scale_replicate n c hc, shift_replicate n k hn hk a]
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hyi : coeff y m ≤ 2 := coeff_le hy m
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [prodPart_succ]
    have hscale := scale_stripAdd n c (prodPart n k hn hk x y m)
      (rowPart n k hn hk x m (coeff y m) n) hc
      (prodPart_trits n k hn hk x y m)
      (rowPart_trits n k hn hk x m (coeff y m) n)
      (by rw [rowPart_len, prodPart_len]) (by rw [prodPart_len])
    rw [hscale]
    have hshift := shift_add n k hn hk a
      (scaleList n c (prodPart n k hn hk x y m))
      (scaleList n c (rowPart n k hn hk x m (coeff y m) n))
      (by rw [scaleList_len]) (by rw [scaleList_len])
      (scaleList_trits n c _ hc (prodPart_trits n k hn hk x y m))
      (scaleList_trits n c _ hc (rowPart_trits n k hn hk x m (coeff y m) n))
    rw [hshift, ih hm',
      row_scale_shift n k hn hk x hx m (coeff y m) c a n hyi hc (Nat.le_refl n)]

private theorem mul_left_tri (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) :
    mulVal n k hn hk (mulVal n k hn hk x y) z = triAll n k hn hk x y z := by
  have hxyL := mulVal_len n k hn hk x y
  have hleft : mulVal n k hn hk (mulVal n k hn hk x y) z =
      (List.range n).foldl (fun acc a =>
        stripAdd acc (shiftAdd n k hn hk a
          (scaleList n (coeff z a) (mulVal n k hn hk x y)))) (List.replicate n 0) := by
    unfold mulVal
    exact fold_strip_congr n
      (fun a => rowSplat n k hn hk (mulVal n k hn hk x y) a (coeff z a))
      (fun a => shiftAdd n k hn hk a (scaleList n (coeff z a) (mulVal n k hn hk x y))) n
      (fun a _ha => row_as_shift n k hn hk _ (coeff z a) a hxyL (coeff_le hz a))
  rw [hleft]
  unfold triAll triRows
  exact fold_strip_congr n
    (fun a => shiftAdd n k hn hk a (scaleList n (coeff z a) (mulVal n k hn hk x y)))
    (fun a => (List.range n).foldl (fun acc i =>
        stripAdd acc (scaledPart n k hn hk x i (coeff y i) (coeff z a) a n))
      (List.replicate n 0)) n
    (fun a _ha => by
      dsimp only
      rw [← prod_full, shift_scale_prod n k hn hk x y hx hy a (coeff z a) n (coeff_le hz a)
        (Nat.le_refl _)])

private theorem rowPart_add (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (i c d m : Nat) (hc : c ≤ 2) (hd : d ≤ 2) :
    rowPart n k hn hk x i (tritAdd c d) m =
      stripAdd (rowPart n k hn hk x i c m) (rowPart n k hn hk x i d m) := by
  induction m with
  | zero =>
    simp [rowPart]
    exact (stripAdd_replicate n).symm
  | succ m ih =>
    rw [rowPart_succ, rowPart_succ, rowPart_succ, ih]
    have hdist := tritMul_add_left c d (coeff x m) hc hd (coeff_le hx m)
    rw [hdist]
    have hc1 : tritMul c (coeff x m) ≤ 2 := tritMul_le c _ hc (coeff_le hx m)
    have hd1 : tritMul d (coeff x m) ≤ 2 := tritMul_le d _ hd (coeff_le hx m)
    rw [splat_add n k hn hk _ _ (i + m) hc1 hd1]
    exact stripAdd_diamond _ _ _ _
      (by rw [rowPart_len, rowPart_len])
      (by rw [splat_len, rowPart_len])
      (by rw [splat_len, rowPart_len])

private theorem row_sum (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (i c d : Nat) (hc : c ≤ 2) (hd : d ≤ 2) :
    rowSplat n k hn hk x i (tritAdd c d) =
      stripAdd (rowSplat n k hn hk x i c) (rowSplat n k hn hk x i d) := by
  rw [← row_full, ← row_full, ← row_full]
  exact rowPart_add n k hn hk x hx i c d n hc hd

private def mulPart (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) : List Nat :=
  (List.range m).foldl (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
    (List.replicate n 0)

private theorem mulPart_full (n k : Nat) (hn : 0 < n) (hk : k < n) (x y : List Nat) :
    mulPart n k hn hk x y n = mulVal n k hn hk x y := by
  unfold mulPart mulVal
  rfl

private theorem mulPart_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) : (mulPart n k hn hk x y m).length = n := by
  unfold mulPart
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

private theorem mulPart_succ (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (m : Nat) :
    mulPart n k hn hk x y (m + 1) =
      stripAdd (mulPart n k hn hk x y m) (rowSplat n k hn hk x m (coeff y m)) := by
  unfold mulPart
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem mulPart_add (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x p q : List Nat) (hx : allTritList x) (hpL : p.length = n) (hqL : q.length = n)
    (hpT : allTritList p) (hqT : allTritList q) (m : Nat) (hm : m ≤ n) :
    mulPart n k hn hk x (stripAdd p q) m =
      stripAdd (mulPart n k hn hk x p m) (mulPart n k hn hk x q m) := by
  induction m with
  | zero =>
    simp [mulPart]
    exact (stripAdd_replicate n).symm
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hlt : m < p.length := by rw [hpL]; omega
    rw [mulPart_succ, mulPart_succ, mulPart_succ, ih hm',
      stripAdd_coeff p q m hlt,
      row_sum n k hn hk x hx m (coeff p m) (coeff q m) (coeff_le hpT m) (coeff_le hqT m)]
    exact stripAdd_diamond _ _ _ _
      (by rw [mulPart_len, mulPart_len])
      (by rw [rowSplat_len, mulPart_len])
      (by rw [rowSplat_len, mulPart_len])

private theorem mulVal_add (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x p q : List Nat) (hx : allTritList x) (hpL : p.length = n) (hqL : q.length = n)
    (hpT : allTritList p) (hqT : allTritList q) :
    mulVal n k hn hk x (stripAdd p q) =
      stripAdd (mulVal n k hn hk x p) (mulVal n k hn hk x q) := by
  rw [← mulPart_full, ← mulPart_full, ← mulPart_full]
  exact mulPart_add n k hn hk x p q hx hpL hqL hpT hqT n (Nat.le_refl _)

private theorem mulVal_zero (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) :
    mulVal n k hn hk x (List.replicate n 0) = List.replicate n 0 := by
  unfold mulVal
  suffices ∀ m, m ≤ n →
      (List.range m).foldl (fun acc i =>
          stripAdd acc (rowSplat n k hn hk x i (coeff (List.replicate n 0) i)))
        (List.replicate n 0) = List.replicate n 0 by
    exact this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (by omega), coeff_replicate_zero, rowSplat_zero, stripAdd_replicate]

private theorem mulPart_hot (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (e d m : Nat) (he : e < n) (hd : d ≤ 2) (hm : m ≤ n) :
    mulPart n k hn hk x ((List.replicate n 0).set e d) m =
      if m ≤ e then List.replicate n 0 else rowSplat n k hn hk x e d := by
  unfold mulPart
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    by_cases hlt : m < e
    · have hle : m + 1 ≤ e := by omega
      rw [if_pos (Nat.le_of_lt hlt), if_pos hle,
        coeff_set_ne (List.replicate n 0) e d m
          (by simpa [List.length_replicate] using (by omega : m < n)) (by omega),
        coeff_replicate_zero, rowSplat_zero, stripAdd_replicate]
    · by_cases heq : m = e
      · have hgt : ¬ m + 1 ≤ e := by omega
        rw [if_pos (by omega : m ≤ e), if_neg hgt, heq,
          coeff_set_eq (List.replicate n 0) e d (by simpa [List.length_replicate] using he)]
        have hz := stripAdd_left_zero (rowSplat n k hn hk x e d)
          (rowSplat_trits n k hn hk x hx e d hd)
        simp only [rowSplat_len] at hz
        exact hz
      · have hgt : ¬ m ≤ e := by omega
        have hgt1 : ¬ m + 1 ≤ e := by omega
        rw [if_neg hgt, if_neg hgt1,
          coeff_set_ne (List.replicate n 0) e d m
            (by simpa [List.length_replicate] using (by omega : m < n)) (by omega),
          coeff_replicate_zero, rowSplat_zero,
          stripAdd_right_zero _ (rowSplat_trits n k hn hk x hx e d hd) (by rw [rowSplat_len])]

private theorem rowPart_high (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (e d m : Nat) (hd : d ≤ 2) (he : ¬ e < n) (hm : m ≤ n) :
    rowPart n k hn hk x e d m =
      stripAdd (rowPart n k hn hk x (e - n) d m) (rowPart n k hn hk x (e - n + k) d m) := by
  induction m with
  | zero =>
    simp [rowPart]
    exact (stripAdd_replicate n).symm
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [rowPart_succ, rowPart_succ, rowPart_succ, ih hm']
    have hdj : tritMul d (coeff x m) ≤ 2 := tritMul_le d _ hd (coeff_le hx m)
    have hge : ¬ e + m < n := by omega
    rw [splat_ge n k hn hk (tritMul d (coeff x m)) (e + m) hge]
    have h1 : e + m - n = e - n + m := by omega
    have h2 : e - n + m + k = e - n + k + m := by omega
    rw [h1, h2]
    exact stripAdd_diamond _ _ _ _
      (by rw [rowPart_len, rowPart_len])
      (by rw [splat_len, rowPart_len])
      (by rw [splat_len, rowPart_len])

private theorem row_high (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (e d : Nat) (hd : d ≤ 2) (he : ¬ e < n) :
    rowSplat n k hn hk x e d =
      stripAdd (rowSplat n k hn hk x (e - n) d) (rowSplat n k hn hk x (e - n + k) d) := by
  rw [← row_full, ← row_full, ← row_full]
  exact rowPart_high n k hn hk x hx e d n hd he (Nat.le_refl _)

private theorem mulVal_splat (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (d e : Nat) (hd : d ≤ 2) :
    mulVal n k hn hk x (splat n k hn hk d e) = rowSplat n k hn hk x e d := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · rw [splat_lt n k hn hk d e he, ← mulPart_full]
      have h := mulPart_hot n k hn hk x hx e d n he hd (Nat.le_refl _)
      rw [h, if_neg (by omega : ¬ n ≤ e)]
    · rw [splat_ge n k hn hk d e he,
        mulVal_add n k hn hk x (splat n k hn hk d (e - n)) (splat n k hn hk d (e - n + k)) hx
          (by rw [splat_len]) (by rw [splat_len])
          (splat_trits n k hn hk d (e - n) hd) (splat_trits n k hn hk d (e - n + k) hd),
        ih (e - n) (by omega), ih (e - n + k) (by omega)]
      exact (row_high n k hn hk x hx e d hd he).symm

private theorem mul_over_prod (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (_hy : allTritList y) (_hz : allTritList z)
    (m : Nat) (hm : m ≤ n) :
    mulVal n k hn hk x (prodPart n k hn hk y z m) =
      (List.range m).foldl (fun acc a =>
          stripAdd acc (mulVal n k hn hk x (rowPart n k hn hk y a (coeff z a) n)))
        (List.replicate n 0) := by
  induction m with
  | zero =>
    rw [show prodPart n k hn hk y z 0 = List.replicate n 0 by simp [prodPart], mulVal_zero]
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [prodPart_succ,
      mulVal_add n k hn hk x (prodPart n k hn hk y z m)
        (rowPart n k hn hk y m (coeff z m) n) hx
        (by rw [prodPart_len]) (by rw [rowPart_len])
        (prodPart_trits n k hn hk y z m)
        (rowPart_trits n k hn hk y m (coeff z m) n),
      ih hm']

private theorem mul_over_row (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y : List Nat) (hx : allTritList x) (hy : allTritList y)
    (shift c m : Nat) (hc : c ≤ 2) (hm : m ≤ n) :
    mulVal n k hn hk x (rowPart n k hn hk y shift c m) =
      (List.range m).foldl (fun acc i =>
          stripAdd acc (mulVal n k hn hk x
            (splat n k hn hk (tritMul c (coeff y i)) (shift + i))))
        (List.replicate n 0) := by
  induction m with
  | zero =>
    rw [show rowPart n k hn hk y shift c 0 = List.replicate n 0 by simp [rowPart], mulVal_zero]
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hcm : tritMul c (coeff y m) ≤ 2 := tritMul_le c _ hc (coeff_le hy m)
    conv =>
      rhs
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [rowPart_succ,
      mulVal_add n k hn hk x (rowPart n k hn hk y shift c m)
        (splat n k hn hk (tritMul c (coeff y m)) (shift + m)) hx
        (by rw [rowPart_len]) (by rw [splat_len])
        (rowPart_trits n k hn hk y shift c m)
        (splat_trits n k hn hk _ _ hcm),
      ih hm']

/-- `(z_a · y_i) · x`, shifted by `a + i`, is the scaled row at exponent `i + j + a`. -/
private theorem assoc_part (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (hy : allTritList y) (hz : allTritList z)
    (a i m : Nat) (hm : m ≤ n) :
    rowPart n k hn hk x (a + i) (tritMul (coeff z a) (coeff y i)) m =
      scaledPart n k hn hk x i (coeff y i) (coeff z a) a m := by
  induction m with
  | zero =>
    simp [rowPart, scaledPart]
  | succ m ih =>
    rw [rowPart_succ, scaledPart_succ, ih (by omega)]
    have hmul := tritMul_assoc (coeff z a) (coeff y i) (coeff x m)
      (coeff_le hz a) (coeff_le hy i) (coeff_le hx m)
    have hexp : (a + i) + m = i + m + a := by omega
    rw [hmul, hexp]

private theorem right_row (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (hy : allTritList y) (hz : allTritList z)
    (a : Nat) :
    mulVal n k hn hk x (rowPart n k hn hk y a (coeff z a) n) = triRows n k hn hk x y z a := by
  rw [mul_over_row n k hn hk x y hx hy a (coeff z a) n (coeff_le hz a) (Nat.le_refl _)]
  unfold triRows
  exact fold_strip_congr n
    (fun i => mulVal n k hn hk x (splat n k hn hk (tritMul (coeff z a) (coeff y i)) (a + i)))
    (fun i => scaledPart n k hn hk x i (coeff y i) (coeff z a) a n) n
    (fun i _hi => by
      dsimp only
      rw [mulVal_splat n k hn hk x hx (tritMul (coeff z a) (coeff y i)) (a + i)
          (tritMul_le _ _ (coeff_le hz a) (coeff_le hy i)),
        ← row_full,
        assoc_part n k hn hk x y z hx hy hz a i n (Nat.le_refl _)])

private theorem mul_right_tri (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) :
    mulVal n k hn hk x (mulVal n k hn hk y z) = triAll n k hn hk x y z := by
  have hinner : mulVal n k hn hk y z = prodPart n k hn hk y z n :=
    (prod_full n k hn hk y z).symm
  rw [hinner, mul_over_prod n k hn hk x y z hx hy hz n (Nat.le_refl _)]
  unfold triAll
  exact fold_strip_congr n
    (fun a => mulVal n k hn hk x (rowPart n k hn hk y a (coeff z a) n))
    (fun a => triRows n k hn hk x y z a) n
    (fun a _ha => right_row n k hn hk x y z hx hy hz a)

/-- `(x · y) · z = x · (y · z)` on the reduced product. -/
theorem mulVal_assoc (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x y z : List Nat) (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) :
    mulVal n k hn hk (mulVal n k hn hk x y) z =
      mulVal n k hn hk x (mulVal n k hn hk y z) := by
  rw [mul_left_tri n k hn hk x y z hx hy hz, mul_right_tri n k hn hk x y z hx hy hz]

/-- SPEC.md §3 R4. Multiplication of trit lists associates. -/
theorem fieldMul_assoc (n k bench : Nat) (x y z : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (hx : allTritList x) (hy : allTritList y) (hz : allTritList z) :
    fieldMul n k bench (fieldMul n k bench x y) z =
      fieldMul n k bench x (fieldMul n k bench y z) := by
  have hxy := fieldMul_eq_mulVal n k bench x y hn hk hb hspan hx hy
  have hyz := fieldMul_eq_mulVal n k bench y z hn hk hb hspan hy hz
  have hxyT : allTritList (fieldMul n k bench x y) := by
    rw [hxy]; exact mulVal_trits n k hn hk x y hx hy
  have hyzT : allTritList (fieldMul n k bench y z) := by
    rw [hyz]; exact mulVal_trits n k hn hk y z hy hz
  rw [fieldMul_eq_mulVal n k bench (fieldMul n k bench x y) z hn hk hb hspan hxyT hz,
    fieldMul_eq_mulVal n k bench x (fieldMul n k bench y z) hn hk hb hspan hx hyzT,
    hxy, hyz, mulVal_assoc n k hn hk x y z hx hy hz]

end EcbsLink2.Link2
