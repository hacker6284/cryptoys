/-
  The reduced product is the schoolbook convolution, taken modulo
  `X^n − X^k − 1`. Convolution associates, and the one-peg is a unit.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldReduce

namespace EcbsLink2.Link2

open EcbsLink2.Spec

/-- One reduced row: `c` times `x`, shifted by `shift` holes. -/
def rowSplat (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat)
    (shift c : Nat) : List Nat :=
  (List.range n).foldl
    (fun acc j => stripAdd acc (splat n k hn hk (tritMul c (coeff x j)) (shift + j)))
    (List.replicate n 0)

/-- `fieldMul` as a sum of reduced rows. The second factor supplies the shift. -/
def mulVal (n k : Nat) (hn : 0 < n) (hk : k < n) (x y : List Nat) : List Nat :=
  (List.range n).foldl
    (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i)))
    (List.replicate n 0)

private theorem foldSplat_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (f : Nat → Nat) (m : Nat) (acc : List Nat) (hlen : acc.length = n) :
    ((List.range m).foldl (fun acc j => stripAdd acc (splat n k hn hk (f j) j)) acc).length = n := by
  induction m generalizing acc with
  | zero => rw [List.range_zero, List.foldl_nil]; exact hlen
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length]
    exact ih acc hlen

theorem rowSplat_len (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat)
    (shift c : Nat) : (rowSplat n k hn hk x shift c).length = n := by
  unfold rowSplat
  -- The exponent is `shift + j`, not `j`, so the generic fold is not the same
  -- function. Length does not read the exponent.
  suffices ∀ m acc, acc.length = n →
      ((List.range m).foldl
        (fun acc j => stripAdd acc (splat n k hn hk (tritMul c (coeff x j)) (shift + j)))
        acc).length = n by
    exact this n _ (by simp)
  intro m
  induction m with
  | zero =>
    intro acc hlen
    rw [List.range_zero, List.foldl_nil]; exact hlen
  | succ m ih =>
    intro acc hlen
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length]
    exact ih acc hlen

theorem mulVal_len (n k : Nat) (hn : 0 < n) (hk : k < n) (x y : List Nat) :
    (mulVal n k hn hk x y).length = n := by
  unfold mulVal
  suffices ∀ m acc, acc.length = n →
      ((List.range m).foldl
        (fun acc i => stripAdd acc (rowSplat n k hn hk x i (coeff y i))) acc).length = n by
    exact this n _ (by simp)
  intro m
  induction m with
  | zero =>
    intro acc hlen
    rw [List.range_zero, List.foldl_nil]; exact hlen
  | succ m ih =>
    intro acc hlen
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length]
    exact ih acc hlen

theorem rowSplat_zero (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat) (shift : Nat) :
    rowSplat n k hn hk x shift 0 = List.replicate n 0 := by
  unfold rowSplat
  suffices ∀ m, m ≤ n →
      (List.range m).foldl
        (fun acc j => stripAdd acc (splat n k hn hk (tritMul 0 (coeff x j)) (shift + j)))
        (List.replicate n 0) = List.replicate n 0 by
    exact this n (Nat.le_refl _)
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      tritMul_zero_left, splat_zero, stripAdd_replicate]

theorem rowSplat_trits (n k : Nat) (hn : 0 < n) (hk : k < n) (x : List Nat)
    (hx : allTritList x) (shift c : Nat) (hc : c ≤ 2) :
    allTritList (rowSplat n k hn hk x shift c) := by
  unfold rowSplat
  suffices ∀ m, m ≤ n → allTritList ((List.range m).foldl
      (fun acc j => stripAdd acc (splat n k hn hk (tritMul c (coeff x j)) (shift + j)))
      (List.replicate n 0)) by
    exact this n (Nat.le_refl _)
  intro m hm
  induction m with
  | zero =>
    simp
    exact replicate_trits n
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact stripAdd_trits _ _

/-- Shift a reduced length-`n` list by `s` more holes. -/
def shiftAdd (n k : Nat) (hn : 0 < n) (hk : k < n) (s : Nat) (p : List Nat) : List Nat :=
  (List.range n).foldl
    (fun acc t => stripAdd acc (splat n k hn hk (coeff p t) (t + s)))
    (List.replicate n 0)

theorem shiftAdd_len (n k : Nat) (hn : 0 < n) (hk : k < n) (s : Nat) (p : List Nat) :
    (shiftAdd n k hn hk s p).length = n := by
  unfold shiftAdd
  suffices ∀ m acc, acc.length = n →
      ((List.range m).foldl
        (fun acc t => stripAdd acc (splat n k hn hk (coeff p t) (t + s))) acc).length = n by
    exact this n _ (by simp)
  intro m
  induction m with
  | zero =>
    intro acc hlen
    rw [List.range_zero, List.foldl_nil]; exact hlen
  | succ m ih =>
    intro acc hlen
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length]
    exact ih acc hlen

private theorem partialShift_len (n k : Nat) (hn : 0 < n) (hk : k < n)
    (s : Nat) (p : List Nat) (m : Nat) :
    ((List.range m).foldl
        (fun acc t => stripAdd acc (splat n k hn hk (coeff p t) (t + s)))
        (List.replicate n 0)).length = n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, stripAdd_length, ih]

/-- Shifting a sum is the sum of the shifts. -/
theorem shift_add (n k : Nat) (hn : 0 < n) (hk : k < n) (s : Nat)
    (a b : List Nat) (ha : a.length = n) (hb : b.length = n)
    (hta : allTritList a) (htb : allTritList b) :
    shiftAdd n k hn hk s (stripAdd a b) =
      stripAdd (shiftAdd n k hn hk s a) (shiftAdd n k hn hk s b) := by
  unfold shiftAdd
  suffices ∀ m, m ≤ n →
      (List.range m).foldl
          (fun acc t => stripAdd acc (splat n k hn hk (coeff (stripAdd a b) t) (t + s)))
          (List.replicate n 0) =
        stripAdd
          ((List.range m).foldl
            (fun acc t => stripAdd acc (splat n k hn hk (coeff a t) (t + s)))
            (List.replicate n 0))
          ((List.range m).foldl
            (fun acc t => stripAdd acc (splat n k hn hk (coeff b t) (t + s)))
            (List.replicate n 0)) from
    this n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _hm
    simp
    exact (stripAdd_replicate n).symm
  | succ m ih =>
    intro hm
    have hlt : m < n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih (by omega),
      stripAdd_coeff a b m (by rw [ha]; exact hlt),
      splat_add n k hn hk (coeff a m) (coeff b m) (m + s) (coeff_le hta m) (coeff_le htb m)]
    exact stripAdd_diamond _ _ _ _
      (by rw [partialShift_len, partialShift_len])
      (by rw [splat_len, partialShift_len])
      (by rw [splat_len, partialShift_len])

private theorem fold_monom (n k : Nat) (hn : 0 < n) (hk : k < n) (c e s m : Nat)
    (hc : c ≤ 2) (he : e < n) (hm : m ≤ n) :
    (List.range m).foldl
        (fun acc t =>
          stripAdd acc (splat n k hn hk (coeff ((List.replicate n 0).set e c) t) (t + s)))
        (List.replicate n 0) =
      if m ≤ e then List.replicate n 0 else splat n k hn hk c (e + s) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    by_cases hlt : m < e
    · have hle : m + 1 ≤ e := by omega
      rw [if_pos (Nat.le_of_lt hlt), if_pos hle,
        coeff_set_ne (List.replicate n 0) e c m (by simpa [List.length_replicate] using (by omega : m < n))
          (by omega),
        coeff_replicate_zero, splat_zero, stripAdd_replicate]
    · by_cases heq : m = e
      · have hgt : ¬ m + 1 ≤ e := by omega
        rw [if_pos (by omega : m ≤ e), if_neg hgt, heq,
          coeff_set_eq (List.replicate n 0) e c (by simpa [List.length_replicate] using he)]
        have hz := stripAdd_left_zero (splat n k hn hk c (e + s))
          (splat_trits n k hn hk c (e + s) hc)
        simp only [splat_len] at hz
        exact hz
      · have hgt : ¬ m ≤ e := by omega
        have hgt1 : ¬ m + 1 ≤ e := by omega
        rw [if_neg hgt, if_neg hgt1,
          coeff_set_ne (List.replicate n 0) e c m (by simpa [List.length_replicate] using (by omega : m < n))
            (by omega),
          coeff_replicate_zero, splat_zero,
          stripAdd_right_zero _ (splat_trits n k hn hk c (e + s) hc) (by rw [splat_len])]

/-- Shifting one reduced power moves the exponent. Below hole `n` the power is a single peg. -/
theorem shift_monom (n k : Nat) (hn : 0 < n) (hk : k < n) (c e s : Nat)
    (hc : c ≤ 2) (he : e < n) :
    shiftAdd n k hn hk s (splat n k hn hk c e) = splat n k hn hk c (e + s) := by
  rw [splat_lt n k hn hk c e he]
  unfold shiftAdd
  have h := fold_monom n k hn hk c e s n hc he (Nat.le_refl _)
  rw [h, if_neg (by omega : ¬ n ≤ e)]

/-- Shifting a power, high or low, moves the exponent and reduces again. -/
theorem shift_splat (n k : Nat) (hn : 0 < n) (hk : k < n) (c e s : Nat) (hc : c ≤ 2) :
    shiftAdd n k hn hk s (splat n k hn hk c e) = splat n k hn hk c (e + s) := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < n
    · exact shift_monom n k hn hk c e s hc he
    · rw [splat_ge n k hn hk c e he,
        shift_add n k hn hk s (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k))
          (by rw [splat_len]) (by rw [splat_len])
          (splat_trits n k hn hk c (e - n) hc) (splat_trits n k hn hk c (e - n + k) hc),
        ih (e - n) (by omega), ih (e - n + k) (by omega)]
      have h1 : e - n + s = e + s - n := by omega
      have h2 : e - n + k + s = e + s - n + k := by omega
      rw [h1, h2, ← splat_ge n k hn hk c (e + s) (by omega)]

end EcbsLink2.Link2
