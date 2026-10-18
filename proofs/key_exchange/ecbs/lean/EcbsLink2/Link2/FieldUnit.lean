/-
  The one-peg is a unit for `fieldMul`. The product keeps only the unshifted
  row, and that row is the list. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldMulAssoc
import EcbsLink2.Link2.OneField
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem whiteHole0_eq_onePeg (n : Nat) : whiteHole0 n = onePeg n := rfl

/-- A row of the one-peg is the single peg `c` at hole `i`. -/
private theorem one_row (n k : Nat) (hn : 0 < n) (hk : k < n)
    (i c m : Nat) (hc : c ≤ 2) (hm : m ≤ n) :
    (List.range m).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (tritMul c (coeff (onePeg n) j)) (i + j)))
      (List.replicate n 0) =
      if m = 0 then List.replicate n 0 else splat n k hn hk c i := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    by_cases hm0 : m = 0
    · have h1 : ¬ m + 1 = 0 := by omega
      rw [if_pos hm0, if_neg h1, hm0, coeff_one_zero n hn, tritMul_one_right c hc,
        Nat.add_zero]
      have hz := stripAdd_left_zero (splat n k hn hk c i) (splat_trits n k hn hk c i hc)
      simp only [splat_len] at hz
      exact hz
    · have hpos : 0 < m := by omega
      have h1 : ¬ m + 1 = 0 := by omega
      rw [if_neg hm0, if_neg h1, coeff_one_pos n m hn hpos, tritMul_zero_right c hc,
        splat_zero,
        stripAdd_right_zero _ (splat_trits n k hn hk c i hc) (by rw [splat_len])]

private theorem row_one (n k : Nat) (hn : 0 < n) (hk : k < n)
    (i c : Nat) (hc : c ≤ 2) :
    rowSplat n k hn hk (onePeg n) i c = splat n k hn hk c i := by
  unfold rowSplat
  rw [one_row n k hn hk i c n hc (Nat.le_refl _), if_neg (by omega : ¬ n = 0)]

private theorem mul_one_left_fold (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (m : Nat) (hm : m ≤ n) :
    (List.range m).foldl (fun acc i =>
        stripAdd acc (rowSplat n k hn hk (onePeg n) i (coeff x i)))
      (List.replicate n 0) =
      polyFold n k hn hk x m := by
  induction m with
  | zero =>
    simp [polyFold]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih hm', polyFold_succ, row_one n k hn hk m (coeff x m) (coeff_le hx m)]

/-- `1 · x = x` on the reduced product. -/
theorem mulVal_one_left (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (hlen : x.length = n) :
    mulVal n k hn hk (onePeg n) x = x := by
  unfold mulVal
  rw [mul_one_left_fold n k hn hk x hx n (Nat.le_refl _)]
  rw [show polyFold n k hn hk x n = polyVal n k hn hk x by
    unfold polyVal; exact congrArg (polyFold n k hn hk x) hlen.symm]
  exact polyVal_self n k hn hk x hx hlen

/-- The unshifted row of `x`, scaled by one, is the reduced list. -/
private theorem row_unshifted (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (m : Nat) (hm : m ≤ n) :
    (List.range m).foldl (fun acc j =>
        stripAdd acc (splat n k hn hk (tritMul 1 (coeff x j)) (0 + j)))
      (List.replicate n 0) =
      polyFold n k hn hk x m := by
  induction m with
  | zero =>
    simp [polyFold]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [polyFold_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih hm', tritMul_one_left (coeff x m) (coeff_le hx m), Nat.zero_add]

private theorem unshifted_is_poly (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) :
    rowSplat n k hn hk x 0 1 = polyFold n k hn hk x n := by
  unfold rowSplat
  exact row_unshifted n k hn hk x hx n (Nat.le_refl _)

private theorem mul_one_right_fold (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (m : Nat) (hm : m ≤ n) :
    (List.range m).foldl (fun acc i =>
        stripAdd acc (rowSplat n k hn hk x i (coeff (onePeg n) i)))
      (List.replicate n 0) =
      if m = 0 then List.replicate n 0 else rowSplat n k hn hk x 0 1 := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm' : m ≤ n := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih hm']
    by_cases hm0 : m = 0
    · have h1 : ¬ m + 1 = 0 := by omega
      rw [if_pos hm0, if_neg h1, hm0, coeff_one_zero n hn]
      have hz := stripAdd_left_zero (rowSplat n k hn hk x 0 1)
        (rowSplat_trits n k hn hk x hx 0 1 (by omega))
      simp only [rowSplat_len] at hz
      exact hz
    · have hpos : 0 < m := by omega
      have h1 : ¬ m + 1 = 0 := by omega
      rw [if_neg hm0, if_neg h1, coeff_one_pos n m hn hpos, rowSplat_zero,
        stripAdd_right_zero _ (rowSplat_trits n k hn hk x hx 0 1 (by omega))
          (by rw [rowSplat_len])]

/-- `x · 1 = x` on the reduced product. -/
theorem mulVal_one_right (n k : Nat) (hn : 0 < n) (hk : k < n)
    (x : List Nat) (hx : allTritList x) (hlen : x.length = n) :
    mulVal n k hn hk x (onePeg n) = x := by
  unfold mulVal
  rw [mul_one_right_fold n k hn hk x hx n (Nat.le_refl _), if_neg (by omega : ¬ n = 0),
    unshifted_is_poly n k hn hk x hx]
  rw [show polyFold n k hn hk x n = polyVal n k hn hk x by
    unfold polyVal; exact congrArg (polyFold n k hn hk x) hlen.symm]
  exact polyVal_self n k hn hk x hx hlen

/-- SPEC.md §3 R4. The one-peg is a right unit. -/
theorem fieldMul_one_right (n k bench : Nat) (x : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (hx : allTritList x) (hlen : x.length = n) :
    fieldMul n k bench x (onePeg n) = x := by
  rw [fieldMul_eq_mulVal n k bench x (onePeg n) hn hk hb hspan hx (onePeg_trits n),
    mulVal_one_right n k hn hk x hx hlen]

/-- SPEC.md §3 R4. The one-peg is a left unit. -/
theorem fieldMul_one_left (n k bench : Nat) (x : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench) (hspan : 2 * (n - 1) < bench)
    (hx : allTritList x) (hlen : x.length = n) :
    fieldMul n k bench (onePeg n) x = x := by
  rw [fieldMul_eq_mulVal n k bench (onePeg n) x hn hk hb hspan (onePeg_trits n) hx,
    mulVal_one_left n k hn hk x hx hlen]

end EcbsLink2.Link2
