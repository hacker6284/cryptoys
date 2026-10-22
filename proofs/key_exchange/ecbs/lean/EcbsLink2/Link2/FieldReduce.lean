/-
  One step of the lane fold adds a multiple of `X^n − X^k − 1`, so the
  remainder does not change. A strip that is already shorter than `n` is its
  own remainder. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldPoly

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem stripAdd_right_zero (xs : List Nat) (ht : allTritList xs) (hlen : xs.length = n) :
    stripAdd xs (List.replicate n 0) = xs := by
  have hrep : List.replicate n 0 = List.replicate xs.length 0 := by rw [hlen]
  rw [hrep]
  exact stripAdd_zero xs ht

private theorem three_cancel (n k : Nat) (hn : 0 < n) (hk : k < n) (c e : Nat)
    (hc : c ≤ 2) (he : ¬ e < n) :
    stripAdd (splat n k hn hk (flipTrit c) e)
        (stripAdd (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k))) =
      List.replicate n 0 := by
  rw [← splat_ge n k hn hk c e he, ← splat_add n k hn hk (flipTrit c) c e (flipTrit_le c) hc,
    tritAdd_comm, trit_add_flip c hc, splat_zero]

/-- `foldHigh` at a high hole replaces `c · X^e` by `c · X^{e-n} + c · X^{e-n+k}`. -/
theorem foldHigh_poly (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat) (e : Nat)
    (ht : allTritList xs) :
    polyVal n k hn hk (foldHigh n (n - k) e xs) = polyVal n k hn hk xs := by
  by_cases hskip : coeff xs e = 0 ∨ e < n
  · unfold foldHigh
    simp [hskip]
  · have hc0 : coeff xs e ≠ 0 := by
      intro hz
      exact hskip (Or.inl hz)
    have he : ¬ e < n := by
      intro hlt
      exact hskip (Or.inr hlt)
    have hel : e < xs.length := by
      by_cases hge : e < xs.length
      · exact hge
      · exact absurd (coeff_ge xs e (Nat.le_of_not_gt hge)) hc0
    have hc : coeff xs e ≤ 2 := coeff_le ht e
    let c := coeff xs e
    let gap := n - k
    have hgap : e - gap = e - n + k := by
      have hk' : k ≤ n := Nat.le_of_lt hk
      omega
    let b0 := xs.set e (tritAdd c (flipTrit c))
    have hb0 : b0 = xs.set e 0 := by
      unfold b0
      rw [trit_add_flip c hc]
    have ht0 : allTritList b0 := tritList_set xs ht e _ (tritAdd_le _ _)
    have hp0 := polyVal_set_add n k hn hk xs e (flipTrit c) hel ht (flipTrit_le c)
    have hp0' : polyVal n k hn hk (xs.set e 0) =
        stripAdd (polyVal n k hn hk xs) (splat n k hn hk (flipTrit c) e) := by
      have hset : xs.set e (tritAdd c (flipTrit c)) = xs.set e 0 := by
        rw [trit_add_flip c hc]
      rw [hset] at hp0
      exact hp0
    have h1len : e - n < (xs.set e 0).length := by
      simp [List.length_set]
      omega
    have ht1 : allTritList (xs.set e 0) := by
      rw [← hb0]
      exact ht0
    let b1 := (xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) c)
    have hp1 := polyVal_set_add n k hn hk (xs.set e 0) (e - n) c h1len ht1 hc
    have h2len : e - gap < b1.length := by
      simp [b1, List.length_set]
      omega
    have ht2 : allTritList b1 := tritList_set _ ht1 (e - n) _ (tritAdd_le _ _)
    have hp2 := polyVal_set_add n k hn hk b1 (e - gap) c h2len ht2 hc
    have hfold : foldHigh n gap e xs = b1.set (e - gap) (tritAdd (coeff b1 (e - gap)) c) := by
      unfold foldHigh
      simp [c, gap, hc0, he, hb0]
    rw [hfold, hp2, hp1, hp0', hgap]
    rw [stripAdd_assoc (stripAdd (polyVal n k hn hk xs) (splat n k hn hk (flipTrit c) e))
        (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k))
        (by rw [splat_len, stripAdd_length, polyVal_len])
        (by rw [splat_len, stripAdd_length, polyVal_len]),
      stripAdd_assoc (polyVal n k hn hk xs) (splat n k hn hk (flipTrit c) e)
        (stripAdd (splat n k hn hk c (e - n)) (splat n k hn hk c (e - n + k)))
        (by rw [splat_len, polyVal_len])
        (by rw [stripAdd_length, splat_len, polyVal_len]),
      three_cancel n k hn hk c e hc he,
      stripAdd_right_zero _ (polyVal_trits n k hn hk xs ht) (polyVal_len n k hn hk xs)]

private theorem polyFold_at (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) (hlen : xs.length = n) (m j : Nat) (hm : m ≤ n) (hj : j < n) :
    coeff (polyFold n k hn hk xs m) j = if j < m then xs[j] else 0 := by
  induction m with
  | zero =>
    simp [polyFold, coeff_replicate_zero]
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hmL : m < xs.length := by omega
    rw [polyFold_succ, stripAdd_coeff _ _ j (by rw [polyFold_len]; exact hj),
      splat_lt n k hn hk (coeff xs m) m (by omega)]
    by_cases hjm : j = m
    · have hmN : m < n := by omega
      have hset : coeff ((List.replicate n 0).set m (coeff xs m)) m = xs[m] := by
        rw [coeff_set_eq (List.replicate n 0) m (coeff xs m)
            (by simpa [List.length_replicate] using hmN),
          coeff_eq_get xs m hmL]
      have hcoe : coeff ((List.replicate n 0).set m (coeff xs m)) j = xs[m] := by
        cases hjm
        exact hset
      have hlow : coeff (polyFold n k hn hk xs m) j = 0 := by
        cases hjm
        have hif := ih hm'
        simp [Nat.lt_irrefl] at hif
        exact hif
      have hrhs : (if j < m + 1 then xs[j] else 0) = xs[m] := by
        cases hjm
        simp [Nat.lt_succ_self]
      rw [hcoe, hlow, tritAdd_zero_left _ (ht _ (List.getElem_mem hmL)), hrhs]
    · rw [coeff_set_ne (List.replicate n 0) m (coeff xs m) j
          (by simpa [List.length_replicate] using hj) (Ne.symm hjm),
        coeff_replicate_zero, tritAdd_zero_right _ (by
          by_cases hlt : j < m
          · rw [ih hm', if_pos hlt]
            exact ht _ (List.getElem_mem (by omega))
          · rw [ih hm', if_neg hlt]
            omega), ih hm']
      by_cases hlt : j < m
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hge : ¬ j < m + 1 := by omega
        simp [hlt, hge]


/-- A list of length `n` is already reduced. -/
theorem polyVal_self (n k : Nat) (hn : 0 < n) (hk : k < n) (xs : List Nat)
    (ht : allTritList xs) (hlen : xs.length = n) :
    polyVal n k hn hk xs = xs := by
  refine lists_coeff (by rw [polyVal_len, hlen]) ?_
  intro j
  by_cases hj : j < n
  · unfold polyVal
    rw [hlen]
    rw [polyFold_at n k hn hk xs ht hlen n j (Nat.le_refl _) hj, if_pos hj,
      coeff_eq_get xs j (by rw [hlen]; exact hj)]
  · rw [coeff_ge _ j (by rw [polyVal_len]; exact Nat.le_of_not_gt hj),
      coeff_ge xs j (by rw [hlen]; exact Nat.le_of_not_gt hj)]

end EcbsLink2.Link2
