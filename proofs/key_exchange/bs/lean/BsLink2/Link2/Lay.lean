/-
  BS Link 2: B2 `lay` (lay a copy of a register starting at a hole) adds
  `val a · 3^s` to the strip's value, when that does not overflow the strip. Proof-only.
-/
import BsLink2.Link2.Drop

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- B2. Laying a non-empty trit register `a` from hole `sN` (with room for all of it)
    adds `val a · 3^sN` to the strip's value, as long as the sum stays below `3^size`. -/
theorem lay_spec (strip a : Array Int) (sN : Nat) (htr : Trits strip) (hta : Trits a)
    (ha : 0 < a.size) (hroom : sN + a.size ≤ strip.size) (hfit : FitsLen strip.size)
    (hov : val strip + val a * pw sN < pw strip.size) :
    ∃ s', Bs.lay strip a (Int.ofNat sN) = .ok s' ∧ s'.size = strip.size ∧ Trits s' ∧
      val s' = val strip + val a * pw sN := by
  unfold Bs.lay
  rw [listLen_eq, subI_ofNat_one _ ha (FitsLen.of_le hfit (by omega))]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_exists (fun j (st : Array Int) => st.size = strip.size ∧ Trits st ∧
      val st = val strip + valL (a.toList.take j) * pw sN)
    (Nat.zero_le _) ⟨rfl, htr, by simp [valL]⟩ ?_ ?_
  · intro j st _ h2 hI
    obtain ⟨hsz, htr', hv⟩ := hI
    have hj : j < a.size := by omega
    have hfi : FitsLen (j + 1) := FitsLen.succ_le (by omega) hfit
    rw [if_neg (ofNat_not_gt h2)]
    dsimp only
    have hjl : j < a.toList.length := by simpa using hj
    have hget : a.toList[j] = a[j] := by simp
    have htake := valL_take_succ a.toList j hjl
    rw [hget] at htake
    have hd := trits_get hta j hj
    rw [atL_ofNat a j hj]
    simp only [ok_bind]
    by_cases h0 : a[j] = 0
    · refine ⟨st, ⟨hsz, htr', ?_⟩, ?_⟩
      · rw [htake, h0]; simp [hv]
      · simp only [h0, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
          pure_eq_ok, ok_bind]
        exact asc_tail _ j hfi _
    · have hc : 1 ≤ a[j] ∧ a[j] ≤ 2 := by omega
      have hsj : sN + j < st.size := by omega
      have hle := valL_take_le hta (j + 1)
      have hpw := pw_pos sN
      have hmul : valL (a.toList.take (j + 1)) * pw sN ≤ valL a.toList * pw sN :=
        Int.mul_le_mul_of_nonneg_right hle (Int.le_of_lt hpw)
      have hexp : a[j] * pw (sN + j) = a[j] * pw j * pw sN := by
        rw [pw_add, Int.mul_assoc, Int.mul_comm (pw sN)]
      have hsplit : valL (a.toList.take (j + 1)) * pw sN =
          valL (a.toList.take j) * pw sN + a[j] * pw j * pw sN := by
        rw [htake, Int.add_mul]
      have hov' : val st + a[j] * pw (sN + j) < pw st.size := by
        rw [hexp, hsz, hv]; unfold val at hov ⊢; omega
      obtain ⟨s', hdrop, hsz', htr'', hv'⟩ :=
        drop_spec st (sN + j) a[j] hc htr' hsj (by rw [hsz]; exact hfit) hov'
      refine ⟨s', ⟨by omega, htr'', ?_⟩, ?_⟩
      · rw [hv', hexp, hv, hsplit]; omega
      · have hne : (!SudoRt.SEq.beq a[j] 0) = true := by simp [sEq_int, h0]
        rw [if_pos hne, addI_ofNat _ _ (FitsLen.of_le hfit (by omega)), ok_bind, hdrop]
        simp only [pure_eq_ok, ok_bind]
        exact asc_tail _ j hfi _
  · intro st hI
    obtain ⟨hsz, htr', hv⟩ := hI
    refine ⟨st, rfl, hsz, htr', ?_⟩
    rw [hv, show a.size - 1 + 1 = a.toList.length by simp; omega, valL_take_length]
    rfl

end BsLink2.Link2
