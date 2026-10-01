/-
  BS Link 2: B1 `drop` (one peg dropped with its odometer carry) adds `colour · 3^hole`
  to the strip's value, when that does not overflow the strip. Proof-only.
-/
import BsLink2.Link2.Basic

namespace BsLink2.Link2

open MegaDreifach.Link2

set_option maxHeartbeats 1000000 in
/-- B1. Dropping a white (1) or red (2) peg into hole `hole` of a trit strip adds
    `colour · 3^hole` to its value, as long as the sum stays below `3^size` (no carry
    past the last hole). The strip stays a trit strip of the same size. The emitted carry
    loop breaks at the first hole that does not carry, and its final `assert clicks == 0`
    holds. -/
theorem drop_spec (strip : Array Int) (hole : Nat) (c : Int) (hc : 1 ≤ c ∧ c ≤ 2)
    (htr : Trits strip) (hh : hole < strip.size) (hfit : FitsLen strip.size)
    (hov : val strip + c * pw hole < pw strip.size) :
    ∃ s', Bs.drop strip (Int.ofNat hole) c = .ok s' ∧ s'.size = strip.size ∧ Trits s' ∧
      val s' = val strip + c * pw hole := by
  unfold Bs.drop
  rw [listLen_eq, subI_ofNat_one _ (by omega) hfit]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  -- `Inv i`: still carrying `k ∈ {1, 2}` into hole `i`; `Done`: the carry stopped.
  refine asc_brk_exists (fun i (st : Array Int × Int) => st.1.size = strip.size ∧
      Trits st.1 ∧ 1 ≤ st.2 ∧ st.2 ≤ 2 ∧ val st.1 + st.2 * pw i = val strip + c * pw hole)
    (fun (st : Array Int × Int) => st.1.size = strip.size ∧ Trits st.1 ∧ st.2 = 0 ∧
      val st.1 = val strip + c * pw hole)
    (by omega) ⟨rfl, htr, hc.1, hc.2, rfl⟩ ?_ ?_
  · intro i st h1 h2 hI
    obtain ⟨st, k⟩ := st
    obtain ⟨hsz, htr', hk1, hk2, hv⟩ := hI
    dsimp only at hsz htr' hk1 hk2 hv ⊢
    have hi : i < st.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.succ_le (by omega) hfit
    rw [if_neg (ofNat_not_gt h2)]
    have hd := trits_get htr' i hi
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · rcases (by omega : st[i] = 0 ∨ st[i] = 1 ∨ st[i] = 2) with hd | hd | hd
      · refine Or.inr ⟨(st.set ⟨i, hi⟩ 1, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          rfl, by rw [val_set, hd]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_0]
        rfl
      · refine Or.inr ⟨(st.set ⟨i, hi⟩ 2, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          rfl, by rw [val_set, hd]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_1]
        rfl
      · refine Or.inl ⟨(st.set ⟨i, hi⟩ 0, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (1:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_2]
        exact asc_tail_cast _ _ hfi _
    · rcases (by omega : st[i] = 0 ∨ st[i] = 1 ∨ st[i] = 2) with hd | hd | hd
      · refine Or.inr ⟨(st.set ⟨i, hi⟩ 2, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          rfl, by rw [val_set, hd]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_0, addI_1_1, runLoopOn_succ,
          set_set, sEq_int, hi, atL_cast, putL_cast]
        rfl
      · refine Or.inl ⟨(st.set ⟨i, hi⟩ 0, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (1:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_1, addI_1_1, runLoopOn_succ,
          set_set, sEq_int, hi, atL_cast, putL_cast]
        exact asc_tail_cast _ _ hfi _
      · refine Or.inl ⟨(st.set ⟨i, hi⟩ 1, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (1:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_2, addI_1_1, runLoopOn_succ,
          set_set, sEq_int, hi, atL_cast, putL_cast]
        exact asc_tail_cast _ _ hfi _
  · intro j st hI
    obtain ⟨st, k⟩ := st
    rcases hI with ⟨hsz, htr', hk1, hk2, hv⟩ | ⟨hsz, htr', hk, hv⟩
    · -- Still carrying past the last hole: impossible, the sum would overflow the strip.
      dsimp only at hsz htr' hk1 hk2 hv
      have hL : strip.size - 1 + 1 = strip.size := by omega
      rw [hL] at hv
      have hnn := val_nonneg htr'
      have hpp := pw_pos strip.size
      have : pw strip.size ≤ k * pw strip.size := by
        have := Int.mul_le_mul_of_nonneg_right hk1 (Int.le_of_lt hpp)
        simpa using this
      omega
    · dsimp only at hsz htr' hk hv
      subst hk
      refine ⟨st, ?_, hsz, htr', hv⟩
      rfl

end BsLink2.Link2
