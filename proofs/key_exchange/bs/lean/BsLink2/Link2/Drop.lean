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
    past the last hole). The strip stays a trit strip of the same size. -/
theorem drop_spec (strip : Array Int) (hole : Nat) (c : Int) (hc : 1 ≤ c ∧ c ≤ 2)
    (htr : Trits strip) (hh : hole < strip.size) (hfit : FitsLen strip.size)
    (hov : val strip + c * pw hole < pw strip.size) :
    ∃ s', Bs.drop strip (Int.ofNat hole) c = .ok s' ∧ s'.size = strip.size ∧ Trits s' ∧
      val s' = val strip + c * pw hole := by
  unfold Bs.drop
  rw [listLen_eq, subI_ofNat_one _ (by omega) hfit]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_exists (fun i (st : Array Int × Int) => st.1.size = strip.size ∧ Trits st.1 ∧
      0 ≤ st.2 ∧ st.2 ≤ 2 ∧ val st.1 + st.2 * pw i = val strip + c * pw hole)
    (by omega) ⟨rfl, htr, by omega, by omega, rfl⟩ ?_ ?_
  · intro i st h1 h2 hI
    obtain ⟨st, k⟩ := st
    obtain ⟨hsz, htr', hk0, hk2, hv⟩ := hI
    dsimp only at hsz htr' hk0 hk2 hv ⊢
    have hi : i < st.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.succ_le (by omega) hfit
    rw [if_neg (ofNat_not_gt h2)]
    have hd := trits_get htr' i hi
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · refine ⟨(st, 0), ⟨hsz, htr', Int.le_refl _, (by decide : (0:Int) ≤ 2),
        by simpa using hv⟩, ?_⟩
      simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, if_false,
        pure_eq_ok, ok_bind]
      exact asc_tail _ i hfi _
    · rcases (by omega : st[i] = 0 ∨ st[i] = 1 ∨ st[i] = 2) with hd | hd | hd
      · refine ⟨(st.set ⟨i, hi⟩ 1, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          Int.le_refl _, (by decide : (0:Int) ≤ 2), by rw [val_set, hd]; omega⟩, ?_⟩
        simp only [show decide ((1 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_0]
        exact asc_tail_cast _ _ hfi _
      · refine ⟨(st.set ⟨i, hi⟩ 2, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          Int.le_refl _, (by decide : (0:Int) ≤ 2), by rw [val_set, hd]; omega⟩, ?_⟩
        simp only [show decide ((1 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_1]
        exact asc_tail_cast _ _ hfi _
      · refine ⟨(st.set ⟨i, hi⟩ 0, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (0:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        simp only [show decide ((1 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 1 then 1 else ((1 : Int) - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_2]
        exact asc_tail_cast _ _ hfi _
    · rcases (by omega : st[i] = 0 ∨ st[i] = 1 ∨ st[i] = 2) with hd | hd | hd
      · refine ⟨(st.set ⟨i, hi⟩ 2, 0), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          Int.le_refl _, (by decide : (0:Int) ≤ 2), by rw [val_set, hd]; omega⟩, ?_⟩
        simp only [show decide ((2 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_0, addI_1_1, runLoopOn_succ, set_set, sEq_int, hi, atL_cast, putL_cast]
        exact asc_tail_cast _ _ hfi _
      · refine ⟨(st.set ⟨i, hi⟩ 0, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (0:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        simp only [show decide ((2 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_1, addI_1_1, runLoopOn_succ, set_set, sEq_int, hi, atL_cast, putL_cast]
        exact asc_tail_cast _ _ hfi _
      · refine ⟨(st.set ⟨i, hi⟩ 1, 1), ⟨by simp [hsz], trits_set htr' i hi (by decide),
          (by decide : (0:Int) ≤ 1), (by decide : (1:Int) ≤ 2),
          by rw [val_set, hd, pw_succ]; omega⟩, ?_⟩
        simp only [show decide ((2 : Int) > 0) = true from rfl, if_true, pure_eq_ok, ok_bind]
        rw [show (if (1 : Int) > 2 then 1 else ((2 : Int) - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [atL_cast st i hi, hd, putL_cast st i _ hi, click_2, addI_1_1, runLoopOn_succ, set_set, sEq_int, hi, atL_cast, putL_cast]
        exact asc_tail_cast _ _ hfi _
  · intro st hI
    obtain ⟨st, k⟩ := st
    obtain ⟨hsz, htr', hk0, hk2, hv⟩ := hI
    dsimp only at hsz htr' hk0 hk2 hv ⊢
    have hL : strip.size - 1 + 1 = strip.size := by omega
    rw [hL] at hv
    have hnn := val_nonneg htr'
    have hpp := pw_pos strip.size
    have hk : k = 0 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · rfl
      · omega
      · omega
    subst hk
    refine ⟨st, ?_, hsz, htr', by omega⟩
    rfl

end BsLink2.Link2
