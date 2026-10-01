/-
  BS Link 2: B3 `multiply`. For a well-formed field and two registers of `n` trits, the
  emitted multiplication succeeds and returns a register of `n` trits whose value is below
  `3^n` and congruent to `A · B · 3^nudge` modulo `p = 3^n - c`. Proof-only.
-/
import BsLink2.Link2.PayToll

namespace BsLink2.Link2

open MegaDreifach.Link2

set_option maxHeartbeats 2000000 in
/-- B3. `multiply f a b nudge`, for registers `a`, `b` of `n` trits, a non-empty trit toll
    of fewer than `n` trits and a nudge of 0, 1 or 2, returns a register of `n` trits
    whose value is below `3^n` and equals `A · B · 3^nudge` minus a multiple of
    `p = 3^n - c`. -/
theorem multiply_spec (f : Bs.Field) (n : Nat) (toll : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n)
    (a b : Array Int) (hta : Trits a) (htb : Trits b) (ha : a.size = n) (hb : b.size = n)
    (nudge : Nat) (hnu : nudge ≤ 2) (hfit : FitsLen (2 * n + nudge)) :
    ∃ out, Bs.multiply f a b (Int.ofNat nudge) = .ok out ∧ out.size = n ∧ Trits out ∧
      val out < pw n ∧ ∃ K : Int, val out = val a * val b * pw nudge - K * (pw n - val toll) := by
  unfold Bs.multiply
  simp only [listLen_eq, hn, ha, hb, sEq_int, decide_True, pure_eq_ok, if_true, ok_bind,
    sudoAssert_true]
  have hn1 : 1 ≤ n := by omega
  have hf2 : FitsLen (2 * n) := FitsLen.of_le hfit (by omega)
  have hfn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hm2 : SudoRt.mulI 2 (Int.ofNat n) = .ok (Int.ofNat (2 * n)) := mulI_ofNat 2 n hf2
  rw [show decide (Int.ofNat nudge ≥ 0) = true from decide_eq_true (Int.ofNat_nonneg _),
    show decide (Int.ofNat nudge ≤ 2) = true from decide_eq_true
      (show Int.ofNat nudge ≤ Int.ofNat 2 from (ofNat_le_iff nudge 2).mpr hnu)]
  simp only [if_true, ok_bind, sudoAssert_true, hm2, addI_ofNat _ _ hfit, filledL_ofNat,
    subI_ofNat_one n hn1 hfn]
  rw [bind_ok_right, fuelRange_eq]
  have hA0 := val_nonneg hta
  have hA1 := val_lt hta
  rw [ha] at hA1
  have hpn := pw_pos nudge
  obtain ⟨W, hW⟩ : ∃ W, W = val a * pw nudge := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact Int.mul_nonneg hA0 (Int.le_of_lt hpn)
  have hBl : valL b.toList < pw n := by have := val_lt htb; rw [hb] at this; exact this
  have hB0 : 0 ≤ valL b.toList := valL_nonneg htb
  have hWB : W * valL b.toList < pw (2 * n + nudge) := by
    have e : pw (2 * n + nudge) = pw n * pw n * pw nudge := by
      rw [show 2 * n + nudge = n + n + nudge by omega, pw_add, pw_add]
    have h1 : val a * valL b.toList ≤ val a * pw n :=
      Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hBl) hA0
    have h2 : val a * pw n < pw n * pw n := Int.mul_lt_mul_of_pos_right hA1 (pw_pos n)
    have h3 : val a * valL b.toList * pw nudge < pw n * pw n * pw nudge :=
      Int.mul_lt_mul_of_pos_right (by omega) hpn
    rw [e, hW, Int.mul_right_comm]; exact h3
  refine asc_exists (fromN := 0) (toN := n - 1) (fun i (st : Array Int) =>
      st.size = 2 * n + nudge ∧ Trits st ∧ val st = W * valL (b.toList.take i))
    (Nat.zero_le _) ⟨by simp, trits_mkArray_zero _, by simp [val_mkArray_zero, valL]⟩ ?_ ?_
  · intro i st _ hi hI
    obtain ⟨hsz, htr', hv⟩ := hI
    have hib : i < b.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    have hfin : FitsLen (i + nudge) := FitsLen.of_le hfit (by omega)
    have hil : i < b.toList.length := by simpa using hib
    have htake := valL_take_succ b.toList i hil
    have hget : b.toList[i] = b[i] := by simp
    rw [hget] at htake
    have hle := valL_take_le htb (i + 1)
    have hWle : W * valL (b.toList.take (i + 1)) ≤ W * valL b.toList :=
      Int.mul_le_mul_of_nonneg_left hle hW0
    have hsplit : W * valL (b.toList.take (i + 1)) = W * valL (b.toList.take i) + b[i] * (W * pw i) := by
      rw [htake, Int.mul_add, Int.mul_left_comm]
    have hlayv : val a * pw (i + nudge) = W * pw i := by
      rw [hW, Nat.add_comm i nudge, pw_add, Int.mul_assoc]
    have hd := trits_get htb i hib
    have hWp : 0 ≤ W * pw i := Int.mul_nonneg hW0 (Int.le_of_lt (pw_pos i))
    have hroom : i + nudge + a.size ≤ st.size := by omega
    have hfst : FitsLen st.size := by rw [hsz]; exact hfit
    have hngt : ¬ (Int.ofNat i > Int.ofNat (n - 1)) := ofNat_not_gt hi
    dsimp only
    rw [if_neg hngt, atL_ofNat b i hib]
    simp only [ok_bind]
    rcases (by omega : b[i] = 0 ∨ b[i] = 1 ∨ b[i] = 2) with hc | hc | hc
    · refine ⟨st, ⟨hsz, htr', by rw [hv, hsplit, hc]; omega⟩, ?_⟩
      rw [hc]
      rw [show (if (1:Int) > 0 then 1 else ((0:Int) - 1).natAbs + 1) = 0 + 1 from rfl,
        runLoopOn_succ]
      simp
      exact asc_tail_cast _ _ hfi _
    · rw [hc, Int.one_mul] at hsplit
      obtain ⟨s2, hlay, hsz2, htr2, hv2⟩ := lay_spec st a (i + nudge) htr' hta (by omega)
        hroom hfst (by rw [hsz, hlayv, hv]; omega)
      refine ⟨s2, ⟨by omega, htr2, by rw [hv2, hv, hsplit, hlayv]⟩, ?_⟩
      rw [hc]
      rw [show (if (1:Int) > 1 then 1 else ((1:Int) - 1).natAbs + 1) = 0 + 1 from rfl,
        runLoopOn_succ]
      have hlay' : Bs.lay st a ((i : Int) + (nudge : Int)) = .ok s2 := by simpa using hlay
      simp [addI_cast _ _ hfin, hlay']
      exact asc_tail_cast _ _ hfi _
    · have hsplit2 : W * valL (b.toList.take (i + 1)) =
          W * valL (b.toList.take i) + 2 * (W * pw i) := by rw [hsplit, hc]
      obtain ⟨s2, hlay, hsz2, htr2, hv2⟩ := lay_spec st a (i + nudge) htr' hta (by omega)
        hroom hfst (by rw [hsz, hlayv, hv]; omega)
      obtain ⟨s3, hlay2, hsz3, htr3, hv3⟩ := lay_spec s2 a (i + nudge) htr2 hta (by omega)
        (by omega) (by rw [hsz2]; exact hfst) (by rw [hsz2, hsz, hlayv, hv2, hlayv, hv]; omega)
      refine ⟨s3, ⟨by omega, htr3, by rw [hv3, hv2, hv, hsplit2, hlayv]; omega⟩, ?_⟩
      rw [hc]
      rw [show (if (1:Int) > 2 then 1 else ((2:Int) - 1).natAbs + 1) = 1 + 1 from rfl,
        runLoopOn_succ]
      have hlay' : Bs.lay st a ((i : Int) + (nudge : Int)) = .ok s2 := by simpa using hlay
      have hlay2' : Bs.lay s2 a ((i : Int) + (nudge : Int)) = .ok s3 := by simpa using hlay2
      simp [addI_cast _ _ hfin, hlay', hlay2', addI_1_1, runLoopOn_succ]
      exact asc_tail_cast _ _ hfi _
  · intro st hI
    obtain ⟨hsz, htr', hv⟩ := hI
    rw [show n - 1 + 1 = b.toList.length by simp; omega, valL_take_length] at hv
    obtain ⟨s', hpay, hsz', htr'', hlt, K, hK⟩ :=
      pay_toll_spec f n toll st hn ht htt hts htn htr' (by omega) (by rw [hsz]; exact hfit)
    have hpay' : Bs.pay_toll f st = .ok s' := hpay
    simp only [hpay', ok_bind]
    rw [show Bs.empty_register f = .ok (Array.mkArray n 0) by
      unfold Bs.empty_register; rw [hn, filledL_ofNat]; rfl, ok_bind, bind_ok_right]
    have hsn : n ≤ s'.size := by omega
    refine asc_exists (fromN := 0) (toN := n - 1) (fun i (o : Array Int) =>
        o.size = n ∧ ∀ j (hj : j < o.size), (j < i → ∃ hj' : j < s'.size, o[j] = s'[j]) ∧
          (i ≤ j → o[j] = 0))
      (Nat.zero_le _) ⟨by simp, fun j hj => ⟨fun h => absurd h (Nat.not_lt_zero _),
        fun _ => by simp⟩⟩ ?_ ?_
    · intro i o _ hi hI
      obtain ⟨hosz, hoj⟩ := hI
      have hio : i < o.size := by omega
      have his : i < s'.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      refine ⟨o.set ⟨i, hio⟩ s'[i], ⟨by simp [hosz], ?_⟩, ?_⟩
      · intro j hj
        simp only [Array.size_set] at hj
        by_cases hji : j = i
        · subst hji
          exact ⟨fun _ => ⟨his, by simp⟩, fun h => absurd h (by omega)⟩
        · rw [Array.getElem_set_ne _ _ _ _ (Ne.symm hji)]
          have := hoj j hj
          exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
      · dsimp only
        rw [if_neg (ofNat_not_gt hi), atL_ofNat s' i his, ok_bind, putL_ofNat o i _ hio, ok_bind]
        exact asc_tail _ i hfi _
    · intro o hI
      obtain ⟨hosz, hoj⟩ := hI
      refine ⟨o, rfl, hosz, ?_⟩
      have hlist : o.toList = s'.toList.take n := by
        apply List.ext_getElem
        · simp [hosz]; omega
        · intro j h1 h2
          have hjo : j < o.size := by simpa using h1
          obtain ⟨hj', e⟩ := (hoj j hjo).1 (by omega)
          simp [e]
      have hsplit := valL_split s'.toList n
      rw [length_take_of_lt (by simpa using (show n < s'.size by omega) : n < s'.toList.length)] at hsplit
      have hd0 := valL_nonneg (tritsL_drop htr'' n)
      have ht0 := valL_nonneg (tritsL_take htr'' n)
      have hdrop0 : valL (s'.toList.drop n) = 0 := by
        rcases (by omega : valL (s'.toList.drop n) = 0 ∨ 1 ≤ valL (s'.toList.drop n)) with e | e
        · exact e
        · have : pw n * 1 ≤ pw n * valL (s'.toList.drop n) :=
            Int.mul_le_mul_of_nonneg_left e (Int.le_of_lt (pw_pos n))
          unfold val at hlt; omega
      have hvo : val o = val s' := by
        unfold val; rw [hlist, hsplit, hdrop0]; simp
      refine ⟨by unfold Trits; rw [hlist]; exact tritsL_take htr'' n, by rw [hvo]; exact hlt,
        K, ?_⟩
      rw [hvo, hK, hv, hW, Int.mul_right_comm]
      rfl

end BsLink2.Link2
