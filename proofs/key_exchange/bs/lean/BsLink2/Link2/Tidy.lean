/-
  BS Link 2: B3 step 3 `slide` and B5 `tidy`. Proof-only.
-/
import BsLink2.Link2.Multiply
import BsLink2.Link2.Bridge

namespace BsLink2.Link2

open MegaDreifach.Link2

/-- B3 step 3. Sliding an answer into a register of the same (non-zero) size leaves exactly
    the answer there. -/
theorem slide_spec (dest answer : Array Int) (h : dest.size = answer.size) (hpos : 0 < dest.size)
    (hfit : FitsLen dest.size) : Bs.slide dest answer = .ok answer := by
  unfold Bs.slide
  simp only [listLen_eq, h, sEq_int, decide_True]
  rw [sudoAssertEq_self, ok_bind, subI_ofNat_one _ (by omega) (by rw [← h]; exact hfit)]
  simp only [ok_bind]
  have hfa : FitsLen answer.size := by rw [← h]; exact hfit
  have hpa : 0 < answer.size := by omega
  rw [except_bind_pure, fuelRange_eq]
  refine asc_goal (fromN := 0) (toN := answer.size - 1) (fun _ (o : Array Int) => o.size = answer.size)
    (Nat.zero_le _) h ?_ ?_
  · intro i o _ hi hI
    have hio : i < o.size := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfa (by omega)
    refine ⟨o.set ⟨i, hio⟩ 0, by simp [hI], ?_⟩
    dsimp only
    rw [if_neg (ofNat_not_gt hi), putL_ofNat o i _ hio, ok_bind]
    exact asc_tail _ i hfi _
  · intro o hI
    dsimp only
    rw [hI, subI_ofNat_one _ hpa hfa, ok_bind, except_bind_pure, fuelRange_eq]
    refine asc_goal (fromN := 0) (toN := answer.size - 1) (fun i (o : Array Int) =>
        o.size = answer.size ∧ ∀ j (hj : j < i) (hj1 : j < o.size) (hj2 : j < answer.size),
          o[j] = answer[j]) (Nat.zero_le _) ⟨hI, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_ ?_
    · intro i o _ hi hI
      obtain ⟨hosz, hoj⟩ := hI
      have hio : i < o.size := by omega
      have hia : i < answer.size := by omega
      have hfi : FitsLen (i + 1) := FitsLen.of_le hfa (by omega)
      refine ⟨o.set ⟨i, hio⟩ answer[i], ⟨by simp [hosz], ?_⟩, ?_⟩
      · intro j hj hj1 hj2
        by_cases hji : j = i
        · subst hji; simp
        · simp only [Array.size_set] at hj1
          rw [Array.getElem_set_ne _ _ _ _ (Ne.symm hji)]
          exact hoj j (by omega) hj1 hj2
      · dsimp only
        rw [if_neg (ofNat_not_gt hi), atL_ofNat answer i hia, ok_bind, putL_ofNat o i _ hio, ok_bind]
        exact asc_tail _ i hfi _
    · intro o hI
      obtain ⟨hosz, hoj⟩ := hI
      show Except.ok o = Except.ok answer
      congr 1
      apply Array.ext _ _ hosz
      intro j h1 h2
      exact hoj j (by omega) h1 h2

set_option maxHeartbeats 1000000 in
/-- B5. Tidying a register of `n` trits (well-formed toll, `n + 1` fits `i64`) returns a
    register of `n` trits whose value is the input's value modulo `p = 3^n - c`. -/
theorem tidy_spec (f : Bs.Field) (n : Nat) (toll : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n) (hfit : FitsLen (n + 1))
    (x : Array Int) (htx : Trits x) (hx : x.size = n) :
    ∃ y, Bs.tidy f x = .ok y ∧ y.size = n ∧ Trits y ∧
      val y = val x % (pw n - val toll) := by
  unfold Bs.tidy Bs.tidy_in_place
  simp only [listLen_eq, hn, hx, ht, sEq_int]
  rw [sudoAssertEq_self, ok_bind]
  -- the copy with one extra hole
  have hcs : (SudoRt.concatL x #[0]).size = n + 1 := by simp [SudoRt.concatL, hx]
  have hctl : (SudoRt.concatL x #[0]).toList = x.toList ++ [0] := by simp [SudoRt.concatL]
  have hct : Trits (SudoRt.concatL x #[0]) := by
    unfold Trits; rw [hctl]; exact tritsL_append.mpr ⟨htx, by intro v hv; simp at hv; omega⟩
  have hcv : val (SudoRt.concatL x #[0]) = val x := by
    unfold val; rw [hctl, valL_append]; simp [valL]
  have hc0 := val_nonneg htt
  have hc1 : val toll < pw (n - 1) := Int.lt_of_lt_of_le (val_lt htt) (pw_mono (by omega))
  have hpn : pw n = 3 * pw (n - 1) := by rw [← pw_succ]; congr 1; omega
  have hx1 : val x < pw n := by have := val_lt htx; rwa [hx] at this
  have hx0 := val_nonneg htx
  obtain ⟨c1, hlay, hsz1, htr1, hv1⟩ := lay_spec (SudoRt.concatL x #[0]) toll 0 hct htt hts
    (by omega) (by rw [hcs]; exact hfit) (by rw [hcs, hcv, pw_succ]; simp [pw_zero]; omega)
  have hlay' : Bs.lay (SudoRt.concatL x #[0]) toll 0 = .ok c1 := hlay
  have hc1s : c1.size = n + 1 := by rw [hsz1, hcs]
  rw [hlay', ok_bind]
  have hn1 : n < c1.size := by omega
  rw [atL_ofNat c1 n hn1, ok_bind]
  -- the digit in the extra hole
  have hl : n < c1.toList.length := by simpa using hn1
  have hsplit := valL_split c1.toList n
  rw [length_take_of_lt hl] at hsplit
  have hd := valL_drop_cons c1.toList n hl
  have hdrop : c1.toList.drop (n + 1) = [] := by
    apply List.drop_eq_nil_of_le; simp; omega
  rw [hdrop] at hd
  have hget : c1.toList[n] = c1[n] := by simp
  rw [hget] at hd
  simp only [valL, Int.mul_zero, Int.add_zero] at hd
  rw [hd] at hsplit
  have hT0 := valL_nonneg (tritsL_take htr1 n)
  have hT1 := valL_lt (tritsL_take htr1 n)
  rw [length_take_of_lt hl] at hT1
  have hdig := trits_get htr1 n hn1
  rw [hcv, pw_zero, Int.mul_one] at hv1
  unfold val at hv1
  rcases (by omega : c1[n] = 0 ∨ c1[n] = 1 ∨ c1[n] = 2) with e | e | e
  · -- no spill: x < p already
    rw [e] at hsplit
    refine ⟨x, ?_, hx, htx, ?_⟩
    · simp [e]; rfl
    · rw [Int.emod_eq_of_lt hx0 (by simp at hsplit; unfold val at *; omega)]
  · -- a white spilled: x ≥ p, the copy is x - p
    rw [e, Int.mul_one] at hsplit
    have hpop : SudoRt.popL c1 = .ok (c1.pop, c1[n]) := by
      unfold SudoRt.popL
      have : (c1.size == 0) = false := by rw [hc1s]; rfl
      simp only [this, if_false, Bool.false_eq_true]
      have hj : c1.size - 1 < c1.size := by omega
      rw [dif_pos hj]
      simp [show c1.size - 1 = n by omega]; rfl
    have hpsz : c1.pop.size = n := by simp; omega
    have hptl : c1.pop.toList = c1.toList.take n := by
      rw [Array.toList_pop, List.dropLast_eq_take]; congr 1; simp; omega
    have hslide := slide_spec x c1.pop (by omega) (by omega) (FitsLen.of_le hfit (by omega))
    refine ⟨c1.pop, ?_, hpsz, by unfold Trits; rw [hptl]; exact tritsL_take htr1 n, ?_⟩
    · simp only [e, decide_True, Bool.true_eq_false, if_false, ok_bind, sudoAssertEq_self, hpop, hslide]
      simp [ite_false]; rfl
    · have hp : val x = (val x - (pw n - val toll)) + (pw n - val toll) * 1 := by
        rw [Int.mul_one]; omega
      unfold val at *
      rw [hptl, hp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · rw [e] at hsplit; unfold val at *; omega

end BsLink2.Link2
