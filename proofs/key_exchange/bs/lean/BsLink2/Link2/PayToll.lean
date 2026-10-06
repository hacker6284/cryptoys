/-
  BS Link 2: B4 `pay_toll` (the fold). On a trit strip longer than `n`, with a toll of
  fewer than `n` trits, the emitted fold never fails its asserts (in particular the
  `lifts_per_hole` = 4 bound per hole holds), and it leaves a trit strip below `3^n`
  whose value differs from the input by a multiple of `p = 3^n - c`. Proof-only.
-/
import BsLink2.Link2.Lay

namespace BsLink2.Link2

open MegaDreifach.Link2

set_option maxHeartbeats 2000000 in
/-- B4. Paying the toll: for a field with `n` holes and a non-empty trit toll `c` of
    fewer than `n` trits, and a trit strip of more than `n` holes, `pay_toll` succeeds
    (no assert fails: at most `Bs.lifts_per_hole` = 4 lifts empty each hole) and returns a
    trit strip of the same size whose value is below `3^n` and equals the input's value
    minus a multiple of `p = 3^n - c`. -/
theorem pay_toll_spec (f : Bs.Field) (n : Nat) (toll strip : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n)
    (htr : Trits strip) (hL : n < strip.size) (hfit : FitsLen strip.size) :
    ∃ s', Bs.pay_toll f strip = .ok s' ∧ s'.size = strip.size ∧ Trits s' ∧
      val s' < pw n ∧ ∃ K : Int, val s' = val strip - K * (pw n - val toll) := by
  unfold Bs.pay_toll Bs.lifts_per_hole
  simp only [listLen_eq]
  rw [hn, ht,
    show decide (Int.ofNat toll.size < Int.ofNat n) = true from
      decide_eq_true ((ofNat_lt_iff _ _).mpr htn), sudoAssert_true, ok_bind,
    subI_ofNat_one _ (by omega) hfit]
  simp only [ok_bind]
  rw [except_bind_pure, fuelDown_eq]
  refine desc_exists (fun m (st : Array Int) => st.size = strip.size ∧ Trits st ∧
      val st < pw m ∧ ∃ K : Int, val st = val strip - K * (pw n - val toll))
    (by omega) ⟨rfl, htr, by rw [show strip.size - 1 + 1 = strip.size by omega]; exact val_lt htr,
      0, by simp⟩ ?_ ?_
  · intro h st h1 h2 hI
    obtain ⟨hsz, htr', hv, K, hK⟩ := hI
    have hh : h < st.size := by omega
    have hnlt : ¬ (Int.ofNat h < Int.ofNat n) := by rw [ofNat_lt_iff]; omega
    dsimp only
    rw [if_neg hnlt]
    -- arithmetic facts for hole h
    have hhn : n ≤ h := h1
    have hfh : FitsLen h := FitsLen.of_le hfit (by omega)
    have hX : pw h = pw (h - n) * pw n := by rw [← pw_add]; congr 1; omega
    have hc0 := val_nonneg htt
    have hc1 : val toll < pw (n - 1) :=
      Int.lt_of_lt_of_le (val_lt htt) (pw_mono (by omega))
    have hq := pw_pos (h - n)
    have hZ3 : 3 * (val toll * pw (h - n)) < pw h := by
      have : val toll * pw (h - n) < pw (n - 1) * pw (h - n) :=
        Int.mul_lt_mul_of_pos_right hc1 hq
      have e : pw h = 3 * (pw (n - 1) * pw (h - n)) := by
        rw [← pw_add, ← pw_succ]; congr 1; omega
      omega
    have hZ0 : 0 ≤ val toll * pw (h - n) := Int.mul_nonneg hc0 (Int.le_of_lt hq)
    have hD : pw h - val toll * pw (h - n) = pw (h - n) * (pw n - val toll) := by
      rw [hX, Int.mul_sub, Int.mul_comm (val toll)]
    refine exists_bind (fun r => ∃ st', r = SudoRt.Flow.cont st' ∧ st'.size = strip.size ∧
        Trits st' ∧ val st' < pw h ∧ ∃ K : Int, val st' = val strip - K * (pw n - val toll))
      ?_ ?_
    · rw [except_bind_pure, fuelRange_eq]
      obtain ⟨D, hDdef⟩ : ∃ D, D = pw h - val toll * pw (h - n) := ⟨_, rfl⟩
      have hhs : h + 1 ≤ strip.size := by omega
      have hpL := pw_mono hhs
      refine asc_exists (fromN := 1) (toN := 4) (fun t (s1 : Array Int) =>
          s1.size = strip.size ∧ Trits s1 ∧ (∃ K : Int, val s1 = val strip - K * (pw n - val toll)) ∧
          val s1 ≤ val st ∧
          ((∀ hh' : h < s1.size, s1[h]'hh' = 0) ∨ val s1 + D * ((t : Int) - 1) ≤ val st))
        (by decide) ⟨hsz, htr', ⟨K, hK⟩, Int.le_refl _, Or.inr (by simp)⟩ ?_ ?_
      · intro t s1 ht1 ht4 hI
        obtain ⟨hsz1, htr1, ⟨K1, hK1⟩, hle1, hdis⟩ := hI
        have hh1 : h < s1.size := by omega
        have hft : FitsLen (t + 1) := by unfold FitsLen i64MaxNat; omega
        have hngt : ¬ (Int.ofNat t > 4) := by
          show ¬ (Int.ofNat t > Int.ofNat 4); rw [gt_iff_lt, ofNat_lt_iff]; omega
        dsimp only
        rw [if_neg hngt, atL_ofNat s1 h hh1]
        simp only [ok_bind]
        have hd := trits_get htr1 h hh1
        have hge := val_ge_digit htr1 h hh1
        rcases (by omega : s1[h] = 0 ∨ s1[h] = 1 ∨ s1[h] = 2) with hc | hc | hc
        · refine ⟨s1, ⟨hsz1, htr1, ⟨K1, hK1⟩, hle1, Or.inl (fun _ => hc)⟩, ?_⟩
          simp only [hc, sEq_int, decide_True, Bool.not_true, Bool.false_eq_true, if_false,
            pure_eq_ok, ok_bind]
          exact asc_tail 4 t hft s1
        all_goals
          have hdis' : val s1 + D * ((t : Int) - 1) ≤ val st := by
            rcases hdis with h0 | h0
            · have := h0 hh1; omega
            · exact h0
          have hmulD : D * (((t + 1 : Nat) : Int) - 1) = D * ((t : Int) - 1) + D := by
            rw [show (((t + 1 : Nat) : Int) - 1) = ((t : Int) - 1) + 1 by omega, Int.mul_add,
              Int.mul_one]
          have hs0 : h < (s1.set ⟨h, hh1⟩ 0).size := by simpa using hh1
          have htr0 := trits_set htr1 h hh1 (v := 0) (by decide)
          have hv0 := val_set s1 h hh1 0
          rw [hc] at hv0
          have hroom : h - n + toll.size ≤ (s1.set ⟨h, hh1⟩ 0).size := by simp; omega
          have hfit0 : FitsLen (s1.set ⟨h, hh1⟩ 0).size := by simp [hsz1]; exact hfit
        · -- white peg: lay the toll once
          obtain ⟨s2, hlay, hsz2, htr2, hv2⟩ := lay_spec (s1.set ⟨h, hh1⟩ 0) toll (h - n) htr0 htt
            hts hroom hfit0 (by simp [hsz1]; omega)
          refine ⟨s2, ⟨by simp [hsz1] at hsz2; omega, htr2,
            ⟨K1 + pw (h - n), by rw [hv2, hv0, hK1, Int.add_mul]; omega⟩,
            by omega, Or.inr (by rw [hmulD]; omega)⟩, ?_⟩
          rw [hc]
          simp only [show (!SudoRt.SEq.beq (1:Int) 0) = true from rfl, if_true,
            putL_ofNat s1 h 0 hh1, ok_bind, pure_eq_ok]
          rw [show (if (1:Int) > 1 then 1 else ((1:Int) - 1).natAbs + 1) = 0 + 1 from rfl,
            runLoopOn_succ]
          simp only [show ¬ ((1:Int) > 1) from by decide, if_false, subI_ofNat h n hfh hhn,
            ok_bind, hlay, pure_eq_ok]
          simp
          exact asc_tail_cast 4 t hft s2
        · -- red peg: lay the toll twice
          obtain ⟨s2, hlay, hsz2, htr2, hv2⟩ := lay_spec (s1.set ⟨h, hh1⟩ 0) toll (h - n) htr0 htt
            hts hroom hfit0 (by simp [hsz1]; omega)
          have hroom2 : h - n + toll.size ≤ s2.size := by simp at hsz2; omega
          have hfit2 : FitsLen s2.size := by simp at hsz2; rw [hsz2, hsz1]; exact hfit
          obtain ⟨s3, hlay2, hsz3, htr3, hv3⟩ := lay_spec s2 toll (h - n) htr2 htt
            hts hroom2 hfit2 (by simp at hsz2; rw [hsz2, hsz1]; omega)
          refine ⟨s3, ⟨by simp at hsz2; omega, htr3,
            ⟨K1 + 2 * pw (h - n), by rw [hv3, hv2, hv0, hK1, Int.add_mul, Int.mul_assoc]; omega⟩,
            by omega, Or.inr (by rw [hmulD]; omega)⟩, ?_⟩
          rw [hc]
          simp only [show (!SudoRt.SEq.beq (2:Int) 0) = true from rfl, if_true,
            putL_ofNat s1 h 0 hh1, ok_bind, pure_eq_ok]
          rw [show (if (1:Int) > 2 then 1 else ((2:Int) - 1).natAbs + 1) = 1 + 1 from rfl,
            runLoopOn_succ]
          simp only [show ¬ ((1:Int) > 2) from by decide, if_false, subI_ofNat h n hfh hhn,
            ok_bind, hlay, pure_eq_ok]
          have hlay2' : Bs.lay s2 toll ((h - n : Nat) : Int) = .ok s3 := hlay2
          simp [addI_1_1, runLoopOn_succ, hlay2']
          exact asc_tail_cast 4 t hft s3
      · intro s1 hI
        obtain ⟨hsz1, htr1, ⟨K1, hK1⟩, hle1, hdis⟩ := hI
        have hh1 : h < s1.size := by omega
        have hd := trits_get htr1 h hh1
        have hge := val_ge_digit htr1 h hh1
        have hz : s1[h] = 0 := by
          rcases hdis with h0 | h0
          · exact h0 hh1
          · have h4 : D * (((4 + 1 : Nat) : Int) - 1) = D * 4 := by
              rw [show (((4 + 1 : Nat) : Int) - 1) = 4 from rfl]
            rw [h4] at h0
            have hpX : pw (h + 1) = 3 * pw h := pw_succ h
            have hmul : s1[h] * pw h ≥ 1 * pw h ∨ s1[h] = 0 := by
              rcases (by omega : s1[h] = 0 ∨ s1[h] = 1 ∨ s1[h] = 2) with e | e | e
              · exact Or.inr e
              · left; rw [e]; exact Int.le_refl _
              · left; rw [e]; have := pw_pos h; omega
            rcases hmul with hm | hm
            · omega
            · exact hm
        refine ⟨SudoRt.Flow.cont s1, ?_, s1, rfl, hsz1, htr1,
          val_lt_of_digit_zero htr1 h hh1 (by omega) hz, K1, hK1⟩
        dsimp only
        rw [atL_ofNat s1 h hh1, ok_bind, hz]
        rfl
    · rintro r ⟨st', rfl, hsz', htr'', hv', K', hK'⟩
      refine ⟨st', ⟨hsz', htr'', hv', K', hK'⟩, ?_⟩
      simp only [pure_eq_ok]
      exact desc_tail_to h n hhn hfh st' 
  · intro st hI
    obtain ⟨hsz, htr', hv, K, hK⟩ := hI
    exact ⟨st, rfl, hsz, htr', hv, K, hK⟩

end BsLink2.Link2
