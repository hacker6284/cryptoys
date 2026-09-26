/-
  LINK 2. `peel_leading` of the zero bigint for `d ≤ 26`.

  The quotient stays the empty limb list: each divisor `f ∈ 2..d` divides
  zero. The factoradic digit is `0 / d! = 0` and the remainder is `0`.
  For `d ≥ 20`, `d!` is three limbs (`10^18 ≤ 20!` and `26! < 10^27`).
  The emitter still builds that factorial, then multiplies it by the digit.
  The coefficient is zero, so `big_mul` short-circuits and the three limbs
  are never scaled.

  Not a positive rank. Not an arbitrary three-limb peel. Not `27!`.
  Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.AccThree

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem fits27 : FitsLen 27 := by
  unfold FitsLen i64MaxNat
  decide

private theorem twentySix_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

/-- One divisor step on the empty limb list. The quotient stays empty. -/
private theorem peelDivStep_wide (d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d) (hd : d ≤ 26) :
    peelDivStep (Int.ofNat d) (Int.ofNat f, bigOf []) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigOf []))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigOf [])) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) twentySix_lt_limb
  rw [show (f : Int) = Int.ofNat f from rfl, divmod_zero f hf0 hflt, ok_bind]
  rw [show ((bigOf [], (0 : Int)).1) = bigOf [] from rfl, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : f = d
  · have hbeq : ((f : Int) == (d : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (f : Int) ≠ (d : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((f : Int) == (d : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((f : Int) == (d : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one f (FitsLen.of_le fits27 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peelDivStep_gt (toV f : Int) (q : Megadreifach.BigInt) (h : f > toV) :
    peelDivStep toV (f, q) = .ok (SudoRt.Flow.brk (f, q)) := by
  unfold peelDivStep
  rw [if_pos h]
  rfl

/-- Finish of `peel_leading` once the quotient is still zero. -/
private theorem peel_after_three (d : Nat) (hd : d ≤ 26) :
    (do
      let idx ← Megadreifach.limb_to_small (bigOf [])
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub
        (bigOf []).sudo_6BigInt_5limbs prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat 0, (0 : Int)) := by
  rw [limb_to_small_zero, ok_bind, big_factorial_acc3 d hd, ok_bind,
    show (0 : Int) = Int.ofNat 0 from rfl, big_from_int_refines 0 FitsLen.zero, ok_bind]
  have hlimbs : limbsOfNat 0 = [] := by simp [limbsOfNat]
  rw [hlimbs, big_mul_zero_left, ok_bind]
  dsimp [bigOf]
  rw [mag_sub_zeros, ok_bind, make_big_false [] FitsLen.zero, ok_bind, pure_eq_ok]
  simp [dropTrail, bigNat_zero]

/--
  `peel_leading 0 d = (0, 0)` for `d ≤ 26`. The digit is `0 / d!`.

  For `d ≥ 20` the factorial is three limbs. The closing multiply is the
  zero coefficient, which short-circuits. Not a positive rank. Not `27!`.
  Not `51!`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_zero_three (d : Nat) (hd : d ≤ 26) :
    Megadreifach.peel_leading (bigNat 0) (d : Int) =
      .ok (bigNat 0, (0 : Int)) := by
  rw [bigNat_zero]
  unfold Megadreifach.peel_leading
  dsimp
  rw [fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := peelDivStep (d : Int))
    intro σ
    unfold peelDivStep
    dsimp
    rfl
  by_cases hd2 : 2 ≤ d
  · rw [show (2 : Int) = Int.ofNat 2 from rfl]
    apply chain_loop
      (f := fun _ : Nat => bigOf [])
      (fromN := 2) (toN := d)
      (hle := hd2)
      (goal := .ok (bigNat 0, (0 : Int)))
    · intro i hlo hhi
      exact peelDivStep_wide d i hlo hhi hd
    · exact peel_after_three d hd
  · have hlt : d < 2 := by omega
    have hgt : (2 : Int) > (d : Int) := by
      have : (d : Int) < 2 := (ofNat_lt_iff d 2).mpr hlt
      omega
    rw [asc_break (2 : Int) (d : Int) (bigOf []) _ _ _ hgt
        (peelDivStep_gt (d : Int) 2 (bigOf []) hgt)]
    exact peel_after_three d hd

/-- Same zero peel, as the factoradic digit `0 / d!` and remainder `0`. -/
theorem peel_leading_zero_digit_three (d : Nat) (hd : d ≤ 26) :
    Megadreifach.peel_leading (bigNat 0) (d : Int) =
      .ok (bigNat (0 % factorial d), ((0 / factorial d : Nat) : Int)) := by
  have hdiv : 0 / factorial d = 0 := Nat.div_eq_of_lt (factorial_pos d)
  have hmod : 0 % factorial d = 0 := Nat.mod_eq_of_lt (factorial_pos d)
  rw [hdiv, hmod]
  exact peel_leading_zero_three d hd

end MegaDreifach.Link2
