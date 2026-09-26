/-
  LINK 2. `big_factorial` through `51!`.

  Each step is the wide-by-small product `big_mul_nat`: the accumulator is
  `natLimbs` of `(i - 1)!` and the factor `i ≤ 51` is one limb.
  `51! < 10^72`, so the limb string stays inside eight base-`10^9` digits
  and the length fits in an i64.

  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.MulWide

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem fits51 : FitsLen 51 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fiftyOne_lt_limb : 51 < limbBase := by
  unfold limbBase
  decide

private theorem factorial_51_lt : factorial 51 < limbBase ^ 8 := by
  unfold factorial limbBase
  decide

private theorem factorial_le_succ (b : Nat) : factorial b ≤ factorial (b + 1) := by
  have hmul : factorial b ≤ factorial b * (b + 1) :=
    Nat.le_mul_of_pos_right (factorial b) (Nat.succ_pos b)
  rw [factorial_succ, Nat.mul_comm]
  exact hmul

private theorem factorial_mono (a b : Nat) (h : a ≤ b) : factorial a ≤ factorial b := by
  induction b generalizing a with
  | zero =>
    have : a = 0 := Nat.eq_zero_of_le_zero h
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hle : a ≤ b
    · exact Nat.le_trans (ih a hle) (factorial_le_succ b)
    · have heq : a = b + 1 := by omega
      subst heq
      exact Nat.le_refl _

private theorem factorial_lt_pow8 (n : Nat) (hn : n ≤ 51) :
    factorial n < limbBase ^ 8 :=
  Nat.lt_of_le_of_lt (factorial_mono n 51 hn) factorial_51_lt

private theorem factorial_limbs_le (n : Nat) (hn : n ≤ 51) :
    (natLimbs (factorial n)).length ≤ 8 :=
  natLimbs_length_le (factorial n) 8 (factorial_lt_pow8 n hn)

private theorem fits_fact_limbs (n : Nat) (hn : n ≤ 51) :
    FitsLen ((natLimbs (factorial n)).length + 1) :=
  fits_le9 (by
    have h := factorial_limbs_le n hn
    omega)

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem natLimbs_one : natLimbs 1 = [1] := by
  have hlt : 1 < limbBase := by unfold limbBase; decide
  exact natLimbs_of_pos_lt 1 (by decide) hlt

private theorem limbs_one : limbsOfNat 1 = [1] := by
  have hlt : 1 < limbBase := by unfold limbBase; decide
  have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt hlt
  simp [limbsOfNat, hq, Nat.mod_eq_of_lt hlt]

/-- One step of `big_factorial`'s `for i = 2 to n` loop. -/
def factStep51 (toV : Int) (σ : Int × Megadreifach.BigInt) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Megadreifach.BigInt) Megadreifach.BigInt) :=
  let i := σ.1
  let r := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, r))
    else
      match ← ((do
        let t1 ← Megadreifach.big_from_int i
        let t2 ← Megadreifach.big_mul r t1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) t2)) :
          Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

private theorem factMul51 (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 51) :
    Megadreifach.big_mul (bigOf (natLimbs (factorial (i - 1))))
        (bigOf (natLimbs i)) =
      .ok (bigOf (natLimbs (factorial i))) := by
  have hi0 : 0 < i := by omega
  have hilt : i < limbBase := Nat.lt_of_le_of_lt hhi fiftyOne_lt_limb
  have hpred : i - 1 ≤ 51 := by omega
  have hmul := big_mul_nat i (factorial (i - 1)) hilt (fits_fact_limbs (i - 1) hpred)
  rw [Nat.mul_comm, factorial_pred_mul i hi0] at hmul
  exact hmul

private theorem factStep51_hit (n i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ n) (hn : n ≤ 51) :
    factStep51 (Int.ofNat n) (Int.ofNat i, bigOf (natLimbs (factorial (i - 1)))) =
      if i = n then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigOf (natLimbs (factorial i))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigOf (natLimbs (factorial i)))) := by
  unfold factStep51
  dsimp
  have hngt : ¬ (i : Int) > (n : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hi0 : i ≠ 0 := by omega
  have hiPos : 0 < i := by omega
  have hilt : i < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hn) fiftyOne_lt_limb
  have hfits : FitsLen i := FitsLen.of_le fits51 (Nat.le_trans hhi hn)
  rw [show (i : Int) = Int.ofNat i from rfl, big_from_int_refines i hfits, ok_bind]
  have hlimbs : limbsOfNat i = natLimbs i := by
    rw [natLimbs_of_pos_lt i hiPos hilt]
    simp [limbsOfNat, hi0, Nat.div_eq_of_lt hilt, Nat.mod_eq_of_lt hilt]
  rw [hlimbs, factMul51 i hlo (Nat.le_trans hhi hn), ok_bind, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : i = n
  · have hbeq : ((i : Int) == (n : Int)) = true := by simp [beq_int_iff, heq]
    simp [hbeq, heq, pure_eq_ok]
  · have hneI : (i : Int) ≠ (n : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == (n : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hadd := addI_ofNat_one i (FitsLen.of_le fits51 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    simp [hbeq, heq, hadd, pure_eq_ok, ok_bind]

private theorem factStep51_gt (toV i : Int) (r : Megadreifach.BigInt) (h : i > toV) :
    factStep51 toV (i, r) = .ok (SudoRt.Flow.brk (i, r)) := by
  unfold factStep51
  dsimp
  rw [if_pos h, pure_eq_ok]

private theorem big_factorial_from2 (n : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 51) :
    Megadreifach.big_factorial (n : Int) = .ok (bigOf (natLimbs (factorial n))) := by
  unfold Megadreifach.big_factorial
  rw [show (1 : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
  rw [limbs_one, ← natLimbs_one]
  dsimp
  rw [fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := factStep51 (n : Int))
    intro σ
    unfold factStep51
    dsimp
    rfl
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  have hf2 : factorial (2 - 1) = 1 := by simp [factorial]
  rw [← hf2]
  apply chain_loop
    (f := fun i => bigOf (natLimbs (factorial (i - 1))))
    (fromN := 2) (toN := n)
    (hle := hn2)
    (goal := .ok (bigOf (natLimbs (factorial n))))
  · intro i hlo hhi
    have hs := factStep51_hit n i hlo hhi hn
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · have hsub : (n + 1) - 1 = n := by omega
    rw [hsub, pure_eq_ok]

/--
  `big_factorial n = n!` for `n ≤ 51`.

  `12!` is one limb and `26!` is three. `27!` through `51!` need up to
  eight base-`10^9` limbs (`51! < 10^72`). Each step multiplies the
  accumulator by `i ≤ 51` via `big_mul_nat`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem big_factorial_51 (n : Nat) (hn : n ≤ 51) :
    Megadreifach.big_factorial (n : Int) = .ok (bigOf (natLimbs (factorial n))) := by
  by_cases hn1 : n ≤ 1
  · unfold Megadreifach.big_factorial
    rw [show (1 : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
    rw [limbs_one, ← natLimbs_one]
    have hf : factorial n = 1 := by
      cases n with
      | zero => rfl
      | succ n =>
        have : n = 0 := by omega
        subst this
        simp [factorial]
    rw [hf]
    dsimp
    have hgt : (2 : Int) > (n : Int) := by
      have hle : (n : Int) ≤ 1 := Int.ofNat_le.mpr hn1
      omega
    rw [fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := factStep51 (n : Int))
      intro σ
      unfold factStep51
      dsimp
      rfl
    rw [asc_break (2 : Int) (n : Int) (bigOf (natLimbs 1)) _ _ _ hgt
        (factStep51_gt (n : Int) 2 (bigOf (natLimbs 1)) hgt), pure_eq_ok]
  · exact big_factorial_from2 n (by omega) hn

end MegaDreifach.Link2
