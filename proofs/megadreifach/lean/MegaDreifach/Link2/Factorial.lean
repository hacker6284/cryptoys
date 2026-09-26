/-
  LINK 2. `big_factorial` and `peel_leading` of the zero bigint.

  `12! < 10^9`, so it is one base-10^9 limb. `13! = 12! · 13` is the last
  product of the proved one-limb multiply (`big_mul_acc`); the value is two
  limbs. `14!` would multiply a two-limb accumulator, which is not this slice.
  `51!` is not claimed.

  `peel_leading` on the zero bigint, for `d ≤ 13`, divides the empty limb
  list by each `f ∈ 2..d` and reads the leading factoradic digit. The digit
  is `0 / d! = 0` and the remainder is `0`. The emitter still builds `d!`
  and multiplies it by that digit; the product is zero, so the factorial
  value is needed only to know the call succeeds.

  Not a positive rank. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.PackOri

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem fits13 : FitsLen 13 := by
  unfold FitsLen i64MaxNat
  decide

private theorem thirteen_lt_limb : 13 < limbBase := by
  unfold limbBase
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

/-- `12!` fits in one limb. `13!` does not (`6_227_020_800 > 10^9`). -/
private theorem factorial_12_lt_limb : factorial 12 < limbBase := by
  unfold factorial limbBase
  decide

private theorem factorial_one_limb (n : Nat) (hn : n ≤ 12) : factorial n < limbBase :=
  Nat.lt_of_le_of_lt (factorial_mono n 12 hn) factorial_12_lt_limb

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    have : (k + 1) - 1 = k := by omega
    rw [this, factorial_succ, Nat.mul_comm]

/-! ## `big_factorial` -/

/-- One step of `big_factorial`'s `for i = 2 to n` loop. -/
def factStep (toV : Int) (σ : Int × Megadreifach.BigInt) :
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

private theorem factStep_gt (toV i : Int) (r : Megadreifach.BigInt) (h : i > toV) :
    factStep toV (i, r) = .ok (SudoRt.Flow.brk (i, r)) := by
  unfold factStep
  rw [if_pos h]
  rfl

private theorem factStep_hit (n i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ n) (hn : n ≤ 13) :
    factStep (Int.ofNat n) (Int.ofNat i, bigNat (factorial (i - 1))) =
      if i = n then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (factorial i)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (factorial i))) := by
  unfold factStep
  dsimp
  have hngt : ¬ (i : Int) > (n : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hi0 : i ≠ 0 := by omega
  have hiPos : 0 < i := by omega
  have hilt : i < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hn) thirteen_lt_limb
  have hfits : FitsLen i := FitsLen.of_le fits13 (Nat.le_trans hhi hn)
  have hacc : factorial (i - 1) < limbBase :=
    factorial_one_limb (i - 1) (by omega)
  rw [show (i : Int) = Int.ofNat i from rfl, big_from_int_refines i hfits, ok_bind]
  have hlimbs : limbsOfNat i = [i] := by
    have hq : i / limbBase = 0 := Nat.div_eq_of_lt hilt
    simp [limbsOfNat, hi0, hq, Nat.mod_eq_of_lt hilt]
  rw [hlimbs, ← bigNat_limb i hilt hi0]
  rw [big_mul_acc (factorial (i - 1)) i hiPos hilt hacc]
  rw [factorial_pred_mul i hiPos, ok_bind, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : i = n
  · have hbeq : ((i : Int) == (n : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (i : Int) ≠ (n : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == (n : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((i : Int) == (n : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one i (FitsLen.of_le fits13 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- `big_factorial n = n!` while `n ≤ 13` (one-limb accumulator, last step may carry). -/
theorem big_factorial_refines (n : Nat) (hn : n ≤ 13) :
    Megadreifach.big_factorial (n : Int) = .ok (bigNat (factorial n)) := by
  unfold Megadreifach.big_factorial
  rw [show (1 : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
  have h1lt : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hlimbs1 : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1lt
    have hm : 1 % limbBase = 1 := Nat.mod_eq_of_lt h1lt
    simp [limbsOfNat, hq, hm]
  rw [hlimbs1, ← bigNat_limb 1 (by unfold limbBase; decide) (by decide)]
  dsimp
  by_cases hn1 : n ≤ 1
  · have hgt : (2 : Int) > (n : Int) := by
      have hle : (n : Int) ≤ 1 := Int.ofNat_le.mpr hn1
      omega
    have hf : factorial n = 1 := by
      cases n with
      | zero => rfl
      | succ n =>
        have : n = 0 := by omega
        subst this
        simp [factorial]
    rw [hf, fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := factStep (n : Int))
      intro σ
      unfold factStep
      dsimp
      rfl
    rw [asc_break (2 : Int) (n : Int) (bigNat 1) _ _ _ hgt
        (factStep_gt (n : Int) 2 (bigNat 1) hgt), pure_eq_ok]
  · have hn2 : 2 ≤ n := by omega
    rw [fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := factStep (n : Int))
      intro σ
      unfold factStep
      dsimp
      rfl
    rw [show (2 : Int) = Int.ofNat 2 from rfl]
    have hf2 : factorial (2 - 1) = 1 := by simp [factorial]
    rw [← hf2]
    apply chain_loop
      (f := fun i => bigNat (factorial (i - 1)))
      (fromN := 2) (toN := n)
      (hle := hn2)
      (goal := .ok (bigNat (factorial n)))
    · intro i hlo hhi
      have hs := factStep_hit n i hlo hhi hn
      have hsub : (i + 1) - 1 = i := by omega
      simpa [hsub] using hs
    · have hsub : (n + 1) - 1 = n := by omega
      rw [hsub, pure_eq_ok]

/-! ## Empty-limb helpers used by a zero peel -/

/-- `big_divmod_small` of the zero bigint by a positive one-limb divisor. -/
theorem divmod_zero (d : Nat) (hd0 : 0 < d) (hd : d < limbBase) :
    Megadreifach.big_divmod_small (bigOf []) (Int.ofNat d) =
      .ok (bigOf [], (0 : Int)) := by
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hgt : decide ((d : Int) > (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact (ofNat_pos_iff d).mpr hd0
  have hlt : decide ((d : Int) < Megadreifach.limb_base) = true := by
    rw [limb_base_eq, decide_eq_true_eq]
    exact (ofNat_lt_iff d limbBase).mpr hd
  rw [hgt]
  simp only [ite_true, hlt]
  rw [show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([] : List Nat).length = 0 from rfl, sEq_ofNat_zero,
    show decide ((0 : Nat) = 0) = true from rfl, if_pos rfl, big_zero_spec]
  rfl

/-- `limb_to_small` of the zero bigint is `0` (the limb loop does not run). -/
theorem limb_to_small_zero :
    Megadreifach.limb_to_small (bigOf []) = .ok (0 : Int) := by
  unfold Megadreifach.limb_to_small
  dsimp [bigOf]
  rw [listLen_embed, List.length_nil, show Int.ofNat 0 = (0 : Int) from rfl,
    subI_zero_one, ok_bind]
  dsimp
  have hgt : (0 : Int) > (-1 : Int) := by decide
  rw [except_bind_pure, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, if_pos hgt]
  simp only [toPure_eq_ok, match_ok_brk, pure_eq_ok]

/-- `mag_sub` of two empty limb lists is empty. -/
theorem mag_sub_zeros :
    Megadreifach.mag_sub (embed []) (embed []) = .ok (embed []) := by
  unfold Megadreifach.mag_sub
  rw [listLen_embed, List.length_nil, show Int.ofNat 0 = (0 : Int) from rfl,
    subI_zero_one, ok_bind]
  dsimp
  have hgt : (0 : Int) > (-1 : Int) := by decide
  rw [except_bind_pure, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, if_pos hgt]
  simp only [toPure_eq_ok, match_ok_brk]
  rw [show (#[] : Array Int) = embed [] from embed_nil.symm,
    trim_embed [] FitsLen.zero, ok_bind]
  simp [dropTrail]

/-! ## `peel_leading` of zero -/

/-- One divisor step of `peel_leading`. The continuation state is the quotient. -/
def peelDivStep (toV : Int) (σ : Int × Megadreifach.BigInt) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × Megadreifach.BigInt) (Megadreifach.BigInt × Int)) :=
  let f := σ.1
  let q := σ.2
  do
    if f > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (f, q))
    else
      match ← ((do
        let t ← Megadreifach.big_divmod_small q f
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) t.1)) :
          Except SudoRt.Trap (SudoRt.Flow _ (Megadreifach.BigInt × Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt × Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (f, fs))
      | .cont fs => do
          if f == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (f, fs))
          else do
            let i' ← SudoRt.addI f (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (i', fs))

private theorem peelDivStep_gt (toV f : Int) (q : Megadreifach.BigInt) (h : f > toV) :
    peelDivStep toV (f, q) = .ok (SudoRt.Flow.brk (f, q)) := by
  unfold peelDivStep
  rw [if_pos h]
  rfl

private theorem peelDivStep_hit (d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d) (hd : d ≤ 13) :
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
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) thirteen_lt_limb
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits13 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- Finish of `peel_leading` once the quotient is still zero. -/
private theorem peel_after_zero (d : Nat) (hd : d ≤ 13) :
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
  rw [limb_to_small_zero, ok_bind, big_factorial_refines d hd, ok_bind,
    show (0 : Int) = Int.ofNat 0 from rfl, big_from_int_refines 0 FitsLen.zero, ok_bind]
  have hlimbs : limbsOfNat 0 = [] := by simp [limbsOfNat]
  rw [hlimbs, big_mul_zero_left, ok_bind]
  dsimp [bigOf]
  rw [mag_sub_zeros, ok_bind, make_big_false [] FitsLen.zero, ok_bind, pure_eq_ok]
  simp [dropTrail, bigNat_zero]

/-- `peel_leading 0 d = (0, 0)` for `d ≤ 13`. The pair is `(remainder, digit)`. -/
theorem peel_leading_zero (d : Nat) (hd : d ≤ 13) :
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
      exact peelDivStep_hit d i hlo hhi hd
    · exact peel_after_zero d hd
  · have hlt : d < 2 := by omega
    have hgt : (2 : Int) > (d : Int) := by
      have : (d : Int) < 2 := (ofNat_lt_iff d 2).mpr hlt
      omega
    rw [asc_break (2 : Int) (d : Int) (bigOf []) _ _ _ hgt
        (peelDivStep_gt (d : Int) 2 (bigOf []) hgt)]
    exact peel_after_zero d hd

/-- Same zero peel, written as the factoradic digit `0 / d!` and remainder `0 % d!`. -/
theorem peel_leading_zero_digit (d : Nat) (hd : d ≤ 13) :
    Megadreifach.peel_leading (bigNat 0) (d : Int) =
      .ok (bigNat (0 % factorial d), ((0 / factorial d : Nat) : Int)) := by
  have hdiv : 0 / factorial d = 0 := Nat.div_eq_of_lt (factorial_pos d)
  have hmod : 0 % factorial d = 0 := Nat.mod_eq_of_lt (factorial_pos d)
  rw [hdiv, hmod]
  exact peel_leading_zero d hd

end MegaDreifach.Link2
