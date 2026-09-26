/-
  LINK 2. `peel_leading` for `d ≤ 51` when the factoradic digit is one limb.

  `big_factorial` reaches `51!` and `big_mul_left` multiplies that digit by
  the factorial. The new piece is `mag_sub_nat`: the remainder
  `n - (n / d!) · d!` may have as many limbs as `n`. The domain is
  `n / d! < 10^9`, which is every digit `phi_chunk` emits (`≤ 51`) and
  every wider one-limb digit. `n` itself stays below `10^81`.

  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.MagSub
import MegaDreifach.Link2.Fact51
import MegaDreifach.Link2.MulLeft

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

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

private theorem pow9 (k : Nat) : limbBase * limbBase ^ k = limbBase ^ (k + 1) := by
  rw [Nat.mul_comm, ← Nat.pow_succ]

private theorem n_lt_pow9 (n d : Nat) (hd : d ≤ 51) (hq : n / factorial d < limbBase) :
    n < limbBase ^ 9 := by
  have hf : 0 < factorial d := factorial_pos d
  have hmod : n % factorial d < factorial d := Nat.mod_lt _ hf
  have hsum : factorial d * (n / factorial d) + n % factorial d = n :=
    Nat.div_add_mod n (factorial d)
  have hlt1 : n < factorial d * (n / factorial d + 1) := by
    have hstep : factorial d * (n / factorial d) + n % factorial d <
        factorial d * (n / factorial d) + factorial d := Nat.add_lt_add_left hmod _
    have hright : factorial d * (n / factorial d) + factorial d =
        factorial d * (n / factorial d + 1) := by
      have hmul := Nat.mul_add (factorial d) (n / factorial d) 1
      rw [Nat.mul_one] at hmul
      exact hmul.symm
    have hlt := Nat.lt_of_lt_of_eq hstep hright
    simpa [hsum] using hlt
  have hq1 : n / factorial d + 1 ≤ limbBase := Nat.succ_le_of_lt hq
  have hmul : factorial d * (n / factorial d + 1) ≤ factorial d * limbBase :=
    Nat.mul_le_mul_left _ hq1
  have hbase : n < limbBase * factorial d := by
    have hcomm : factorial d * limbBase = limbBase * factorial d := Nat.mul_comm _ _
    exact Nat.lt_of_lt_of_le hlt1 (by simpa [hcomm] using hmul)
  have hf8 : factorial d < limbBase ^ 8 := factorial_lt_pow8 d hd
  have hmul8 : limbBase * factorial d < limbBase * limbBase ^ 8 :=
    Nat.mul_lt_mul_of_pos_left hf8 limbBase_pos
  rw [pow9] at hmul8
  exact Nat.lt_trans hbase hmul8

private theorem fits_limbs (k : Nat) (hk : k < limbBase ^ 9) :
    FitsLen (natLimbs k).length := by
  exact fits_le9 (natLimbs_length_le k 9 hk)

private theorem fits_fact_mul (d : Nat) (hd : d ≤ 51) :
    FitsLen ((natLimbs (factorial d)).length + 1) := by
  have hlen := natLimbs_length_le (factorial d) 8 (factorial_lt_pow8 d hd)
  exact fits_le9 (by omega)

private theorem limbsOfNat_small (a : Nat) (ha : a < limbBase) :
    limbsOfNat a = natLimbs a := by
  by_cases h0 : a = 0
  · simp [h0, limbsOfNat, natLimbs_zero]
  · rw [natLimbs_of_pos_lt a (Nat.pos_of_ne_zero h0) ha]
    simp [limbsOfNat, h0, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

private theorem bigNat_small (a : Nat) (ha : a < limbBase) :
    bigNat a = bigOf (natLimbs a) := by
  rw [show bigNat a = bigOf (limbsOfNat a) from rfl, limbsOfNat_small a ha]

private theorem prod_le_self (n d : Nat) : (n / d) * d ≤ n :=
  Nat.div_mul_le_self n d

private theorem mod_eq_sub_mul (n d : Nat) (_hd : 0 < d) :
    n % d = n - (n / d) * d := by
  have hsum : (n / d) * d + n % d = n := by
    rw [Nat.mul_comm (n / d) d]
    exact Nat.div_add_mod n d
  have hle : (n / d) * d ≤ n := Nat.div_mul_le_self n d
  have hcancel : (n / d) * d + n % d = (n / d) * d + (n - (n / d) * d) := by
    rw [hsum, Nat.add_sub_of_le hle]
  exact Nat.add_left_cancel hcancel

private theorem div_fact_step (n f : Nat) (hf : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul]
  cases f with
  | zero => cases hf
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem peelDiv_gt (toV f : Int) (q : Megadreifach.BigInt) (h : f > toV) :
    peelDivStep toV (f, q) = .ok (SudoRt.Flow.brk (f, q)) := by
  unfold peelDivStep
  rw [if_pos h]
  rfl

private theorem peelDiv_hit (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d) (hd : d ≤ 51)
    (hn : n < limbBase ^ 9) :
    peelDivStep (Int.ofNat d)
        (Int.ofNat f, bigOf (natLimbs (n / factorial (f - 1)))) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigOf (natLimbs (n / factorial f))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigOf (natLimbs (n / factorial f)))) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) fiftyOne_lt_limb
  have hq : n / factorial (f - 1) < limbBase ^ 9 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [show (f : Int) = Int.ofNat f from rfl,
    big_divmod_nat f (n / factorial (f - 1)) hf0 hflt (fits_limbs _ hq), ok_bind]
  rw [show ((bigOf (natLimbs ((n / factorial (f - 1)) / f)),
        (((n / factorial (f - 1)) % f : Nat) : Int)).1) =
      bigOf (natLimbs ((n / factorial (f - 1)) / f)) from rfl,
    div_fact_step n f hf0, pure_eq_ok, ok_bind]
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits51 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_finish (n d : Nat) (hd : d ≤ 51) (hq : n / factorial d < limbBase)
    (hn : n < limbBase ^ 9) :
    (do
      let idx ← Megadreifach.limb_to_small (bigOf (natLimbs (n / factorial d)))
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub
        (bigOf (natLimbs n)).sudo_6BigInt_5limbs prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigOf (natLimbs (n % factorial d)), Int.ofNat (n / factorial d)) := by
  let q := n / factorial d
  have hbig := bigNat_small q hq
  rw [← hbig, limb_to_small_limb q hq, ok_bind, big_factorial_51 d hd, ok_bind]
  rw [show ((q : Nat) : Int) = Int.ofNat q from rfl,
    big_from_int_refines q (fits_of_lt_limb hq), ok_bind, limbsOfNat_small q hq]
  rw [big_mul_left_nat q (factorial d) hq (fits_fact_mul d hd), ok_bind]
  have hle : q * factorial d ≤ n := prod_le_self n (factorial d)
  have hprod : q * factorial d < limbBase ^ 9 := Nat.lt_of_le_of_lt hle hn
  have hdiff : n - q * factorial d < limbBase ^ 9 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn
  rw [show (bigOf (natLimbs n)).sudo_6BigInt_5limbs = embed (natLimbs n) from rfl,
    show (bigOf (natLimbs (q * factorial d))).sudo_6BigInt_5limbs =
      embed (natLimbs (q * factorial d)) from rfl,
    mag_sub_nat n (q * factorial d) hle (fits_limbs n hn), ok_bind]
  have hfitD : FitsLen (natLimbs (n - q * factorial d)).length := fits_limbs _ hdiff
  rw [make_big_false (natLimbs (n - q * factorial d)) hfitD, dropTrail_natLimbs,
    ← mod_eq_sub_mul n (factorial d) (factorial_pos d), ok_bind, pure_eq_ok]

/--
  `peel_leading (natLimbs n) d = (n % d!, n / d!)` for `d ≤ 51`,
  whenever the digit `n / d!` is one limb.
-/
theorem peel_leading_51 (n d : Nat) (hd : d ≤ 51) (hq : n / factorial d < limbBase) :
    Megadreifach.peel_leading (bigOf (natLimbs n)) (d : Int) =
      .ok (bigOf (natLimbs (n % factorial d)), Int.ofNat (n / factorial d)) := by
  have hn : n < limbBase ^ 9 := n_lt_pow9 n d hd hq
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
    have hdiv1 : n / factorial (2 - 1) = n := by
      have : factorial (2 - 1) = 1 := by simp [factorial]
      rw [this, Nat.div_one]
    have hpair :
        ((Int.ofNat 2, bigOf (natLimbs n)) : Int × Megadreifach.BigInt) =
          (Int.ofNat 2, bigOf (natLimbs (n / factorial (2 - 1)))) := by
      rw [hdiv1]
    rw [hpair]
    apply chain_loop
      (f := fun i => bigOf (natLimbs (n / factorial (i - 1))))
      (fromN := 2) (toN := d)
      (hle := hd2)
      (goal := .ok (bigOf (natLimbs (n % factorial d)), Int.ofNat (n / factorial d)))
    · intro i hlo hhi
      have hs := peelDiv_hit n d i hlo hhi hd hn
      have hsub : (i + 1) - 1 = i := by omega
      simpa [hsub] using hs
    · simp only [Prod.snd]
      rw [show (d + 1) - 1 = d from by omega]
      exact peel_finish n d hd hq hn
  · have hgt : (2 : Int) > (d : Int) := by
      have hlt : d ≤ 1 := by omega
      have : (d : Int) ≤ 1 := Int.ofNat_le.mpr hlt
      omega
    have hfact : factorial d = 1 := by
      cases d with
      | zero => rfl
      | succ k =>
        have : k = 0 := by omega
        subst this
        simp [factorial]
    have hdiv : n / factorial d = n := by rw [hfact, Nat.div_one]
    have hfin := peel_finish n d hd hq hn
    rw [hdiv, hfact] at hfin
    rw [asc_break (2 : Int) (d : Int) (bigOf (natLimbs n)) _ _ _ hgt
        (peelDiv_gt (d : Int) 2 (bigOf (natLimbs n)) hgt)]
    rw [hfact]
    have hone : (n : Int) / ((1 : Nat) : Int) = (n : Int) := by
      have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
      rw [h1, Int.ediv_one]
    rw [hone]
    dsimp
    exact hfin

end MegaDreifach.Link2
