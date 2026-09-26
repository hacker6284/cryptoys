/-
  LINK 2. `peel_leading` of a rank strictly below `d!` for `d ≤ 26`.

  The factoradic digit is `n / d! = 0` and the remainder is `n`. The rank
  may be positive. For `13 ≤ d` a value `10^9 ≤ n < d!` is two limbs; for
  `20 ≤ d` a value `10^18 ≤ n < d!` is three limbs (`26! < 10^27`). The
  division loop is `divmod_cube` on each prefix quotient `n / k!`. The
  closing multiply is the zero coefficient, which short-circuits, and
  `mag_sub` copies the rank off the empty product.

  Not `d!` itself (digit `1`). Not an arbitrary rank `n ≥ d!`. Not a
  positive digit. Not `27!`. Not `51!`. Not `phi_chunk`. Not `phi_inv`.
  Not `v_Hash`.
-/
import MegaDreifach.Link2.PeelCube
import MegaDreifach.Link2.PeelZeroThree

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  rfl

private theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

private theorem len_embed_nil :
    SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by
  rw [listLen_embed]; rfl

private theorem len_embed_one (x : Nat) :
    SudoRt.listLen (embed [x]) = (1 : Int) := by
  rw [listLen_embed]; rfl

private theorem len_embed_two (x y : Nat) :
    SudoRt.listLen (embed [x, y]) = (2 : Int) := by
  rw [listLen_embed]; rfl

private theorem len_embed_three (x y z : Nat) :
    SudoRt.listLen (embed [x, y, z]) = (3 : Int) := by
  rw [listLen_embed]; rfl

private theorem append_dig (out : List Nat) (k : Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat k)).1 = embed (out ++ [k]) := by
  rw [appendL_spec]
  exact push_embed out k

private theorem not_neg_ofNat (k : Nat) :
    decide (Int.ofNat k < Int.ofNat 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

private theorem not_neg (k : Nat) : decide (Int.ofNat k < 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

private theorem idx_lt_zero (i : Nat) : decide (Int.ofNat i < 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

/-! ## `mag_sub` of a value below `10^27` minus zero -/

private theorem magSubZ_one (x : Nat) (hx : x < limbBase) :
    magSubStep (embed [x]) (embed []) 0 ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.brk ((0 : Int), ((0 : Int), embed [x]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [x] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat x 0 (fits_of_lt_limb hx) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_nil]
  rw [idx_lt_zero 0, not_neg_ofNat x]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (#[] : Array Int) = embed [] from embed_nil.symm, append_dig [] x,
    bind_pure_flow]
  simp [List.nil_append, pure_eq_ok]

private theorem mag_sub_one (x : Nat) (hx0 : x ≠ 0) (hx : x < limbBase) :
    Megadreifach.mag_sub (embed [x]) (embed ([] : List Nat)) =
      .ok (embed [x]) := by
  unfold Megadreifach.mag_sub
  rw [len_embed_one x, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := magSubStep (embed [x]) (embed []) 0)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, magSubZ_one x hx]
  simp only [match_ok_brk]
  have hdrop : dropTrail [x] = [x] := by simp [dropTrail, hx0]
  rw [trim_embed [x] FitsLen.one, ok_bind, hdrop, pure_eq_ok]

private theorem magSubZ2_0 (lo hi : Nat) (hlo : lo < limbBase) :
    magSubStep (embed [lo, hi]) (embed []) 1
        ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.cont ((1 : Int), ((0 : Int), embed [lo]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [lo, hi] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat lo 0 (fits_of_lt_limb hlo) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_nil]
  rw [idx_lt_zero 0, not_neg_ofNat lo]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (#[] : Array Int) = embed [] from embed_nil.symm, append_dig [] lo,
    bind_pure_flow]
  simp only [List.nil_append]
  dsimp
  rw [addI_zero_one, ok_bind, pure_eq_ok]

private theorem magSubZ2_1 (lo hi : Nat) (hhi : hi < limbBase) :
    magSubStep (embed [lo, hi]) (embed []) 1
        ((1 : Int), ((0 : Int), embed [lo])) =
      .ok (SudoRt.Flow.brk ((1 : Int), ((0 : Int), embed [lo, hi]))) := by
  unfold magSubStep
  dsimp
  rw [show (1 : Int) = Int.ofNat 1 from rfl, atL_embed [lo, hi] 1 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat hi 0 (fits_of_lt_limb hhi) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_nil]
  rw [idx_lt_zero 1, not_neg hi]
  simp only [Bool.false_eq_true, ite_false]
  rw [append_dig [lo] hi, bind_pure_flow]
  dsimp
  rw [pure_eq_ok]

private theorem mag_sub_two (lo hi : Nat) (hlo : lo < limbBase) (hhi : hi < limbBase)
    (hhi0 : hi ≠ 0) :
    Megadreifach.mag_sub (embed [lo, hi]) (embed ([] : List Nat)) =
      .ok (embed [lo, hi]) := by
  unfold Megadreifach.mag_sub
  rw [len_embed_two lo hi, subI_two_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := magSubStep (embed [lo, hi]) (embed []) 1)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ, magSubZ2_0 lo hi hlo]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, magSubZ2_1 lo hi hhi]
  simp only [match_ok_brk]
  have hlen : ([lo, hi] : List Nat).length ≤ 3 := by simp
  have hdrop : dropTrail [lo, hi] = [lo, hi] := by simp [dropTrail, hhi0]
  rw [trim_embed [lo, hi] (fits_le3 hlen), ok_bind, hdrop, pure_eq_ok]

private theorem magSubZ3_0 (a b c : Nat) (ha : a < limbBase) :
    magSubStep (embed [a, b, c]) (embed []) 2
        ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.cont ((1 : Int), ((0 : Int), embed [a]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [a, b, c] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat a 0 (fits_of_lt_limb ha) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_nil]
  rw [idx_lt_zero 0, not_neg_ofNat a]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (#[] : Array Int) = embed [] from embed_nil.symm, append_dig [] a,
    bind_pure_flow]
  simp only [List.nil_append]
  dsimp
  rw [addI_zero_one, ok_bind, pure_eq_ok]

private theorem magSubZ3_1 (a b c : Nat) (hb : b < limbBase) :
    magSubStep (embed [a, b, c]) (embed []) 2
        ((1 : Int), ((0 : Int), embed [a])) =
      .ok (SudoRt.Flow.cont ((2 : Int), ((0 : Int), embed [a, b]))) := by
  unfold magSubStep
  dsimp
  rw [show (1 : Int) = Int.ofNat 1 from rfl, atL_embed [a, b, c] 1 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat b 0 (fits_of_lt_limb hb) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_nil]
  rw [idx_lt_zero 1, not_neg b]
  simp only [Bool.false_eq_true, ite_false]
  rw [append_dig [a] b, bind_pure_flow]
  dsimp
  rw [addI_one_one, ok_bind, pure_eq_ok]

private theorem magSubZ3_2 (a b c : Nat) (hc : c < limbBase) :
    magSubStep (embed [a, b, c]) (embed []) 2
        ((2 : Int), ((0 : Int), embed [a, b])) =
      .ok (SudoRt.Flow.brk ((2 : Int), ((0 : Int), embed [a, b, c]))) := by
  unfold magSubStep
  dsimp
  rw [show (2 : Int) = Int.ofNat 2 from rfl, atL_embed [a, b, c] 2 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat c 0 (fits_of_lt_limb hc) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_nil]
  rw [idx_lt_zero 2, not_neg c]
  simp only [Bool.false_eq_true, ite_false]
  rw [append_dig [a, b] c, bind_pure_flow]
  dsimp
  rw [pure_eq_ok]

private theorem mag_sub_three (a b c : Nat) (ha : a < limbBase) (hb : b < limbBase)
    (hc : c < limbBase) (hc0 : c ≠ 0) :
    Megadreifach.mag_sub (embed [a, b, c]) (embed ([] : List Nat)) =
      .ok (embed [a, b, c]) := by
  unfold Megadreifach.mag_sub
  rw [len_embed_three a b c, subI_three_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := magSubStep (embed [a, b, c]) (embed []) 2)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ, magSubZ3_0 a b c ha]
  simp only [match_ok_cont]
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ, magSubZ3_1 a b c hb]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, magSubZ3_2 a b c hc]
  simp only [match_ok_brk]
  have hlen : ([a, b, c] : List Nat).length ≤ 3 := by simp
  rw [trim_embed [a, b, c] (fits_le3 hlen), ok_bind, dropTrail_eq_self_of_high hc0,
    pure_eq_ok]

private theorem limbs_one (n : Nat) (h0 : n ≠ 0) (hlt : n < limbBase) :
    limbsOfNat n = [n] := by
  have hq : n / limbBase = 0 := Nat.div_eq_of_lt hlt
  simp [limbsOfNat, h0, hq, Nat.mod_eq_of_lt hlt]

private theorem limbs_two (n : Nat) (hge : limbBase ≤ n) (hlt : n < limbBase ^ 2) :
    limbsOfNat n = [n % limbBase, n / limbBase] := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le limbBase_pos hge)
  have hq0 : n / limbBase ≠ 0 := by
    intro hz
    exact Nat.not_le_of_gt (lt_of_div_eq_zero limbBase_pos hz) hge
  have hq2 : (n / limbBase) / limbBase = 0 := by
    rw [limbBase_pow2] at hlt
    exact Nat.div_eq_of_lt (div_lt_of_lt_mul limbBase_pos hlt)
  have hmod : (n / limbBase) % limbBase = n / limbBase :=
    Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq2)
  simp [limbsOfNat, hn0, hq0, hq2, hmod]

private theorem limbs_three (n : Nat) (hge : limbBase ^ 2 ≤ n) (_hlt : n < limbBase ^ 3) :
    limbsOfNat n =
      [n % limbBase, (n / limbBase) % limbBase, (n / limbBase) / limbBase] := by
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pow_pos limbBase_pos) hge)
  have hq0 : n / limbBase ≠ 0 := by
    have hle : limbBase ≤ n / limbBase := by
      rw [Nat.le_div_iff_mul_le limbBase_pos, ← limbBase_pow2]
      exact hge
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le limbBase_pos hle)
  have hq1 : (n / limbBase) / limbBase ≠ 0 := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact Nat.ne_of_gt (div_pos_of_le (Nat.pow_pos limbBase_pos) hge)
  simp [limbsOfNat, hn0, hq0, hq1]

/-- Subtracting the empty limb list copies a value below `10^27`. -/
theorem mag_sub_zero_right (n : Nat) (hn : n < limbBase ^ 3) :
    Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs (embed ([] : List Nat)) =
      .ok (embed (limbsOfNat n)) := by
  by_cases h0 : n = 0
  · subst h0
    rw [bigNat_zero]
    dsimp [bigOf]
    simp [limbsOfNat, mag_sub_zeros]
  · by_cases hlt : n < limbBase
    · rw [bigNat_limb n hlt h0, limbs_one n h0 hlt]
      dsimp [bigOf]
      exact mag_sub_one n h0 hlt
    · have hge : limbBase ≤ n := Nat.le_of_not_lt hlt
      by_cases hsq : n < limbBase ^ 2
      · have hlo : n % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hhiLt : n / limbBase < limbBase := by
          rw [limbBase_pow2] at hsq
          exact div_lt_of_lt_mul limbBase_pos hsq
        have hhi0 : n / limbBase ≠ 0 := by
          intro hz
          exact Nat.not_le_of_gt (lt_of_div_eq_zero limbBase_pos hz) hge
        rw [bigNat_two n hge hsq, limbs_two n hge hsq]
        dsimp [bigOf]
        exact mag_sub_two (n % limbBase) (n / limbBase) hlo hhiLt hhi0
      · have hge3 : limbBase ^ 2 ≤ n := Nat.le_of_not_lt hsq
        have hlo : n % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hmid : (n / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hhi : (n / limbBase) / limbBase < limbBase := by
          have hdiv : n / limbBase < limbBase ^ 2 := by
            rw [limbBase_pow3] at hn
            exact div_lt_of_lt_mul limbBase_pos hn
          rw [limbBase_pow2] at hdiv
          exact div_lt_of_lt_mul limbBase_pos hdiv
        have hhi0 : (n / limbBase) / limbBase ≠ 0 := by
          rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
          exact Nat.ne_of_gt (div_pos_of_le (Nat.pow_pos limbBase_pos) hge3)
        rw [bigNat_three n hge3 hn, limbs_three n hge3 hn]
        dsimp [bigOf]
        exact mag_sub_three (n % limbBase) ((n / limbBase) % limbBase)
          ((n / limbBase) / limbBase) hlo hmid hhi hhi0

/-! ## Division loop for `n < d!` -/

private theorem fits27 : FitsLen 27 := by
  unfold FitsLen i64MaxNat
  decide

private theorem twentySix_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

private theorem factorial_12_lt_limb : factorial 12 < limbBase := by
  unfold factorial limbBase
  decide

private theorem factorial_26_lt_cube : factorial 26 < limbBase ^ 3 := by
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

private theorem factorial_lt_limb12 (n : Nat) (hn : n ≤ 12) : factorial n < limbBase :=
  Nat.lt_of_le_of_lt (factorial_mono n 12 hn) factorial_12_lt_limb

private theorem factorial_lt_cube26 (n : Nat) (hn : n ≤ 26) : factorial n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt (factorial_mono n 26 hn) factorial_26_lt_cube

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem div_fact_step (n f : Nat) (hf0 : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf0]

private theorem peelDivStep_gt (toV f : Int) (q : Megadreifach.BigInt) (h : f > toV) :
    peelDivStep toV (f, q) = .ok (SudoRt.Flow.brk (f, q)) := by
  unfold peelDivStep
  rw [if_pos h]
  rfl

private theorem peelDivStep_below (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 26) (hn : n < limbBase ^ 3) :
    peelDivStep (Int.ofNat d)
        (Int.ofNat f, bigNat (n / factorial (f - 1))) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigNat (n / factorial f)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigNat (n / factorial f))) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) twentySix_lt_limb
  have hq : n / factorial (f - 1) < limbBase ^ 3 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [show (f : Int) = Int.ofNat f from rfl,
    divmod_cube (n / factorial (f - 1)) f hq hf0 hflt, ok_bind]
  rw [show ((bigNat ((n / factorial (f - 1)) / f),
        ((((n / factorial (f - 1)) % f : Nat) : Int))).1) =
      bigNat ((n / factorial (f - 1)) / f) from rfl,
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits27 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_finish_below (n d : Nat) (hn : n < limbBase ^ 3) (hd : d ≤ 26) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat 0)
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat n, (0 : Int)) := by
  rw [bigNat_zero, limb_to_small_zero, ok_bind, big_factorial_acc3 d hd, ok_bind,
    show (0 : Int) = Int.ofNat 0 from rfl, big_from_int_refines 0 FitsLen.zero, ok_bind]
  have hlimbs0 : limbsOfNat 0 = [] := by simp [limbsOfNat]
  rw [hlimbs0, big_mul_zero_left, ok_bind]
  dsimp [bigOf]
  rw [mag_sub_zero_right n hn, ok_bind,
    make_big_false (limbsOfNat n) (fits_le3 (limbsOfNat_len n)), ok_bind,
    limbsOfNat_trimmed n hn, pure_eq_ok]
  rfl

private theorem peel_leading_below_wide (n d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 26)
    (hn : n < factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat n, (0 : Int)) := by
  have hn3 : n < limbBase ^ 3 := Nat.lt_trans hn (factorial_lt_cube26 d hd)
  unfold Megadreifach.peel_leading
  dsimp
  rw [fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := peelDivStep (d : Int))
    intro σ
    unfold peelDivStep
    dsimp
    rfl
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  have hdiv1 : n / factorial (2 - 1) = n := by
    have : factorial (2 - 1) = 1 := by simp [factorial]
    rw [this, Nat.div_one]
  have hpair :
      ((Int.ofNat 2, bigNat n) : Int × Megadreifach.BigInt) =
        (Int.ofNat 2, bigNat (n / factorial (2 - 1))) := by
    rw [hdiv1]
  rw [hpair]
  apply chain_loop
    (f := fun i => bigNat (n / factorial (i - 1)))
    (fromN := 2) (toN := d)
    (hle := by omega)
    (goal := .ok (bigNat n, (0 : Int)))
  · intro i hlo hhi
    have hs := peelDivStep_below n d i hlo hhi hd hn3
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · simp only [Prod.snd]
    rw [show (d + 1) - 1 = d from by omega, Nat.div_eq_of_lt hn]
    exact peel_finish_below n d hn3 hd

/--
  `peel_leading (bigNat n) d = (n, 0)` when `n < d!` and `d ≤ 26`.

  The digit is `0 / d!` only in the sense `n / d! = 0`; the remainder is
  `n` itself. For `13 ≤ d` the factorial is at least two limbs, and a
  positive `n` in `10^9 ≤ n < d!` is a positive multi-limb rank that is
  not `d!`. For `20 ≤ d` that rank may be three limbs. The closing
  multiply is the zero coefficient. Not a positive digit. Not `27!`.
  Not `51!`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem peel_leading_below (n d : Nat) (hd : d ≤ 26) (hn : n < factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat n, (0 : Int)) := by
  by_cases hn0 : n = 0
  · subst hn0
    exact peel_leading_zero_three d hd
  · by_cases hd12 : d ≤ 12
    · have hlt : n < limbBase := Nat.lt_trans hn (factorial_lt_limb12 d hd12)
      have h := peel_leading_limb n d hd12 hlt
      have hdiv : n / factorial d = 0 := Nat.div_eq_of_lt hn
      have hmod : n % factorial d = n := Nat.mod_eq_of_lt hn
      simpa [hdiv, hmod] using h
    · exact peel_leading_below_wide n d (by omega) hd hn

/-- Same peel, as the factoradic pair `(n % d!, n / d!)`. -/
theorem peel_leading_below_digit (n d : Nat) (hd : d ≤ 26) (hn : n < factorial d) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  have hdiv : n / factorial d = 0 := Nat.div_eq_of_lt hn
  have hmod : n % factorial d = n := Nat.mod_eq_of_lt hn
  rw [hdiv, hmod]
  exact peel_leading_below n d hd hn

end MegaDreifach.Link2
