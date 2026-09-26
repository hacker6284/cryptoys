/-
  LINK 2. Three-limb `big_factorial` for `n ≤ 20`.

  `19!` is two limbs (`19! < 10^18`). `20! = 19! · 20` is the first factorial
  with a nonzero third limb (`10^18 ≤ 20! < 10^27`). The schoolbook product
  of a two-limb value by a one-limb factor stays inside an i64 at every
  digit; the third scratch limb is the carry out of the middle digit.

  Not `21!` (that multiplies a three-limb accumulator). Not `51!`.
  Not an arbitrary positive two-limb `peel_leading`. Not `phi_chunk`.
  Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.FactTwo

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

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

private theorem addI_two_one : SudoRt.addI (2 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen (2 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 2 1 h]
  rfl

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem addI_nat_zero (n : Nat) (h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

private theorem addI_zero_nat (n : Nat) (h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

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

private theorem filledL_three :
    SudoRt.filledL (3 : Int) (0 : Int) = .ok (Array.mkArray 3 (0 : Int)) := by
  erw [filledL_ofNat 3 (0 : Int)]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem embed3_set1 (x y z v : Nat) :
    (embed [x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem embed3_set2 (x y z v : Nat) :
    (embed [x, y, z]).set ⟨2, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [x, y, v] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem prod_lt_sq {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    a * b < limbBase ^ 2 := by
  have ha' : a ≤ limbBase - 1 := by omega
  have hb' : b ≤ limbBase - 1 := by omega
  have hmul : a * b ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha' hb'
  have hconst : (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hmul hconst

private theorem prod_fits {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    FitsLen (a * b) := by
  exact Nat.le_trans (Nat.le_of_lt (prod_lt_sq ha hb)) limb_sq_fits

private theorem repr_mul (lo hi r : Nat) :
    (lo + limbBase * hi) * r =
      (lo * r) % limbBase +
        limbBase * ((lo * r) / limbBase + hi * r) := by
  have hlow : lo * r = (lo * r) % limbBase + limbBase * ((lo * r) / limbBase) :=
    (Nat.mod_add_div (lo * r) limbBase).symm
  have hL := congrArg (fun n => n + limbBase * (hi * r)) hlow
  have hA :
      ((lo * r) % limbBase + limbBase * ((lo * r) / limbBase)) + limbBase * (hi * r) =
        (lo * r) % limbBase +
          (limbBase * ((lo * r) / limbBase) + limbBase * (hi * r)) := by
    rw [Nat.add_assoc]
  have hM :
      (lo * r) % limbBase +
          (limbBase * ((lo * r) / limbBase) + limbBase * (hi * r)) =
        (lo * r) % limbBase + limbBase * ((lo * r) / limbBase + hi * r) := by
    rw [← Nat.mul_add]
  rw [Nat.add_mul, Nat.mul_assoc]
  exact (hL.trans hA).trans hM

private theorem div_add_mul (q d : Nat) (hq : q < limbBase) :
    (q + limbBase * d) / limbBase = d := by
  have h := Nat.add_mul_div_right q d limbBase_pos
  rw [Nat.mul_comm d limbBase] at h
  rw [h, Nat.div_eq_of_lt hq, Nat.zero_add]

private theorem mod_add_mul (q d : Nat) (hq : q < limbBase) :
    (q + limbBase * d) % limbBase = q := by
  rw [Nat.add_comm q (limbBase * d), Nat.mul_add_mod, Nat.mod_eq_of_lt hq]

private theorem prod_div_eq (lo hi r : Nat) :
    ((lo + limbBase * hi) * r) / limbBase =
      (lo * r) / limbBase + hi * r := by
  have hq : (lo * r) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hdiv := div_add_mul ((lo * r) % limbBase)
    ((lo * r) / limbBase + hi * r) hq
  have hrepr := repr_mul lo hi r
  rw [← hrepr] at hdiv
  exact hdiv

private theorem prod_mod_eq (lo hi r : Nat) :
    ((lo + limbBase * hi) * r) % limbBase = (lo * r) % limbBase := by
  have hq : (lo * r) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hmod := mod_add_mul ((lo * r) % limbBase)
    ((lo * r) / limbBase + hi * r) hq
  rw [← repr_mul lo hi r] at hmod
  exact hmod

private theorem prod_div_mod (lo hi r : Nat) :
    (((lo + limbBase * hi) * r) / limbBase) % limbBase =
      ((lo * r) / limbBase + hi * r) % limbBase := by
  rw [prod_div_eq]

private theorem prod_div_div (lo hi r : Nat) :
    (((lo + limbBase * hi) * r) / limbBase) / limbBase =
      ((lo * r) / limbBase + hi * r) / limbBase := by
  rw [prod_div_eq]

/-- Canonical three-limb form. `10^18 ≤ v < 10^27`. -/
theorem bigNat_three (v : Nat) (hlo : limbBase ^ 2 ≤ v) (_hhi : v < limbBase ^ 3) :
    bigNat v =
      bigOf [v % limbBase, (v / limbBase) % limbBase, (v / limbBase) / limbBase] := by
  have hv0 : v ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pow_pos limbBase_pos) hlo)
  have hq0 : 0 < v / limbBase := by
    have hle : limbBase ≤ v / limbBase := by
      rw [Nat.le_div_iff_mul_le limbBase_pos, ← limbBase_pow2]
      exact hlo
    exact Nat.lt_of_lt_of_le limbBase_pos hle
  have hq1 : 0 < (v / limbBase) / limbBase := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_pos_of_le (Nat.pow_pos limbBase_pos) hlo
  simp [bigNat, limbsOfNat, hv0, Nat.ne_of_gt hq0, Nat.ne_of_gt hq1]

/-! ## Carry into the third scratch limb -/

/-- Write a positive one-limb carry into scratch slot 2 and stop. -/
private theorem mulKStep_limb2 (d0 d1 c : Nat) (hc0 : 0 < c) (hc : c < limbBase) :
    mulKStep (2 : Int) ((2 : Int), embed [d0, d1, 0], Int.ofNat c) =
      .ok (SudoRt.Flow.brk ((2 : Int), embed [d0, d1, c], (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hdec : decide ((c : Int) > (0 : Int)) = true := by
    rw [show (c : Int) = Int.ofNat c from rfl, decide_ofNat_pos, decide_eq_true_eq]
    exact hc0
  rw [hdec]
  simp only [ite_true]
  have hsz : 2 < (embed [d0, d1, 0]).size := by simp [size_embed]
  have hat : SudoRt.atL (embed [d0, d1, 0]) (2 : Int) = .ok (0 : Int) := by
    erw [atL_embed [d0, d1, 0] 2 (by simp)]
    simp
  rw [hat, ok_bind]
  have hcur : FitsLen c := fits_of_lt_limb hc
  erw [addI_zero_nat c hcur]
  rw [ok_bind]
  erw [modI_nat_base c]
  rw [ok_bind]
  have hmod : c % limbBase = c := Nat.mod_eq_of_lt hc
  have hdiv : c / limbBase = 0 := Nat.div_eq_of_lt hc
  rw [hmod]
  erw [putL_ofNat (embed [d0, d1, 0]) 2 (Int.ofNat c) hsz]
  rw [ok_bind]
  erw [divI_nat_base c]
  rw [ok_bind, hdiv, embed3_set2 d0 d1 0 c]
  simp [pure_eq_ok]

set_option maxHeartbeats 2000000 in
private theorem big_mul_open (lo hi r : Nat) :
    Megadreifach.big_mul (bigOf [lo, hi]) (bigOf [r]) =
      SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((0 : Int), Array.mkArray 3 (0 : Int)) 2
        (mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int))
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by
    rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq2 : SudoRt.SEq.beq (2 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq2]
  dsimp
  rw [hlenb, hbeq1]
  have hnz : ¬ ((false : Bool) = true) := by decide
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind, if_neg hnz]
  rw [addI_two_one, ok_bind, filledL_three, ok_bind, subI_two_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rfl

set_option maxHeartbeats 4000000 in
private theorem mulIStep_high3 (lo hi r : Nat)
    (_hlo : lo < limbBase) (hhi : hi < limbBase) (hr : r < limbBase)
    (hpLo : limbBase ^ 2 ≤ (lo + limbBase * hi) * r)
    (hpHi : (lo + limbBase * hi) * r < limbBase ^ 3) :
    mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int)
        ((1 : Int), embed [lo * r % limbBase, lo * r / limbBase, 0]) =
      .ok (SudoRt.Flow.brk
        ((1 : Int),
          embed [((lo + limbBase * hi) * r) % limbBase,
            (((lo + limbBase * hi) * r) / limbBase) % limbBase,
            (((lo + limbBase * hi) * r) / limbBase) / limbBase])) := by
  have hfitR : FitsLen (hi * r) := prod_fits hhi hr
  have hmid_lt : (lo * r) / limbBase + hi * r < limbBase ^ 2 := by
    rw [← prod_div_eq lo hi r]
    rw [limbBase_pow3] at hpHi
    exact div_lt_of_lt_mul limbBase_pos hpHi
  have hfitM : FitsLen ((lo * r) / limbBase + hi * r) :=
    Nat.le_trans (Nat.le_of_lt hmid_lt) limb_sq_fits
  have hcarry_pos : 0 < ((lo * r) / limbBase + hi * r) / limbBase := by
    rw [← prod_div_eq lo hi r, Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_pos_of_le (Nat.pow_pos limbBase_pos) hpLo
  have hcarry_lt : ((lo * r) / limbBase + hi * r) / limbBase < limbBase := by
    rw [limbBase_pow2] at hmid_lt
    exact div_lt_of_lt_mul limbBase_pos hmid_lt
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  erw [addI_nat_zero 1 FitsLen.one]
  rw [ok_bind]
  erw [atL_embed [lo * r % limbBase, lo * r / limbBase, 0] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, hi] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat hi r hfitR]
  rw [ok_bind]
  erw [addI_ofNat ((lo * r) / limbBase) (hi * r) hfitM]
  rw [ok_bind]
  erw [addI_nat_zero ((lo * r) / limbBase + hi * r) hfitM]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base ((lo * r) / limbBase + hi * r)]
  rw [ok_bind]
  erw [putL_ofNat (embed [lo * r % limbBase, lo * r / limbBase, 0]) 1
    (Int.ofNat (((lo * r) / limbBase + hi * r) % limbBase)) (by simp [size_embed])]
  rw [ok_bind]
  erw [divI_nat_base ((lo * r) / limbBase + hi * r)]
  rw [ok_bind,
    embed3_set1 (lo * r % limbBase) (lo * r / limbBase) 0
      (((lo * r) / limbBase + hi * r) % limbBase)]
  erw [bind_pure_flow]
  dsimp
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen
      (embed [lo * r % limbBase,
        ((lo * r) / limbBase + hi * r) % limbBase, 0]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_one_one, ok_bind, hlenOut, subI_three_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  erw [mulKStep_limb2 (lo * r % limbBase)
    (((lo * r) / limbBase + hi * r) % limbBase)
    (((lo * r) / limbBase + hi * r) / limbBase)
    hcarry_pos hcarry_lt]
  simp only [match_ok_brk, pure_eq_ok]
  rw [← prod_mod_eq lo hi r, ← prod_div_mod lo hi r, ← prod_div_div lo hi r]
  simp [beq_int_iff]

/-- Two-limb × one-limb schoolbook product with a nonzero third limb. -/
theorem big_mul_three_limbs (lo hi r : Nat)
    (hlo : lo < limbBase) (_hhi0 : 0 < hi) (hhi : hi < limbBase)
    (_hr0 : 0 < r) (hr : r < limbBase)
    (hpLo : limbBase ^ 2 ≤ (lo + limbBase * hi) * r)
    (hpHi : (lo + limbBase * hi) * r < limbBase ^ 3) :
    Megadreifach.big_mul (bigOf [lo, hi]) (bigOf [r]) =
      .ok (bigNat ((lo + limbBase * hi) * r)) := by
  rw [big_mul_open lo hi r]
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ, mulIStep_low lo hi r hlo hr]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
    mulIStep_high3 lo hi r hlo hhi hr hpLo hpHi]
  simp only [match_ok_brk, except_bind_pure]
  let p := (lo + limbBase * hi) * r
  have h3 : (p / limbBase) / limbBase ≠ 0 := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact Nat.ne_of_gt (div_pos_of_le (Nat.pow_pos limbBase_pos) hpLo)
  rw [make_big_false [p % limbBase, (p / limbBase) % limbBase, (p / limbBase) / limbBase]
      (by simp [fits_le3]),
    dropTrail_eq_self_of_high h3]
  exact congrArg Except.ok (bigNat_three p hpLo hpHi).symm

/--
  Multiply a two-limb value by a one-limb factor when the product needs a
  third limb: `10^18 ≤ a * r < 10^27`.
-/
theorem big_mul_three (a r : Nat) (hr0 : 0 < r) (hr : r < limbBase)
    (hge : limbBase ≤ a) (hlt : a < limbBase ^ 2)
    (hpLo : limbBase ^ 2 ≤ a * r) (hpHi : a * r < limbBase ^ 3) :
    Megadreifach.big_mul (bigNat a) (bigNat r) = .ok (bigNat (a * r)) := by
  have ha0 : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have ha1lt : a / limbBase < limbBase := by
    rw [limbBase_pow2] at hlt
    exact div_lt_of_lt_mul limbBase_pos hlt
  have ha1 : 0 < a / limbBase := div_pos_of_le limbBase_pos hge
  have hrepr : a % limbBase + limbBase * (a / limbBase) = a :=
    Nat.mod_add_div a limbBase
  rw [bigNat_two a hge hlt, bigNat_limb r hr (Nat.ne_of_gt hr0)]
  have hpLo' : limbBase ^ 2 ≤ (a % limbBase + limbBase * (a / limbBase)) * r := by
    simpa [hrepr] using hpLo
  have hpHi' : (a % limbBase + limbBase * (a / limbBase)) * r < limbBase ^ 3 := by
    simpa [hrepr] using hpHi
  have hmul :=
    big_mul_three_limbs (a % limbBase) (a / limbBase) r ha0 ha1 ha1lt hr0 hr hpLo' hpHi'
  simpa [hrepr] using hmul

/-! ## `big_factorial` through `20!` -/

private theorem fits20 : FitsLen 20 := by
  unfold FitsLen i64MaxNat
  decide

private theorem twenty_lt_limb : 20 < limbBase := by
  unfold limbBase
  decide

private theorem factorial_19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem factorial_19_ge : limbBase ≤ factorial 19 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_ge_sq : limbBase ^ 2 ≤ factorial 20 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_lt_cube : factorial 20 < limbBase ^ 3 := by
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

private theorem factorial_lt_sq (n : Nat) (hn : n ≤ 19) : factorial n < limbBase ^ 2 :=
  Nat.lt_of_le_of_lt (factorial_mono n 19 hn) factorial_19_lt_sq

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem twenty_mul_ge : limbBase ^ 2 ≤ factorial 19 * 20 := by
  rw [factorial_pred_mul 20 (by decide)]
  exact factorial_20_ge_sq

private theorem twenty_mul_lt : factorial 19 * 20 < limbBase ^ 3 := by
  rw [factorial_pred_mul 20 (by decide)]
  exact factorial_20_lt_cube

private theorem factMul_at20 (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 20) :
    Megadreifach.big_mul (bigNat (factorial (i - 1))) (bigNat i) =
      .ok (bigNat (factorial i)) := by
  have hiPos : 0 < i := by omega
  have hilt : i < limbBase := Nat.lt_of_le_of_lt hhi twenty_lt_limb
  by_cases h20 : i = 20
  · subst h20
    have hmul := big_mul_three (factorial 19) 20 (by decide) twenty_lt_limb
      factorial_19_ge factorial_19_lt_sq twenty_mul_ge twenty_mul_lt
    rw [factorial_pred_mul 20 (by decide)] at hmul
    simpa [show (20 - 1) = 19 from by decide] using hmul
  · have hi19 : i ≤ 19 := by omega
    have hacc : factorial (i - 1) < limbBase ^ 2 := factorial_lt_sq (i - 1) (by omega)
    have hp : factorial (i - 1) * i < limbBase ^ 2 := by
      rw [factorial_pred_mul i hiPos]
      exact factorial_lt_sq i hi19
    by_cases hlimb : factorial (i - 1) < limbBase
    · have hmul := big_mul_acc (factorial (i - 1)) i hiPos hilt hlimb
      rw [factorial_pred_mul i hiPos] at hmul
      exact hmul
    · have hge : limbBase ≤ factorial (i - 1) := Nat.le_of_not_lt hlimb
      have hmul := big_mul_two (factorial (i - 1)) i hiPos hilt hge hacc hp
      rw [factorial_pred_mul i hiPos] at hmul
      exact hmul

private theorem factStep_at20 (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 20) :
    factStep (20 : Int) (Int.ofNat i, bigNat (factorial (i - 1))) =
      if i = 20 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (factorial i)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (factorial i))) := by
  unfold factStep
  dsimp
  have hngt : ¬ (i : Int) > (20 : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hi0 : i ≠ 0 := by omega
  have hilt : i < limbBase := Nat.lt_of_le_of_lt hhi twenty_lt_limb
  have hfits : FitsLen i := FitsLen.of_le fits20 hhi
  rw [show (i : Int) = Int.ofNat i from rfl, big_from_int_refines i hfits, ok_bind]
  have hlimbs : limbsOfNat i = [i] := by
    have hq : i / limbBase = 0 := Nat.div_eq_of_lt hilt
    simp [limbsOfNat, hi0, hq, Nat.mod_eq_of_lt hilt]
  rw [hlimbs, ← bigNat_limb i hilt hi0, factMul_at20 i hlo hhi, ok_bind, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : i = 20
  · have hbeq : ((i : Int) == (20 : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (i : Int) ≠ (20 : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == (20 : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((i : Int) == (20 : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one i (FitsLen.of_le fits20 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem big_factorial_20 :
    Megadreifach.big_factorial (20 : Int) = .ok (bigNat (factorial 20)) := by
  unfold Megadreifach.big_factorial
  rw [show (1 : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
  have h1lt : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hlimbs1 : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1lt
    have hm : 1 % limbBase = 1 := Nat.mod_eq_of_lt h1lt
    simp [limbsOfNat, hq, hm]
  rw [hlimbs1, ← bigNat_limb 1 (by unfold limbBase; decide) (by decide)]
  dsimp
  have hfuel : (19 : Nat) = fuelRange (2 : Int) (20 : Int) := by
    unfold fuelRange
    decide
  rw [hfuel, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := factStep (20 : Int))
    intro σ
    unfold factStep
    dsimp
    rfl
  rw [show (2 : Int) = Int.ofNat 2 from rfl]
  have hf2 : factorial (2 - 1) = 1 := by simp [factorial]
  rw [← hf2]
  apply chain_loop
    (f := fun i => bigNat (factorial (i - 1)))
    (fromN := 2) (toN := 20)
    (hle := by decide)
    (goal := .ok (bigNat (factorial 20)))
  · intro i hlo hhi
    have hs := factStep_at20 i hlo hhi
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · have hsub : (20 + 1) - 1 = 20 := by omega
    rw [hsub, pure_eq_ok]

/--
  `big_factorial n = n!` for `n ≤ 20`.

  `12!` is one limb. `13!` through `19!` are two limbs (`19! < 10^18`).
  `20! = 19! · 20` is three limbs (`10^18 ≤ 20! < 10^27`); that step is
  `big_mul_three`. Not `21!`. Not `51!`. Not `phi_chunk`. Not `v_Hash`.
-/
theorem big_factorial_three (n : Nat) (hn : n ≤ 20) :
    Megadreifach.big_factorial (n : Int) = .ok (bigNat (factorial n)) := by
  by_cases h19 : n ≤ 19
  · exact big_factorial_two n h19
  · have hn20 : n = 20 := by omega
    subst hn20
    exact big_factorial_20

end MegaDreifach.Link2
