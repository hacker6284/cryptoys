/-
  LINK 2. `peel_leading` on a one-limb rank.

  Domain: `d ≤ 12` and `n < 10^9`. Then `d!` is one limb (`12! < 10^9`,
  `13!` is not), and every quotient `n / k!` for `k ≤ d` is one limb too.
  Each `big_divmod_small` is a single base-10^9 digit divided by `f ∈ 2..d`.
  The factoradic digit `n / d!` may be positive (`d! ≤ n`); the product
  `(n / d!) * d!` stays below one limb, so the closing subtract does not
  borrow. `peel_leading (bigNat (d!)) d` is the positive corner `(0, 1)`.

  Not `d ≥ 13` (a positive digit times a two-limb factorial). Not `51!`.
  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.Factorial

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

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem fits13 : FitsLen 13 := by
  unfold FitsLen i64MaxNat
  decide

private theorem twelve_lt_limb : 12 < limbBase := by
  unfold limbBase
  decide

private theorem fits_limbBase : FitsLen limbBase := by
  unfold FitsLen i64MaxNat limbBase
  decide

private theorem div_lt_limb {n k : Nat} (hn : n < limbBase) : n / k < limbBase :=
  Nat.lt_of_le_of_lt (Nat.div_le_self n k) hn

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

/-- `(n / (f-1)!) / f = n / f!`. -/
private theorem div_fact_step (n f : Nat) (hf : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf]

/-- `n - (n / m) * m = n % m`. -/
private theorem sub_mul_mod (n m : Nat) : n - (n / m) * m = n % m := by
  have h := (Nat.div_add_mod n m).symm
  rw [Nat.mul_comm m (n / m), Nat.add_comm] at h
  exact Nat.sub_eq_of_eq_add h

private theorem limbs_canon (v : Nat) (hv : v < limbBase) :
    dropTrail (limbsOfNat v) = limbsOfNat v := by
  by_cases h0 : v = 0
  · simp [h0, limbsOfNat, dropTrail]
  · have hq : v / limbBase = 0 := Nat.div_eq_of_lt hv
    have hm : v % limbBase = v := Nat.mod_eq_of_lt hv
    simp [limbsOfNat, dropTrail, h0, hq, hm]

private theorem make_big_canon (v : Nat) (hv : v < limbBase) :
    Megadreifach.make_big false (embed (limbsOfNat v)) = .ok (bigNat v) := by
  have hfits : FitsLen (limbsOfNat v).length := fits_le3 (limbsOfNat_len v)
  rw [make_big_false (limbsOfNat v) hfits, limbs_canon v hv]
  rfl

private theorem append_nil (k : Nat) :
    (SudoRt.appendL (#[] : Array Int) (Int.ofNat k)).1 = embed [k] := by
  simp [appendL_spec, embed]

/-! ## One-limb `big_divmod_small` -/

/-- Descending division step. `dv` is the one-limb divisor. -/
def divmodByStep (dv : Int) (limbs : Array Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Array Int × Int)) (Megadreifach.BigInt × Int)) :=
  if σ.1 < 0 then
    pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, σ.2.1, σ.2.2))
  else do
    let lift ←
      ((do
        let x ← SudoRt.mulI σ.2.2 Megadreifach.limb_base
        let dig ← SudoRt.atL limbs σ.1
        let cur ← SudoRt.addI x dig
        let qv ← SudoRt.divI cur dv
        let q ← SudoRt.putL σ.2.1 σ.1 qv
        let r ← SudoRt.modI cur dv
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (q, r))) :
        Except SudoRt.Trap
          (SudoRt.Flow (Array Int × Int) (Megadreifach.BigInt × Int)))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt × Int) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == 0) = true then
        pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
      else do
        let i' ← SudoRt.subI σ.1 1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (i', fs))

private theorem divmod_pos (a d : Nat) (ha : a < limbBase) (_hne : a ≠ 0)
    (hd0 : 0 < d) (hd : d < limbBase) :
    Megadreifach.big_divmod_small (bigOf [a]) (d : Int) =
      .ok (bigNat (a / d), ((a % d : Nat) : Int)) := by
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
    show ([a] : List Nat).length = 1 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (1 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 1 (by decide) FitsLen.one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := divmodByStep (d : Int) (embed [a]))
    intro σ
    unfold divmodByStep
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  have hsz : 0 < (Array.mkArray 1 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]
    decide
  have hstep :
      divmodByStep (d : Int) (embed [a])
          (Int.ofNat 0, Array.mkArray 1 (Int.ofNat 0), Int.ofNat 0) =
        .ok (SudoRt.Flow.brk (Int.ofNat 0,
          (Array.mkArray 1 (Int.ofNat 0)).set ⟨0, hsz⟩ (Int.ofNat (a / d)),
          Int.ofNat (a % d))) := by
    unfold divmodByStep
    dsimp
    rw [limb_base_eq, ← ofNat_eq_natCast limbBase,
      show (0 : Int) = Int.ofNat 0 from rfl,
      mulI_ofNat 0 limbBase (rem_limb_fits 0 (by decide)), ok_bind]
    have hidx : 0 < ([a] : List Nat).length := by
      rw [List.length_cons, List.length_nil]
      decide
    rw [atL_embed [a] 0 hidx, ok_bind]
    have hhead : ([a] : List Nat)[0]'hidx = a := rfl
    have hcur : FitsLen (0 * limbBase + a) := limb_mul_fits 0 a (by decide) ha
    rw [hhead, addI_ofNat (0 * limbBase) a hcur, ok_bind]
    rw [show (d : Int) = Int.ofNat d from rfl,
      divI_ofNat (0 * limbBase + a) (Nat.ne_of_gt hd0), ok_bind]
    rw [putL_ofNat (Array.mkArray 1 (Int.ofNat 0)) 0 _ hsz, ok_bind,
      modI_ofNat (0 * limbBase + a) (Nat.ne_of_gt hd0), ok_bind]
    simp [Nat.zero_mul, Nat.zero_add]
    rfl
  have hmk : Array.mkArray (0 + 1) (Int.ofNat 0) = Array.mkArray 1 (Int.ofNat 0) := by
    simp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, hmk, hstep]
  dsimp
  erw [embed_set1 (a / d)]
  rw [make_big_false [a / d] (by
    rw [show ([a / d] : List Nat).length = 1 from rfl]
    exact FitsLen.one), ok_bind,
    drop_singleton_limbs (a / d) (div_lt_limb ha)]
  simp [bigNat]
  exact pure_eq_ok _

/-- `big_divmod_small` of a one-limb value by a positive one-limb divisor. -/
theorem divmod_limb (a d : Nat) (ha : a < limbBase) (hd0 : 0 < d) (hd : d < limbBase) :
    Megadreifach.big_divmod_small (bigNat a) (d : Int) =
      .ok (bigNat (a / d), ((a % d : Nat) : Int)) := by
  by_cases ha0 : a = 0
  · rw [ha0, bigNat_zero, show (d : Int) = Int.ofNat d from rfl, divmod_zero d hd0 hd]
    have hdiv : 0 / d = 0 := Nat.div_eq_of_lt hd0
    have hmod : 0 % d = 0 := Nat.mod_eq_of_lt hd0
    simp [hdiv, hmod, bigNat_zero]
  · rw [bigNat_limb a ha ha0]
    exact divmod_pos a d ha ha0 hd0 hd

/-! ## One-limb `limb_to_small` -/

def limbStep (limbs : Array Int) (toV : Int) (σ : Int × (Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Int × Int)) Int) :=
  let i := σ.1
  let acc := σ.2.1
  let place := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Int) (i, acc, place))
    else
      match ← ((do
        let dig ← SudoRt.atL limbs i
        let prod ← SudoRt.mulI dig place
        let acc ← SudoRt.addI acc prod
        let place ← SudoRt.mulI place Megadreifach.limb_base
        pure (SudoRt.Flow.cont (ρ := Int) (acc, place))) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Int) Int)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Int) (i', fs))

private theorem limb_to_small_pos (a : Nat) (ha : a < limbBase) (_hne : a ≠ 0) :
    Megadreifach.limb_to_small (bigOf [a]) = .ok (a : Int) := by
  unfold Megadreifach.limb_to_small
  dsimp [bigOf]
  rw [listLen_embed, show ([a] : List Nat).length = 1 from rfl,
    subI_ofNat_one 1 (by decide) FitsLen.one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := limbStep (embed [a]) 0)
    intro σ
    unfold limbStep
    dsimp
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  have hidx : 0 < ([a] : List Nat).length := by
    rw [List.length_cons, List.length_nil]
    decide
  have hmul : FitsLen (a * 1) := by
    rw [Nat.mul_one]
    exact fits_of_lt_limb ha
  have hadd : FitsLen (0 + a * 1) := by
    rw [Nat.zero_add, Nat.mul_one]
    exact fits_of_lt_limb ha
  have hplace : FitsLen (1 * limbBase) := by
    rw [Nat.one_mul]
    exact fits_limbBase
  have hstep :
      limbStep (embed [a]) 0 ((0 : Int), ((0 : Int), (1 : Int))) =
        .ok (SudoRt.Flow.brk ((0 : Int),
          ((a : Int), (Int.ofNat (1 * limbBase))))) := by
    unfold limbStep
    dsimp
    rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [a] 0 hidx, ok_bind]
    simp only [List.getElem_cons_zero]
    rw [show (1 : Int) = Int.ofNat 1 from rfl, mulI_ofNat a 1 hmul, ok_bind,
      addI_ofNat 0 (a * 1) hadd, ok_bind,
      limb_base_eq, ← ofNat_eq_natCast limbBase, mulI_ofNat 1 limbBase hplace, ok_bind,
      bind_pure_flow]
    simp [Nat.mul_one, Nat.zero_add, Nat.one_mul, pure_eq_ok]
  rw [hstep]
  simp [toPure_eq_ok, match_ok_brk, Nat.one_mul]

/-- `limb_to_small` of a one-limb bigint is the limb. -/
theorem limb_to_small_limb (a : Nat) (ha : a < limbBase) :
    Megadreifach.limb_to_small (bigNat a) = .ok (a : Int) := by
  by_cases ha0 : a = 0
  · simp [ha0, bigNat_zero, limb_to_small_zero]
  · rw [bigNat_limb a ha ha0]
    exact limb_to_small_pos a ha ha0

/-! ## One-limb `mag_sub` (no borrow) -/

def magSubStep (a b : Array Int) (toV : Int) (σ : Int × (Int × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Int × Array Int)) (Array Int)) :=
  let i := σ.1
  let borrow := σ.2.1
  let out := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, borrow, out))
    else
      match ← ((do
        let av ← SudoRt.atL a i
        let cur ← SudoRt.subI av borrow
        if decide (i < SudoRt.listLen b) then do
          let bv ← SudoRt.atL b i
          let cur ← SudoRt.subI cur bv
          if decide (cur < (0 : Int)) then do
            let cur ← SudoRt.addI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
          else do
            let out := (SudoRt.appendL out cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))
        else do
          if decide (cur < (0 : Int)) then do
            let cur ← SudoRt.addI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
          else do
            let out := (SudoRt.appendL out cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

private theorem len_embed_one (x : Nat) :
    SudoRt.listLen (embed [x]) = (1 : Int) := by
  rw [listLen_embed]; rfl

private theorem len_embed_nil :
    SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by
  rw [listLen_embed]; rfl

private theorem magSub_empty (x : Nat) (_hx0 : 0 < x) (hx : x < limbBase) :
    magSubStep (embed [x]) (embed []) 0 ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.brk ((0 : Int), ((0 : Int), embed [x]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [x] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat x 0 (fits_of_lt_limb hx) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_nil]
  have hlt : decide (Int.ofNat 0 < 0) = false := by decide
  have hnn : decide (Int.ofNat x < Int.ofNat 0) = false := by
    rw [decide_eq_false_iff_not]
    exact Int.not_lt.mpr (Int.ofNat_zero_le _)
  rw [hlt, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [append_nil x, bind_pure_flow]
  simp [pure_eq_ok]

private theorem magSub_le (x y : Nat) (hx : x < limbBase) (hle : y ≤ x) :
    magSubStep (embed [x]) (embed [y]) 0 ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.brk ((0 : Int), ((0 : Int), embed [x - y]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [x] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat x 0 (fits_of_lt_limb hx) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_one y]
  have hlt : decide (Int.ofNat 0 < 1) = true := by decide
  have hnn : decide (Int.ofNat (x - y) < Int.ofNat 0) = false := by
    rw [decide_eq_false_iff_not]
    exact Int.not_lt.mpr (Int.ofNat_zero_le _)
  rw [hlt]
  simp only [ite_true]
  rw [atL_embed [y] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat x y (fits_of_lt_limb hx) hle, ok_bind, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [append_nil (x - y), bind_pure_flow]
  simp [pure_eq_ok]

private theorem mag_sub_of_step (a b : Array Int) (out : List Nat)
    (hlen : SudoRt.listLen a = (1 : Int))
    (hstep :
      magSubStep a b 0 ((0 : Int), ((0 : Int), (#[] : Array Int))) =
        .ok (SudoRt.Flow.brk ((0 : Int), ((0 : Int), embed out))))
    (htrim : Megadreifach.trim (embed out) = .ok (embed (dropTrail out))) :
    Megadreifach.mag_sub a b = .ok (embed (dropTrail out)) := by
  unfold Megadreifach.mag_sub
  dsimp
  rw [hlen, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := magSubStep a b 0)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, hstep]
  simp [toPure_eq_ok, match_ok_brk, htrim, pure_eq_ok]

/-- `mag_sub` of two one-limb values, subtrahend at most the minuend. -/
private theorem mag_sub_limb (x y : Nat) (hx : x < limbBase) (hle : y ≤ x) :
    Megadreifach.mag_sub (bigNat x).sudo_6BigInt_5limbs (bigNat y).sudo_6BigInt_5limbs =
      .ok (embed (limbsOfNat (x - y))) := by
  by_cases hx0 : x = 0
  · have hy0 : y = 0 := Nat.eq_zero_of_le_zero (by simpa [hx0] using hle)
    subst hx0 hy0
    rw [bigNat_zero]
    simp [bigOf, limbsOfNat, Nat.sub_self, mag_sub_zeros]
  · have hx0' : 0 < x := Nat.pos_of_ne_zero hx0
    rw [bigNat_limb x hx hx0]
    dsimp [bigOf]
    by_cases hy0 : y = 0
    · subst hy0
      rw [bigNat_zero, Nat.sub_zero]
      dsimp [bigOf]
      have hdrop : dropTrail [x] = limbsOfNat x := drop_singleton_limbs x hx
      have h := mag_sub_of_step (embed [x]) (embed ([] : List Nat)) [x]
        (len_embed_one x) (magSub_empty x hx0' hx)
        (by rw [trim_embed [x] (by rw [show ([x] : List Nat).length = 1 from rfl]; exact FitsLen.one)])
      simpa [hdrop] using h
    · have hy : y < limbBase := Nat.lt_of_le_of_lt hle hx
      rw [bigNat_limb y hy hy0]
      dsimp [bigOf]
      have hdiff : x - y < limbBase := Nat.lt_of_le_of_lt (Nat.sub_le x y) hx
      have h := mag_sub_of_step (embed [x]) (embed [y]) [x - y]
        (len_embed_one x) (magSub_le x y hx hle)
        (by
          rw [trim_embed [x - y]
            (by rw [show ([x - y] : List Nat).length = 1 from rfl]; exact FitsLen.one)])
      have hdrop : dropTrail [x - y] = limbsOfNat (x - y) :=
        drop_singleton_limbs (x - y) hdiff
      simpa [hdrop] using h

/-! ## `peel_leading` -/

private theorem peelDivStep_gt (toV f : Int) (q : Megadreifach.BigInt) (h : f > toV) :
    peelDivStep toV (f, q) = .ok (SudoRt.Flow.brk (f, q)) := by
  unfold peelDivStep
  rw [if_pos h]
  rfl

private theorem peelDivStep_limb (n d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 12) (hn : n < limbBase) :
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
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) twelve_lt_limb
  have hqlt : n / factorial (f - 1) < limbBase := div_lt_limb hn
  have hdiv := divmod_limb (n / factorial (f - 1)) f hqlt hf0 hflt
  rw [hdiv, ok_bind]
  rw [show ((bigNat ((n / factorial (f - 1)) / f),
        (((n / factorial (f - 1)) % f : Nat) : Int)).1) =
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits13 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- Finish of `peel_leading` once the quotient is `n / d!`. -/
private theorem peel_finish (n d q : Nat) (hd : d ≤ 12) (hn : n < limbBase)
    (hq : q < limbBase) (hquot : q = n / factorial d) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat q)
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat n).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
  rw [limb_to_small_limb q hq, ok_bind,
    big_factorial_refines d (Nat.le_trans hd (by decide : (12 : Nat) ≤ 13)), ok_bind,
    show (q : Int) = Int.ofNat q from rfl,
    big_from_int_refines q (fits_of_lt_limb hq), ok_bind]
  have hcoeff : bigOf (limbsOfNat q) = bigNat q := by simp [bigNat]
  rw [hcoeff,
    big_mul_acc q (factorial d) (factorial_pos d) (factorial_one_limb d hd) hq, ok_bind]
  have hle : q * factorial d ≤ n := by
    rw [hquot]
    have hsum := Nat.div_add_mod n (factorial d)
    have hmul :
        factorial d * (n / factorial d) ≤
          factorial d * (n / factorial d) + n % factorial d :=
      Nat.le_add_right _ _
    rw [hsum] at hmul
    rwa [Nat.mul_comm] at hmul
  have hdiff_lt : n - q * factorial d < limbBase :=
    Nat.lt_of_le_of_lt (Nat.sub_le n _) hn
  rw [mag_sub_limb n (q * factorial d) hn hle, ok_bind,
    make_big_canon (n - q * factorial d) hdiff_lt, ok_bind, hquot, sub_mul_mod]
  exact pure_eq_ok _

/--
  `peel_leading (bigNat n) d = (n % d!, n / d!)`.

  `d ≤ 12` keeps `d!` in one limb. `n < 10^9` keeps the rank, every
  quotient, and the product `(n / d!) * d!` in one limb. The digit is
  positive when `d! ≤ n`.
-/
theorem peel_leading_limb (n d : Nat) (hd : d ≤ 12) (hn : n < limbBase) :
    Megadreifach.peel_leading (bigNat n) (d : Int) =
      .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)) := by
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
    have hstate : bigNat n = bigNat (n / factorial (2 - 1)) := by
      have : factorial (2 - 1) = 1 := by rfl
      rw [this, Nat.div_one]
    have hpair :
        ((Int.ofNat 2, bigNat n) : Int × Megadreifach.BigInt) =
          (Int.ofNat 2, bigNat (n / factorial (2 - 1))) :=
      congrArg (fun z => (Int.ofNat 2, z)) hstate
    rw [hpair]
    apply chain_loop
      (f := fun i => bigNat (n / factorial (i - 1)))
      (fromN := 2) (toN := d)
      (hle := hd2)
      (goal := .ok (bigNat (n % factorial d), ((n / factorial d : Nat) : Int)))
    · intro i hlo hhi
      simpa using peelDivStep_limb n d i hlo hhi hd hn
    · simp only [Prod.snd]
      rw [show (d + 1) - 1 = d from by omega]
      exact peel_finish n d (n / factorial d) hd hn (div_lt_limb hn) rfl
  · have hlt : d < 2 := by omega
    have hgt : (2 : Int) > (d : Int) := by
      have : (d : Int) < 2 := (ofNat_lt_iff d 2).mpr hlt
      omega
    have hfact : factorial d = 1 := by
      cases d with
      | zero => rfl
      | succ d =>
        have : d = 0 := by omega
        subst this
        rfl
    rw [asc_break (2 : Int) (d : Int) (bigNat n) _ _ _ hgt
        (peelDivStep_gt (d : Int) 2 (bigNat n) hgt)]
    have hq : n < limbBase := hn
    have hquot : n = n / factorial d := by rw [hfact, Nat.div_one]
    exact peel_finish n d n hd hn hq hquot

/-- Positive corner: peeling `d!` itself yields digit `1` and remainder `0`. -/
theorem peel_leading_factorial (d : Nat) (hd : d ≤ 12) :
    Megadreifach.peel_leading (bigNat (factorial d)) (d : Int) =
      .ok (bigNat 0, (1 : Int)) := by
  have hlt : factorial d < limbBase := factorial_one_limb d hd
  have h := peel_leading_limb (factorial d) d hd hlt
  rw [Nat.div_self (factorial_pos d), Nat.mod_self] at h
  simpa using h

end MegaDreifach.Link2
