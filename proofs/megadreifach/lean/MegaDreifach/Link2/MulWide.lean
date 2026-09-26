/-
  LINK 2. `big_mul` of a wide canonical limb list by a one-limb factor.

  The left factor may have any number of base-`10^9` limbs. The right
  factor is one limb. Each cell `digit * q + carry` stays below `10^18`,
  so it fits in an i64. The outer loop is the schoolbook product
  `scanMul`, trimmed to `natLimbs`.

  CLOSED: `big_mul_wide_refines`, `big_mul_nat`. The emitted product is
  `natLimbs (q * value)`. This is the multiply `big_factorial` and Horner
  `big_from_be` emit (accumulator on the left, small factor on the right).

  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.DivInd
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem addI_zero_nat (n : Nat) (h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

private theorem addI_nat_zero (n : Nat) (h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

private theorem addI_nat_one (n : Nat) (h : FitsLen (n + 1)) :
    SudoRt.addI (Int.ofNat n) (1 : Int) = .ok (Int.ofNat (n + 1)) := by
  have hone : (1 : Int) = Int.ofNat 1 := rfl
  rw [hone]
  exact addI_ofNat n 1 h

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem sum_limb_fits (x q c : Nat) (hx : x < limbBase) (hq : q < limbBase)
    (hc : c < limbBase) : FitsLen (x * q + c) := by
  have hx' : x ≤ limbBase - 1 := by omega
  have hq' : q ≤ limbBase - 1 := by omega
  have hc' : c ≤ limbBase - 1 := by omega
  have hmul : x * q ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul hx' hq'
  have hpair : (limbBase - 1) * (limbBase - 1) + (limbBase - 1) = (limbBase - 1) * limbBase := by
    calc
      (limbBase - 1) * (limbBase - 1) + (limbBase - 1)
        = (limbBase - 1) * (limbBase - 1) + (limbBase - 1) * 1 := by rw [Nat.mul_one]
      _ = (limbBase - 1) * ((limbBase - 1) + 1) := by rw [← Nat.mul_add]
      _ = (limbBase - 1) * limbBase := by
          have : (limbBase - 1) + 1 = limbBase := by omega
          rw [this]
  have hle : x * q + c ≤ (limbBase - 1) * limbBase := by omega
  have hlt : (limbBase - 1) * limbBase < limbBase ^ 2 := by
    rw [limbBase_pow2]
    exact Nat.mul_lt_mul_of_pos_right (by omega : limbBase - 1 < limbBase) limbBase_pos
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt)) limb_sq_fits

/-- Accumulator after absorbing the first `i` limbs of `xs`, times `q`. -/
def mulAcc (q : Nat) (xs : List Nat) (i : Nat) : List Nat :=
  let s := scanMul q 0 (xs.take i)
  padZero (s.1 ++ [s.2]) (xs.length + 1)

theorem mulAcc_length (q : Nat) (xs : List Nat) (i : Nat) (hi : i ≤ xs.length) :
    (mulAcc q xs i).length = xs.length + 1 := by
  unfold mulAcc
  have hraw :
      ((scanMul q 0 (xs.take i)).1 ++ [(scanMul q 0 (xs.take i)).2]).length = i + 1 := by
    rw [List.length_append, scanMul_length, List.length_take, List.length_singleton]
    omega
  exact padZero_length _ _ (by omega)

theorem mulAcc_zero (q : Nat) (xs : List Nat) :
    mulAcc q xs 0 = List.replicate (xs.length + 1) 0 := by
  unfold mulAcc padZero scanMul
  simp [List.replicate_succ]

private theorem raw_len (q : Nat) (xs : List Nat) (i : Nat) (hi : i ≤ xs.length) :
    ((scanMul q 0 (xs.take i)).1 ++ [(scanMul q 0 (xs.take i)).2]).length = i + 1 := by
  rw [List.length_append, scanMul_length, List.length_take, List.length_singleton]
  omega

theorem mulAcc_at_carry (q : Nat) (xs : List Nat) (i : Nat) (hi : i ≤ xs.length) :
    (mulAcc q xs i)[i]'(by rw [mulAcc_length q xs i hi]; omega) =
      (scanMul q 0 (xs.take i)).2 := by
  unfold mulAcc padZero
  have hlenD : (scanMul q 0 (xs.take i)).1.length = i := by
    rw [scanMul_length, List.length_take]; omega
  have hraw : ((scanMul q 0 (xs.take i)).1 ++ [(scanMul q 0 (xs.take i)).2]).length = i + 1 := by
    rw [List.length_append, hlenD, List.length_singleton]
  rw [List.getElem_append]
  have hlt : i < ((scanMul q 0 (xs.take i)).1 ++ [(scanMul q 0 (xs.take i)).2]).length := by
    rw [hraw]; omega
  simp only [hlt, dite_true]
  rw [List.getElem_append]
  have hnot : ¬ i < (scanMul q 0 (xs.take i)).1.length := by rw [hlenD]; omega
  simp [hnot, hlenD]

theorem mulAcc_at_zero (q : Nat) (xs : List Nat) (i j : Nat)
    (hi : i ≤ xs.length) (hj : i < j) (hj' : j < xs.length + 1) :
    (mulAcc q xs i)[j]'(by rw [mulAcc_length q xs i hi]; exact hj') = 0 := by
  unfold mulAcc padZero
  rw [List.getElem_append]
  have hnot : ¬ j < ((scanMul q 0 (xs.take i)).1 ++ [(scanMul q 0 (xs.take i)).2]).length := by
    rw [raw_len q xs i hi]; omega
  rw [dif_neg hnot]
  apply List.getElem_replicate

theorem mulAcc_succ (q : Nat) (xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase) :
    let c := (scanMul q 0 (xs.take i)).2
    let cur := xs[i] * q + c
    mulAcc q xs (i + 1) =
      ((mulAcc q xs i).set i (cur % limbBase)).set (i + 1) (cur / limbBase) := by
  intro c cur
  have hi' : i ≤ xs.length := Nat.le_of_lt hi
  have htake : ∀ d ∈ xs.take i, d < limbBase :=
    fun d hd => hxs d (List.mem_of_mem_take hd)
  have hc : c < limbBase := (scanMul_bounds q 0 hq limbBase_pos (xs.take i) htake).2
  have hdigLen : (scanMul q 0 (xs.take i)).1.length = i := by
    rw [scanMul_length, List.length_take]
    omega
  have hsetRaw :
      ((scanMul q 0 (xs.take i)).1 ++ [c]).set i (cur % limbBase) =
        (scanMul q 0 (xs.take i)).1 ++ [cur % limbBase] := by
    rw [set_append_right (scanMul q 0 (xs.take i)).1 [c] i (cur % limbBase)
      (by rw [hdigLen]; exact Nat.le_refl i)
      (by simp [List.length_singleton, hdigLen])]
    simp [hdigLen, Nat.sub_self, List.set_cons_zero]
  have hraw : ((scanMul q 0 (xs.take i)).1 ++ [c]).length = i + 1 := raw_len q xs i hi'
  have hpad1 :
      (mulAcc q xs i).set i (cur % limbBase) =
        padZero ((scanMul q 0 (xs.take i)).1 ++ [cur % limbBase]) (xs.length + 1) := by
    unfold mulAcc padZero
    rw [set_append_left ((scanMul q 0 (xs.take i)).1 ++ [c])
      (List.replicate (xs.length + 1 - ((scanMul q 0 (xs.take i)).1 ++ [c]).length) 0)
      i (cur % limbBase) (by rw [hraw]; omega)]
    rw [hsetRaw]
    have hsame :
        ((scanMul q 0 (xs.take i)).1 ++ [c]).length =
          ((scanMul q 0 (xs.take i)).1 ++ [cur % limbBase]).length := by
      rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
    rw [hsame]
  have hpreLen : ((scanMul q 0 (xs.take i)).1 ++ [cur % limbBase]).length = i + 1 := by
    rw [List.length_append, hdigLen, List.length_singleton]
  have hlt : ((scanMul q 0 (xs.take i)).1 ++ [cur % limbBase]).length < xs.length + 1 := by
    rw [hpreLen]; omega
  have hpad2 := padZero_set ((scanMul q 0 (xs.take i)).1 ++ [cur % limbBase])
    (xs.length + 1) (cur / limbBase) hlt
  rw [hpad1, ← hpreLen, hpad2, hpreLen]
  unfold mulAcc
  rw [take_succ_get xs i hi, scanMul_snoc q 0 (xs.take i) xs[i]]

/-- Carry propagation after a one-limb multiply digit. -/
def kCarryStep (toK : Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt) :=
  if σ.fst > toK then
    pure (SudoRt.Flow.brk (σ.fst, σ.snd.fst, σ.snd.snd))
  else do
    let liftK ←
      (if decide (σ.snd.snd > 0) = true then do
        let cur0 ← SudoRt.atL σ.snd.fst σ.fst
        let cur ← SudoRt.addI cur0 σ.snd.snd
        let digit ← SudoRt.modI cur Megadreifach.limb_base
        let out ← SudoRt.putL σ.snd.fst σ.fst digit
        let carry ← SudoRt.divI cur Megadreifach.limb_base
        pure (SudoRt.Flow.cont (out, carry))
      else
        pure (SudoRt.Flow.cont (σ.snd.fst, σ.snd.snd)))
    match liftK with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
    | .cont fs =>
      if (σ.fst == toK) = true then
        pure (SudoRt.Flow.brk (σ.fst, fs))
      else do
        let i' ← SudoRt.addI σ.fst 1
        pure (SudoRt.Flow.cont (i', fs))

private theorem kStep_idle (out : List Nat) (k toK : Nat) (hk : k ≤ toK)
    (hfit : FitsLen (k + 1)) :
    kCarryStep (Int.ofNat toK) (Int.ofNat k, embed out, (0 : Int)) =
      if k = toK then
        .ok (SudoRt.Flow.brk (Int.ofNat k, embed out, (0 : Int)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), embed out, (0 : Int))) := by
  unfold kCarryStep
  have hngt : ¬ (toK < k) := by omega
  simp [hngt, decide_eq_false_iff_not.mpr (by decide : ¬ ((0 : Int) > 0))]
  by_cases heq : k = toK
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hne : ¬ ((k : Int) = (toK : Int)) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_nat_one k hfit
    simp [heq, hne, beq_int_iff]
    rw [show (k : Int) = Int.ofNat k from rfl, hadd]
    simp [pure_eq_ok]

theorem kLoop_idle (out : List Nat) (k0 toK : Nat) (hle : k0 ≤ toK)
    (hfit : FitsLen (toK + 1)) :
    SudoRt.runLoopOn (Int.ofNat k0, embed out, (0 : Int))
      (fuelRange (Int.ofNat k0) (Int.ofNat toK))
      (kCarryStep (Int.ofNat toK))
      (fun σ => pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) σ.2.1))
      (fun r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)) =
    pure (SudoRt.Flow.cont (embed out)) := by
  apply chain_loop
    (f := fun _ => (embed out, (0 : Int)))
    (fromN := k0) (toN := toK) (hle := hle)
    (goal := pure (SudoRt.Flow.cont (embed out)))
  · intro i _ hi2
    exact kStep_idle out i toK hi2 (FitsLen.of_le hfit (by omega))
  · rfl

private theorem kStep_write (out : List Nat) (k toK c : Nat) (hk : k ≤ toK)
    (hc0 : 0 < c) (hc : c < limbBase) (hlen : k < out.length)
    (h0 : out[k] = 0) (hfit : FitsLen (k + 1)) :
    kCarryStep (Int.ofNat toK) (Int.ofNat k, embed out, Int.ofNat c) =
      if k = toK then
        .ok (SudoRt.Flow.brk (Int.ofNat k, embed (out.set k c), (0 : Int)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), embed (out.set k c), (0 : Int))) := by
  unfold kCarryStep
  have hngt : ¬ (toK < k) := by omega
  simp [hngt, hc0, ok_bind]
  have hidx : k < (embed out).size := by rw [size_embed]; exact hlen
  rw [show (k : Int) = Int.ofNat k from rfl, atL_embed out k hlen, h0]
  simp [ok_bind]
  rw [show (c : Int) = Int.ofNat c from rfl, addI_zero_nat c (fits_of_lt_limb hc)]
  simp [ok_bind]
  rw [show (c : Int) = Int.ofNat c from rfl, show (k : Int) = Int.ofNat k from rfl]
  rw [modI_nat_base c, Nat.mod_eq_of_lt hc, divI_nat_base c, Nat.div_eq_of_lt hc]
  simp [ok_bind]
  rw [show (k : Int) = Int.ofNat k from rfl, show (c : Int) = Int.ofNat c from rfl,
    putL_ofNat (embed out) k (Int.ofNat c) hidx, embed_set_nat out k c hlen]
  simp [ok_bind, pure_eq_ok]
  by_cases heq : k = toK
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hne : ¬ ((k : Int) = (toK : Int)) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_nat_one k hfit
    simp [heq, hne, beq_int_iff]
    rw [show (k : Int) = Int.ofNat k from rfl, hadd]
    simp [pure_eq_ok]

theorem kLoop_write (out : List Nat) (k0 toK c : Nat) (hle : k0 ≤ toK)
    (hc0 : 0 < c) (hc : c < limbBase)
    (hlen : k0 < out.length) (h0 : out[k0] = 0)
    (hfit : FitsLen (toK + 1)) :
    SudoRt.runLoopOn (Int.ofNat k0, embed out, Int.ofNat c)
      (fuelRange (Int.ofNat k0) (Int.ofNat toK))
      (kCarryStep (Int.ofNat toK))
      (fun σ => pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) σ.2.1))
      (fun r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)) =
    pure (SudoRt.Flow.cont (embed (out.set k0 c))) := by
  rw [fuelRange_le hle]
  have hfuel : toK - k0 + 1 = (toK - k0) + 1 := by omega
  rw [hfuel, runLoopOn_succ, kStep_write out k0 toK c hle hc0 hc hlen h0
    (FitsLen.of_le hfit (by omega))]
  by_cases heq : k0 = toK
  · simp [heq, pure_eq_ok]
  · simp [heq, pure_eq_ok]
    have hnext : toK - k0 = fuelRange (Int.ofNat (k0 + 1)) (Int.ofNat toK) := by
      rw [fuelRange_le (by omega)]
      omega
    rw [hnext]
    exact kLoop_idle (out.set k0 c) (k0 + 1) toK (by omega) hfit

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

/-- Expose the outer schoolbook loop of `big_mul` for a one-limb right factor. -/
theorem big_mul_wide_open (q : Nat) (xs : List Nat) (_hq0 : 0 < q) (hne : xs ≠ [])
    (hfits : FitsLen (xs.length + 1)) :
    Megadreifach.big_mul (bigOf xs) (bigOf [q]) =
      SudoRt.runLoopOn ((0 : Int), embed (List.replicate (xs.length + 1) 0))
        (fuelRange (0 : Int) (Int.ofNat (xs.length - 1)))
        (mulSchoolStep (bigOf xs) (bigOf [q]) (Int.ofNat (xs.length - 1)))
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  have hpos : 0 < xs.length := Nat.pos_of_ne_zero (fun h => hne (List.eq_nil_of_length_eq_zero h))
  have hlenA : SudoRt.listLen (embed xs) = Int.ofNat xs.length := listLen_embed xs
  have hlenB : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  rw [hlenA, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (fun h => hne (List.eq_nil_of_length_eq_zero h)),
    if_neg (by decide : ¬ ((false : Bool) = true))]
  conv =>
    lhs
    pattern SudoRt.SEq.beq (SudoRt.listLen (embed [q])) (0 : Int)
    rw [hlenB]
  have hbeq : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq, show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  conv =>
    lhs
    pattern SudoRt.addI (Int.ofNat xs.length) (SudoRt.listLen (embed [q]))
    rw [hlenB]
  rw [addI_ofNat_one xs.length hfits, ok_bind, filledL_ofNat, ok_bind, embed_replicate_zero]
  rw [subI_ofNat_one xs.length hpos (FitsLen.of_le hfits (Nat.le_succ _)), ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulSchoolStep (bigOf xs) (bigOf [q]) (Int.ofNat (xs.length - 1)))
    intro σ
    unfold mulSchoolStep
    dsimp [bigOf]
    rfl
  rw [fuelRange_eq]
  rfl

/-! ## One outer digit, then the trimmed product -/

private theorem getElem_irrel (xs : List Nat) (i : Nat) (h1 h2 : i < xs.length) :
    xs[i]'h1 = xs[i]'h2 := by
  induction xs generalizing i with
  | nil => simp at h1
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp [List.getElem_cons_succ,
        ih i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)]

private theorem set_eq_val (xs : List Nat) (i v : Nat) {hi : i < xs.length}
    (h : xs[i] = v) : xs.set i v = xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero] at h ⊢
      simp [h]
    | succ i =>
      simp only [List.set_cons_succ, List.getElem_cons_succ] at h ⊢
      rw [ih i (hi := Nat.lt_of_succ_lt_succ hi) h]

private theorem mulAcc_done (q : Nat) (xs : List Nat) :
    mulAcc q xs xs.length =
      (scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2] := by
  simp only [mulAcc, List.take_length, padZero]
  have hlen :
      ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length = xs.length + 1 := by
    rw [List.length_append, scanMul_length, List.length_singleton]
  simp [hlen]

private theorem fits_index (n i : Nat) (hi : i < n) (hfits : FitsLen (n + 1)) :
    FitsLen (i + 1) :=
  FitsLen.of_le hfits (Nat.succ_le_of_lt (Nat.lt_succ_of_lt hi))

/-- One schoolbook cell: `out[i] + limb * q`, with the incoming carry already
    stored at `out[i]` and the loop carry still zero. -/
private theorem wideDigit (xs out : List Nat) (q c i : Nat)
    (hi : i < out.length) (hix : i < xs.length) (hcAt : out[i] = c)
    (hx : xs[i] < limbBase) (hq : q < limbBase) (hc : c < limbBase)
    (hfit : FitsLen (i + 1)) :
    ((do
      let ij ← SudoRt.addI (Int.ofNat i) (0 : Int)
      let cur0 ← SudoRt.atL (embed out) ij
      let ai ← SudoRt.atL (embed xs) (Int.ofNat i)
      let bj ← SudoRt.atL (embed [q]) (0 : Int)
      let prod ← SudoRt.mulI ai bj
      let s1 ← SudoRt.addI cur0 prod
      let cur ← SudoRt.addI s1 (0 : Int)
      let ij2 ← SudoRt.addI (Int.ofNat i) (0 : Int)
      let digit ← SudoRt.modI cur Megadreifach.limb_base
      let out ← SudoRt.putL (embed out) ij2 digit
      let carry ← SudoRt.divI cur Megadreifach.limb_base
      pure (SudoRt.Flow.cont (out, carry))) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int × Int) Megadreifach.BigInt)) =
      .ok (SudoRt.Flow.cont
        (embed (out.set i ((xs[i] * q + c) % limbBase)),
          Int.ofNat ((xs[i] * q + c) / limbBase))) := by
  have hsum := sum_limb_fits (xs[i]) q c hx hq hc
  have hprod : FitsLen (xs[i] * q) :=
    FitsLen.of_le hsum (Nat.le_add_right _ _)
  have hsumc : FitsLen (c + xs[i] * q) := by
    simpa [Nat.add_comm] using hsum
  have hfiti : FitsLen i := FitsLen.of_le hfit (Nat.le_succ i)
  have hadd0 := addI_nat_zero i hfiti
  rw [hadd0, ok_bind]
  have hat : SudoRt.atL (embed out) (Int.ofNat i) = .ok (Int.ofNat c) := by
    rw [atL_embed out i hi, hcAt]
  rw [hat, ok_bind]
  have hq0 : 0 < ([q] : List Nat).length := by simp
  erw [atL_embed xs i hix, ok_bind, atL_embed [q] 0 hq0, ok_bind]
  simp only [List.getElem_cons_zero]
  rw [mulI_ofNat (xs[i]) q hprod, ok_bind]
  have haddc : SudoRt.addI (Int.ofNat c) (Int.ofNat (xs[i] * q)) =
      .ok (Int.ofNat (c + xs[i] * q)) := addI_ofNat c (xs[i] * q) hsumc
  rw [haddc, ok_bind]
  have haddZ := addI_nat_zero (c + xs[i] * q) hsumc
  rw [haddZ, ok_bind]
  have hcomm : c + xs[i] * q = xs[i] * q + c := Nat.add_comm _ _
  rw [hcomm]
  rw [ok_bind]
  rw [modI_nat_base (xs[i] * q + c), ok_bind]
  have hidx : i < (embed out).size := by rw [size_embed]; exact hi
  rw [putL_ofNat (embed out) i (Int.ofNat ((xs[i] * q + c) % limbBase)) hidx, ok_bind]
  rw [embed_set_nat out i ((xs[i] * q + c) % limbBase) hi]
  rw [divI_nat_base (xs[i] * q + c), ok_bind]
  rfl

private theorem kCarry_fun (toK : Int) :
    (fun σ : Int × (Array Int × Int) =>
      if σ.fst > toK then
        pure (SudoRt.Flow.brk (σ.fst, σ.snd.fst, σ.snd.snd))
      else do
        let liftK ←
          (if decide (σ.snd.snd > 0) = true then do
            let cur0 ← SudoRt.atL σ.snd.fst σ.fst
            let cur ← SudoRt.addI cur0 σ.snd.snd
            let digit ← SudoRt.modI cur Megadreifach.limb_base
            let out ← SudoRt.putL σ.snd.fst σ.fst digit
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (out, carry))
          else
            pure (SudoRt.Flow.cont (σ.snd.fst, σ.snd.snd)))
        match liftK with
        | .ret r => pure (SudoRt.Flow.ret r)
        | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
        | .cont fs =>
          if (σ.fst == toK) = true then
            pure (SudoRt.Flow.brk (σ.fst, fs))
          else do
            let i' ← SudoRt.addI σ.fst 1
            pure (SudoRt.Flow.cont (i', fs))) =
      kCarryStep toK := by
  unfold kCarryStep
  rfl

/-- Write the one-limb carry into the next cell. A zero carry leaves the
    already-zero cell alone. -/
private theorem kPropagate (q : Nat) (out : List Nat) (i carryN len : Nat)
    (hi : i < len) (hc : carryN < limbBase)
    (hlen : out.length = len + 1) (hIdx : i + 1 < out.length)
    (h0 : out[i + 1]'hIdx = 0)
    (hfits : FitsLen (len + 1)) :
    ((do
      let k0 ← SudoRt.addI (Int.ofNat i) (SudoRt.listLen (embed [q]))
      let toK ← SudoRt.subI (SudoRt.listLen (embed out)) 1
      let kLoop ←
        SudoRt.runLoopOn (k0, embed out, Int.ofNat carryN)
          (if k0 > toK then 1 else (toK - k0).natAbs + 1)
          (fun σk =>
            if σk.fst > toK then
              pure (SudoRt.Flow.brk (σk.fst, σk.snd.fst, σk.snd.snd))
            else do
              let liftK ←
                (if decide (σk.snd.snd > 0) = true then do
                  let cur0 ← SudoRt.atL σk.snd.fst σk.fst
                  let cur ← SudoRt.addI cur0 σk.snd.snd
                  let digit ← SudoRt.modI cur Megadreifach.limb_base
                  let out ← SudoRt.putL σk.snd.fst σk.fst digit
                  let carry ← SudoRt.divI cur Megadreifach.limb_base
                  pure (SudoRt.Flow.cont (out, carry))
                else
                  pure (SudoRt.Flow.cont (σk.snd.fst, σk.snd.snd)))
              match liftK with
              | .ret r => pure (SudoRt.Flow.ret r)
              | .brk fs => pure (SudoRt.Flow.brk (σk.fst, fs))
              | .cont fs =>
                if (σk.fst == toK) = true then
                  pure (SudoRt.Flow.brk (σk.fst, fs))
                else do
                  let i' ← SudoRt.addI σk.fst 1
                  pure (SudoRt.Flow.cont (i', fs)))
          (fun σk => pure (SudoRt.Flow.cont σk.snd.fst))
          (fun r => pure (SudoRt.Flow.ret r))
      pure kLoop) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) =
      pure (SudoRt.Flow.cont (embed (out.set (i + 1) carryN))) := by
  have hlen1 : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hfiti : FitsLen (i + 1) := fits_index len i hi hfits
  have hadd := addI_ofNat_one i hfiti
  rw [hlen1, hadd, ok_bind]
  have hposL : 0 < out.length := by omega
  have hlenE : SudoRt.listLen (embed out) = Int.ofNat out.length := listLen_embed out
  rw [hlenE, subI_ofNat_one out.length hposL (by rw [hlen]; exact hfits), ok_bind]
  have hto : out.length - 1 = len := by omega
  rw [hto]
  have hk0 : i + 1 ≤ len := by omega
  have hfuel :
      (if (Int.ofNat (i + 1)) > (Int.ofNat len) then 1
        else ((Int.ofNat len) - (Int.ofNat (i + 1))).natAbs + 1) =
        fuelRange (Int.ofNat (i + 1)) (Int.ofNat len) :=
    fuelRange_eq _ _
  rw [hfuel]
  have hfun := kCarry_fun (Int.ofNat len)
  rw [hfun]
  have hafter :
      (fun σk : Int × (Array Int × Int) =>
        (pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) σk.snd.fst) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) =
      (fun σk : Int × (Array Int × Int) =>
        (pure (SudoRt.Flow.cont σk.snd.fst) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) := rfl
  rw [← hafter]
  have hon :
      (fun r : Megadreifach.BigInt =>
        (pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) =
      (fun r : Megadreifach.BigInt =>
        (pure (SudoRt.Flow.ret r) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) := rfl
  rw [← hon]
  by_cases hc0 : carryN = 0
  · subst hc0
    rw [except_bind_pure]
    erw [kLoop_idle out (i + 1) len hk0 hfits]
    rw [set_eq_val out (i + 1) 0 h0]
  · have hposC : 0 < carryN := Nat.pos_of_ne_zero hc0
    rw [except_bind_pure]
    erw [kLoop_write out (i + 1) len carryN hk0 hposC hc hIdx h0 hfits]

/-- One outer iteration of `big_mul` on a one-limb right factor. -/
private theorem mulSchool_at (q : Nat) (xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase)
    (hfits : FitsLen (xs.length + 1)) :
    mulSchoolStep (bigOf xs) (bigOf [q]) (Int.ofNat (xs.length - 1))
        (Int.ofNat i, embed (mulAcc q xs i)) =
      if i = xs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed (mulAcc q xs (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (mulAcc q xs (i + 1)))) := by
  have hi' : i ≤ xs.length := Nat.le_of_lt hi
  have hiTo : i ≤ xs.length - 1 := by omega
  have hngt : ¬ (Int.ofNat i) > (Int.ofNat (xs.length - 1)) := ofNat_not_gt hiTo
  have htake : ∀ d ∈ xs.take i, d < limbBase :=
    fun d hd => hxs d (List.mem_of_mem_take hd)
  have hcScan : (scanMul q 0 (xs.take i)).2 < limbBase :=
    (scanMul_bounds q 0 hq limbBase_pos (xs.take i) htake).2
  have hcAt := mulAcc_at_carry q xs i hi'
  have hc : (mulAcc q xs i)[i]'(by rw [mulAcc_length q xs i hi']; omega) < limbBase := by
    rw [hcAt]; exact hcScan
  have hx : xs[i] < limbBase := hxs _ (List.getElem_mem hi)
  have hfiti := fits_index xs.length i hi hfits
  have hdigit := wideDigit xs (mulAcc q xs i) q
      ((mulAcc q xs i)[i]'(by rw [mulAcc_length q xs i hi']; omega)) i
      (by rw [mulAcc_length q xs i hi']; omega) hi rfl hx hq hc hfiti
  unfold mulSchoolStep
  rw [if_neg hngt]
  dsimp [bigOf]
  have hlen1 : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  rw [hlen1, subI_one_one, ok_bind]
  have hfuel :
      (if (0 : Int) > (0 : Int) then 1 else ((0 : Int) - (0 : Int)).natAbs + 1) = 0 + 1 := by
    simp
  rw [hfuel, runLoopOn_succ]
  dsimp
  erw [hdigit]
  rw [ok_bind]
  simp only [pure_eq_ok]
  have hsucc := mulAcc_succ q xs i hi hq hxs
  have hIdx0 : i + 1 < (mulAcc q xs i).length := by
    rw [mulAcc_length q xs i hi']; omega
  have hcell0 : (mulAcc q xs i)[i + 1]'hIdx0 = 0 :=
    mulAcc_at_zero q xs i (i + 1) hi' (Nat.lt_succ_self i) (by omega)
  have hlenAcc : (mulAcc q xs i).length = xs.length + 1 := mulAcc_length q xs i hi'
  let digit := (xs[i] * q + (mulAcc q xs i)[i]'(by rw [hlenAcc]; omega)) % limbBase
  let carryN := (xs[i] * q + (mulAcc q xs i)[i]'(by rw [hlenAcc]; omega)) / limbBase
  have hcarryLt : carryN < limbBase :=
    mul_carry_lt (xs[i]) q _ hx hq hc
  have houtLen : ((mulAcc q xs i).set i digit).length = xs.length + 1 := by
    rw [List.length_set, hlenAcc]
  have hIdx : i + 1 < ((mulAcc q xs i).set i digit).length := by
    rw [houtLen]; omega
  have h0next : ((mulAcc q xs i).set i digit)[i + 1]'hIdx = 0 := by
    have hne := List.getElem_set_ne (l := mulAcc q xs i) (i := i) (j := i + 1)
      (by omega : i ≠ i + 1) (a := digit) hIdx
    have hback : (mulAcc q xs i)[i + 1]'(by simp at hIdx; exact hIdx) = 0 := by
      simpa [getElem_irrel (mulAcc q xs i) (i + 1)] using hcell0
    exact hne.trans hback
  have hk := kPropagate q ((mulAcc q xs i).set i digit) i carryN xs.length hi
    hcarryLt houtLen hIdx h0next hfits
  erw [hk]
  rw [pure_eq_ok, ok_bind]
  have hnext : mulAcc q xs (i + 1) =
      (((mulAcc q xs i).set i digit).set (i + 1) carryN) := by
    simpa [digit, carryN, hcAt] using hsucc
  rw [← hnext]
  by_cases heq : i = xs.length - 1
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hneI : (i : Int) ≠ ((xs.length - 1 : Nat) : Int) :=
      fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == ((xs.length - 1 : Nat) : Int)) = false := by
      simpa [beq_int_iff] using hneI
    simp only [hbeq, heq, pure_eq_ok]
    have hadd := addI_ofNat_one i hfiti
    erw [hadd]
    rw [ok_bind]
    rfl

/-- `big_mul` of any canonical-digit string by one limb is `natLimbs` of the product. -/
theorem big_mul_wide_refines (q : Nat) (xs : List Nat)
    (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase)
    (hfits : FitsLen (xs.length + 1)) :
    Megadreifach.big_mul (bigOf xs) (bigOf (natLimbs q)) =
      .ok (bigOf (natLimbs (q * limbVal xs))) := by
  by_cases hq0 : q = 0
  · simp [hq0, natLimbs_zero, Nat.zero_mul, big_mul_zero_right]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hlimbs : natLimbs q = [q] := natLimbs_of_pos_lt q hqpos hq
    rw [hlimbs]
    by_cases hnil : xs = []
    · simp [hnil, limbVal, Nat.mul_zero, natLimbs_zero, big_mul_zero_left]
    · have hpos : 0 < xs.length :=
        Nat.pos_of_ne_zero (fun h => hnil (List.eq_nil_of_length_eq_zero h))
      rw [big_mul_wide_open q xs hqpos hnil hfits]
      rw [show (0 : Int) = Int.ofNat 0 from rfl,
        show embed (List.replicate (xs.length + 1) 0) = embed (mulAcc q xs 0) from by
          rw [mulAcc_zero]]
      apply chain_loop
        (f := fun i => embed (mulAcc q xs i))
        (fromN := 0) (toN := xs.length - 1)
        (hle := Nat.zero_le _)
        (goal := .ok (bigOf (natLimbs (q * limbVal xs))))
      · intro i _ hi2
        have hi : i < xs.length := by omega
        simpa using mulSchool_at q xs i hi hq hxs hfits
      · have hfull : (xs.length - 1) + 1 = xs.length := by omega
        rw [hfull]
        rw [mulAcc_done q xs, except_bind_pure]
        have hrawLen :
            ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length = xs.length + 1 := by
          rw [List.length_append, scanMul_length, List.length_singleton]
        have hfitRaw : FitsLen
            ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length := by
          rw [hrawLen]; exact hfits
        rw [make_big_false _ hfitRaw, scan_raw_trim q xs hq hxs]

/-- Same product on the canonical limbs of a natural number. -/
theorem big_mul_nat (q n : Nat) (hq : q < limbBase)
    (hfits : FitsLen ((natLimbs n).length + 1)) :
    Megadreifach.big_mul (bigOf (natLimbs n)) (bigOf (natLimbs q)) =
      .ok (bigOf (natLimbs (q * n))) := by
  simpa [limbVal_natLimbs] using
    big_mul_wide_refines q (natLimbs n) hq (natLimbs_digits n) hfits

end MegaDreifach.Link2
