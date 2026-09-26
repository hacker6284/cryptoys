/-
  LINK 2. `big_mul` of a wide canonical limb list by a one-limb factor.

  The left factor may have any number of base-`10^9` limbs. The right
  factor is one limb. Each cell `digit * q + carry` stays below `10^18`,
  so it fits in an i64. The outer loop is the schoolbook product
  `scanMul`, trimmed to `natLimbs`.

  This is the multiply `big_factorial` and Horner `big_from_be` emit
  (accumulator on the left, small factor on the right).

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

private theorem kLoop_idle (out : List Nat) (k0 toK : Nat) (hle : k0 ≤ toK)
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

private theorem kLoop_write (out : List Nat) (k0 toK c : Nat) (hle : k0 ≤ toK)
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

end MegaDreifach.Link2
