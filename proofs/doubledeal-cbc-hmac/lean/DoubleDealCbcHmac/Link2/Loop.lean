/-
  LINK 2. The shape every emitted ascending `for i = from to toV` stepper takes, once
  its destructuring `let`s are reduced. Proof-only; reuses the MegaDreifach runtime
  lemmas (`MegaDreifach.Link2.Sudo`, `chain_loop`). Not emitter soundness.
-/
import MegaDreifach.Link2.Loop

namespace DoubleDealCbcHmac.Link2
open MegaDreifach.Link2

@[simp] theorem bind_ok_right {ε α} (m : Except ε α) : (m >>= fun r => Except.ok r) = m := by
  cases m <;> rfl

/-- One iteration of an emitted ascending loop whose body continues with `s'`. -/
theorem asc_step {S ρ : Type} (toN i : Nat) (hi : i ≤ toN) (hfit : FitsLen (i + 1)) (st : S)
    (body : Except SudoRt.Trap (SudoRt.Flow S ρ)) (s' : S)
    (hbody : body = .ok (.cont s')) :
    (if Int.ofNat i > Int.ofNat toN then
        (pure (SudoRt.Flow.brk (Int.ofNat i, st)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else do
        let d ← body
        match d with
        | .ret r => pure (SudoRt.Flow.ret r)
        | .brk fs => pure (SudoRt.Flow.brk (Int.ofNat i, fs))
        | .cont fs =>
          if (Int.ofNat i == Int.ofNat toN) = true then pure (SudoRt.Flow.brk (Int.ofNat i, fs))
          else do
            let i' ← SudoRt.addI (Int.ofNat i) 1
            pure (SudoRt.Flow.cont (i', fs))) =
      if i = toN then .ok (.brk (Int.ofNat i, s')) else .ok (.cont (Int.ofNat (i + 1), s')) := by
  rw [if_neg (ofNat_not_gt hi), hbody, ok_bind]
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]; rfl
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [addI_ofNat_one i hfit]
    rfl

/-- The emitted loop tail after the body continued with `s`: break on the last index,
    else step the index (no Overflow for `FitsLen (i + 1)`). -/
theorem asc_tail {S ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i + 1), s)) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [addI_ofNat_one i hfit]
    rfl

/-- The same tail for a loop whose state is the index alone. -/
theorem asc_tail_idx {ρ : Type} (toN i : Nat) (hfit : FitsLen (i + 1)) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i)) : Except SudoRt.Trap (SudoRt.Flow Int ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont i')) =
      if i = toN then .ok (.brk (Int.ofNat i)) else .ok (.cont (Int.ofNat (i + 1))) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [addI_ofNat_one i hfit]
    rfl

/-- The tail of an emitted descending loop `for i = from downto 0`. -/
theorem desc_tail {S ρ : Type} (i : Nat) (hfit : FitsLen i) (s : S) :
    (if (Int.ofNat i == Int.ofNat 0) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.subI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = 0 then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i - 1), s)) := by
  by_cases h : i = 0
  · subst h; simp [beq_int_iff]
  · have hne : ¬ (Int.ofNat i = Int.ofNat 0) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [subI_ofNat_one i (Nat.pos_of_ne_zero h) hfit]
    rfl

theorem decide_zero_le_ofNat (n : Nat) : decide ((0 : Int) ≤ Int.ofNat n) = true :=
  decide_eq_true (Int.ofNat_zero_le n)

theorem decide_ofNat_le_of {a b : Nat} (h : a ≤ b) :
    decide (Int.ofNat a ≤ Int.ofNat b) = true :=
  decide_eq_true (Int.ofNat_le.mpr h)

/-- `(embed l).push x` is `embed (l ++ [x])`. -/
theorem push_embed' (l : List Nat) (x : Nat) :
    (embed l).push (Int.ofNat x) = embed (l ++ [x]) := by
  simp [embed, List.map_append, Array.push]

/-- An emitted ascending loop `for i = fromN to toN` whose body appends `g i` to the
    accumulator: it ends with `pre ++ [g fromN, …, g toN]`. -/
theorem push_loop {ρ β : Type} (fromN toN : Nat) (hle : fromN ≤ toN) (g : Nat → Nat)
    (pre : List Nat)
    (step : Int × Array Int → Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) ρ))
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (hstep : ∀ i (l : List Nat), fromN ≤ i → i ≤ toN →
      step (Int.ofNat i, embed l) =
        if i = toN then .ok (.brk (Int.ofNat i, embed (l ++ [g i])))
        else .ok (.cont (Int.ofNat (i + 1), embed (l ++ [g i])))) :
    SudoRt.runLoopOn (Int.ofNat fromN, embed pre) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        step after onRet =
      after (Int.ofNat toN, embed (pre ++ (List.range' fromN (toN + 1 - fromN)).map g)) := by
  have hf : ∀ i, fromN ≤ i → pre ++ (List.range' fromN (i - fromN)).map g ++ [g i] =
      pre ++ (List.range' fromN (i + 1 - fromN)).map g := by
    intro i hi
    rw [show i + 1 - fromN = (i - fromN) + 1 by omega, List.range'_1_concat, List.map_append,
      List.append_assoc]
    simp [show fromN + (i - fromN) = i by omega]
  have h0 : embed pre = embed (pre ++ (List.range' fromN (fromN - fromN)).map g) := by simp
  rw [h0]
  refine chain_loop step after onRet
    (fun i => embed (pre ++ (List.range' fromN (i - fromN)).map g)) fromN toN hle ?_ _ rfl
  intro i h1 h2
  rw [hstep i _ h1 h2, hf i h1]

theorem range'_map_getD (xs : List Nat) (s k : Nat) (h : s + k ≤ xs.length) :
    (List.range' s k).map (fun i => xs.getD i 0) = (xs.drop s).take k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range'_1_concat, List.map_append, ih (by omega), List.take_succ]
    simp only [List.map_cons, List.map_nil, List.getElem?_drop]
    rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl

end DoubleDealCbcHmac.Link2
