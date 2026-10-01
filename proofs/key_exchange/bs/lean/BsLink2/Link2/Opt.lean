/-
  BS Link 2: refinement of partial code. A model that can fail is an `Option`; the emitted
  code is an `Except SudoRt.Trap`. "Refines" is `x.toOption = o.map E`: the emitted code
  succeeds with `E b` exactly when the model returns `b`, and traps exactly when the model
  fails (whatever the trap's message). A loop driver for this form. Proof-only.
-/
import BsLink2.Link2.Loop

namespace BsLink2.Link2

open MegaDreifach.Link2

@[simp] theorem toOpt_ok {ε α} (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

@[simp] theorem toOpt_error {ε α} (e : ε) : (Except.error e : Except ε α).toOption = none := rfl

theorem toOpt_bind {ε α β} (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind (fun a => (f a).toOption) := by
  cases x <;> rfl

@[simp] theorem toOpt_pure {ε α} (a : α) : (pure a : Except ε α).toOption = some a := rfl

theorem atL_toOpt {α} (a : Array α) (i : Nat) : (SudoRt.atL a (Int.ofNat i)).toOption = a[i]? := by
  by_cases h : i < a.size
  · rw [atL_ofNat _ _ h, Array.getElem?_eq_getElem h]; rfl
  · have hf : (SudoRt.idxCheck a.size (Int.ofNat i)).toOption = none := by
      unfold SudoRt.idxCheck
      rw [if_pos (by simp; omega)]; rfl
    unfold SudoRt.atL
    rw [show a[i]? = none by simp; omega]
    revert hf
    cases SudoRt.idxCheck a.size (Int.ofNat i) with
    | error e => intro _; rfl
    | ok j => intro hf; cases hf

theorem sudoAssert_false_opt (line : Nat) : (SudoRt.sudoAssert false line).toOption = none := rfl

theorem runLoopOn_succ_opt {σ ρ α} (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α) (onRet : ρ → Except SudoRt.Trap α) :
    (SudoRt.runLoopOn (ρ := ρ) s0 (fuel + 1) step after onRet).toOption =
      (step s0).toOption.bind (fun fl => match fl with
        | .ret r => (onRet r).toOption
        | .brk s => (after s).toOption
        | .cont s => (SudoRt.runLoopOn (ρ := ρ) s fuel step after onRet).toOption) := by
  rw [runLoopOn_succ]
  cases step s0 with
  | error e => rfl
  | ok fl => cases fl <;> rfl

theorem foldlM_range'_succ {S} (m : Nat → S → Option S) (a k : Nat) (s : S) :
    (List.range' a (k + 1)).foldlM (fun s i => m i s) s =
      (m a s).bind (fun s' => (List.range' (a + 1) k).foldlM (fun s i => m i s) s') := by
  simp only [List.range', List.foldlM_cons]
  rfl

/-- An ascending loop `for i = fromN to n − 1` (`fromN < n`) whose iterations may trap,
    against a model whose steps may fail: the emitted loop refines the model's fold, and
    joins `after` (which must not depend on the index) with the final state. `P` is an
    invariant the model steps keep. -/
theorem loop_opt {S α ρ β} (E : S → α)
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (m : Nat → S → Option S) (P : Nat → S → Prop) (A : S → Option β) (fromN n : Nat)
    (hlt : fromN < n)
    (hstep : ∀ i s, fromN ≤ i → i < n → P i s →
      (step (Int.ofNat i, E s)).toOption = (m i s).map (fun s' =>
        if i + 1 = n then .brk (Int.ofNat i, E s') else .cont (Int.ofNat (i + 1), E s')))
    (hP : ∀ i s s', fromN ≤ i → i < n → P i s → m i s = some s' → P (i + 1) s')
    (hafter : ∀ j s, P n s → (after (j, E s)).toOption = A s)
    (s0 : S) (h0 : P fromN s0) :
    (SudoRt.runLoopOn (Int.ofNat fromN, E s0) (fuelRange (Int.ofNat fromN) (Int.ofNat (n - 1)))
      step after onRet).toOption =
      ((List.range' fromN (n - fromN)).foldlM (fun s i => m i s) s0).bind A := by
  rw [fuelRange_le (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, n - fromN = k + 1 := ⟨n - fromN - 1, by omega⟩
  rw [show n - 1 - fromN = k by omega, hk]
  induction k generalizing fromN s0 with
  | zero =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt h0, foldlM_range'_succ]
    cases hm : m fromN s0 with
    | none => rfl
    | some s' =>
      simp only [Option.map_some', Option.some_bind, if_pos (show fromN + 1 = n by omega)]
      exact hafter _ s' (by have := hP fromN s0 s' (Nat.le_refl _) hlt h0 hm; rwa [show fromN + 1 = n by omega] at this)
  | succ k ih =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt h0, foldlM_range'_succ]
    cases hm : m fromN s0 with
    | none => rfl
    | some s' =>
      simp only [Option.map_some', Option.some_bind, if_neg (show ¬ fromN + 1 = n by omega)]
      exact ih (fromN + 1) (by omega) (fun i s h1 h2 hI => hstep i s (by omega) h2 hI)
        (fun i s s'' h1 h2 hI hm' => hP i s s'' (by omega) h2 hI hm') s'
        (hP fromN s0 s' (Nat.le_refl _) hlt h0 hm) (by omega)

/-- The same loop when its range is empty (`n ≤ fromN`): the first test breaks at once. -/
theorem loop_opt_empty {S α ρ β} (E : S → α)
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (fromN : Nat) (toV : Int) (hgt : Int.ofNat fromN > toV) (s0 : S)
    (hbrk : step (Int.ofNat fromN, E s0) = .ok (.brk (Int.ofNat fromN, E s0))) :
    SudoRt.runLoopOn (Int.ofNat fromN, E s0) (fuelRange (Int.ofNat fromN) toV)
      step after onRet = after (Int.ofNat fromN, E s0) := by
  rw [fuelRange_gt hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, hbrk]

/-- A model loop that may stop early: from index `i`, at most `k` steps; a step returns
    `.inl s` to go on and `.inr s` to stop with `s`, or fails. -/
def brkFold {S} (m : Nat → S → Option (S ⊕ S)) : Nat → Nat → S → Option S
  | _, 0, s => some s
  | i, k + 1, s => (m i s).bind (fun r => match r with
      | .inl s' => brkFold m (i + 1) k s'
      | .inr s' => some s')

/-- An ascending loop `for i = fromN to n − 1` (`fromN < n`) that may break and whose
    iterations may trap, against `brkFold`. `after` must not depend on the index. -/
theorem loop_brk_opt {S α ρ β} (E : S → α)
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (m : Nat → S → Option (S ⊕ S)) (A : S → Option β) (fromN n : Nat)
    (hlt : fromN < n)
    (hstep : ∀ i s, fromN ≤ i → i < n →
      (step (Int.ofNat i, E s)).toOption = (m i s).map (fun r => match r with
        | .inl s' => if i + 1 = n then .brk (Int.ofNat i, E s') else .cont (Int.ofNat (i + 1), E s')
        | .inr s' => .brk (Int.ofNat i, E s')))
    (hafter : ∀ j s, (after (j, E s)).toOption = A s) (s0 : S) :
    (SudoRt.runLoopOn (Int.ofNat fromN, E s0) (fuelRange (Int.ofNat fromN) (Int.ofNat (n - 1)))
      step after onRet).toOption = (brkFold m fromN (n - fromN) s0).bind A := by
  rw [fuelRange_le (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, n - fromN = k + 1 := ⟨n - fromN - 1, by omega⟩
  rw [show n - 1 - fromN = k by omega, hk]
  induction k generalizing fromN s0 with
  | zero =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt]
    simp only [brkFold]
    cases hm : m fromN s0 with
    | none => rfl
    | some r =>
      cases r with
      | inl s' =>
        simp only [Option.map_some', Option.some_bind, if_pos (show fromN + 1 = n by omega)]
        exact hafter _ s'
      | inr s' => simp only [Option.map_some', Option.some_bind]; exact hafter _ s'
  | succ k ih =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt]
    simp only [brkFold]
    cases hm : m fromN s0 with
    | none => rfl
    | some r =>
      cases r with
      | inl s' =>
        simp only [Option.map_some', Option.some_bind, if_neg (show ¬ fromN + 1 = n by omega)]
        exact ih (fromN + 1) (by omega) (fun i s h1 h2 => hstep i s (by omega) h2) s' (by omega)
      | inr s' => simp only [Option.map_some', Option.some_bind]; exact hafter _ s'

/-- `loop_brk_opt` with an invariant `P i s` (state `s` before iteration `i`), kept by the
    model steps. -/
theorem loop_brk_inv {S α ρ β} (E : S → α)
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (m : Nat → S → Option (S ⊕ S)) (P : Nat → S → Prop) (A : S → Option β) (fromN n : Nat)
    (hlt : fromN < n)
    (hstep : ∀ i s, fromN ≤ i → i < n → P i s →
      (step (Int.ofNat i, E s)).toOption = (m i s).map (fun r => match r with
        | .inl s' => if i + 1 = n then .brk (Int.ofNat i, E s') else .cont (Int.ofNat (i + 1), E s')
        | .inr s' => .brk (Int.ofNat i, E s')))
    (hP : ∀ i s r, fromN ≤ i → i < n → P i s → m i s = some r → P (i + 1) (Sum.elim id id r))
    (hafter : ∀ i j s, i ≤ n → P i s → (after (j, E s)).toOption = A s) (s0 : S)
    (h0 : P fromN s0) :
    (SudoRt.runLoopOn (Int.ofNat fromN, E s0) (fuelRange (Int.ofNat fromN) (Int.ofNat (n - 1)))
      step after onRet).toOption = (brkFold m fromN (n - fromN) s0).bind A := by
  rw [fuelRange_le (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, n - fromN = k + 1 := ⟨n - fromN - 1, by omega⟩
  rw [show n - 1 - fromN = k by omega, hk]
  induction k generalizing fromN s0 with
  | zero =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt h0]
    simp only [brkFold]
    cases hm : m fromN s0 with
    | none => rfl
    | some r =>
      have hr := hP fromN s0 r (Nat.le_refl _) hlt h0 hm
      cases r with
      | inl s' =>
        simp only [Option.map_some', Option.some_bind, if_pos (show fromN + 1 = n by omega)]
        exact hafter _ _ s' (by omega) hr
      | inr s' => simp only [Option.map_some', Option.some_bind]; exact hafter _ _ s' (by omega) hr
  | succ k ih =>
    rw [runLoopOn_succ_opt, hstep fromN s0 (Nat.le_refl _) hlt h0]
    simp only [brkFold]
    cases hm : m fromN s0 with
    | none => rfl
    | some r =>
      have hr := hP fromN s0 r (Nat.le_refl _) hlt h0 hm
      cases r with
      | inl s' =>
        simp only [Option.map_some', Option.some_bind, if_neg (show ¬ fromN + 1 = n by omega)]
        exact ih (fromN + 1) (by omega) (fun i s h1 h2 => hstep i s (by omega) h2)
          (fun i s r h1 h2 => hP i s r (by omega) h2) s' hr (by omega)
      | inr s' => simp only [Option.map_some', Option.some_bind]; exact hafter _ _ s' (by omega) hr

/-- An ascending loop over `[fromN, fromN + k]` on the index alone whose iterations either
    pass or trap (`ok i`): it reaches `after` iff every iteration passes. -/
theorem asc_check {ρ β} (step : Int → Except SudoRt.Trap (SudoRt.Flow Int ρ))
    (after : Int → Except SudoRt.Trap β) (onRet : ρ → Except SudoRt.Trap β)
    (ok : Nat → Bool) (fromN k : Nat)
    (hstep : ∀ i, fromN ≤ i → i ≤ fromN + k → (step (Int.ofNat i)).toOption =
      if ok i then some (if i = fromN + k then .brk (Int.ofNat i) else .cont (Int.ofNat (i + 1)))
      else none) :
    (SudoRt.runLoopOn (Int.ofNat fromN) (k + 1) step after onRet).toOption =
      if (List.range' fromN (k + 1)).all ok then (after (Int.ofNat (fromN + k))).toOption
      else none := by
  induction k generalizing fromN with
  | zero =>
    rw [runLoopOn_succ_opt, hstep fromN (Nat.le_refl _) (by omega)]
    cases hok : ok fromN <;> simp [List.range', hok]
  | succ k ih =>
    rw [runLoopOn_succ_opt, hstep fromN (Nat.le_refl _) (by omega)]
    cases hok : ok fromN
    · simp [List.range', hok]
    · simp only [if_true, if_neg (show fromN ≠ fromN + (k + 1) by omega), Option.some_bind]
      rw [ih (fromN + 1) (fun i h1 h2 => by
        rw [hstep i (by omega) (by omega), show fromN + (k + 1) = fromN + 1 + k by omega])]
      simp only [List.range', List.all_cons, hok, Bool.true_and,
        show fromN + 1 + k = fromN + (k + 1) by omega]

end BsLink2.Link2
