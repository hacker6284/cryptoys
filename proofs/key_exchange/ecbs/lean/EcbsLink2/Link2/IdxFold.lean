/-
  An ascending `runLoopOn` over list indices is the list fold `climbEmit` already
  is. `climbEmit_foldlM` is that fold; this file only connects the emitted index
  loop. The fuel may exceed `fuelRange`: the loop breaks on the last index, so
  the spare is never used. Same `runLoopOn_succ` driver as the other ascending
  loops. The BS `loop_opt` driver is an `Option` refinement of `range'`, not
  this equality.
-/
import EcbsLink2.Link2.ClimbStep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem drop_get_cons (L : List Nat) (k : Nat) (hk : k < L.length) :
    L.drop k = L[k] :: L.drop (k + 1) := by
  induction L generalizing k with
  | nil => cases hk
  | cons a L ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih k (by simp at hk; omega)

theorem drop_isEmpty_eq (L : List Nat) (k : Nat) (hk : k ≤ L.length) :
    (L.drop k).isEmpty = decide (k = L.length) := by
  by_cases h : k = L.length
  · rw [h, List.drop_eq_nil_of_le (Nat.le_refl _)]
    simp
  · have hk' : k < L.length := by
      apply Nat.lt_of_le_of_ne hk
      exact h
    rw [drop_get_cons L k hk', List.isEmpty_cons, decide_eq_false h]

theorem loop_match_brk {σ ρ α} (s : σ) (fuel : Nat)
    (body : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α) (onRet : ρ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => Except.error e
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s) => after s
      | Except.ok (SudoRt.Flow.cont s) => SudoRt.runLoopOn s fuel body after onRet) = after s := rfl

theorem loop_match_cont {σ ρ α} (s : σ) (fuel : Nat)
    (body : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α) (onRet : ρ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => Except.error e
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s) => after s
      | Except.ok (SudoRt.Flow.cont s) => SudoRt.runLoopOn s fuel body after onRet) =
      SudoRt.runLoopOn s fuel body after onRet := rfl

/-- `fuel ≥ fuelRange from to` still breaks on the last index, so the join does
    not depend on the spare. `0 < L.length` keeps `L.length - 1` from saturating. -/
theorem runLoop_drop
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (L : List Nat) (k : Nat) (b : Ecbs.Board)
    (body : Int × Ecbs.Board → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hpos : 0 < L.length) (hk : k ≤ L.length) (fuel : Nat)
    (hfuel : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel)
    (hbody : ∀ i (b : Ecbs.Board) (hi : i < L.length),
      body (Int.ofNat i, b) =
        (step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) >>= fun b' =>
          pure (if (L.drop (i + 1)).isEmpty = true then
            SudoRt.Flow.brk (Int.ofNat i, b')
          else
            SudoRt.Flow.cont (Int.ofNat (i + 1), b'))))
    (hhi : ∀ i (b : Ecbs.Board), L.length ≤ i →
      body (Int.ofNat i, b) = pure (SudoRt.Flow.brk (Int.ofNat i, b)))
    (hafter : ∀ i (b : Ecbs.Board), after (Int.ofNat i, b) = pure b) :
    SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
      climbEmit step b (L.drop k) := by
  have hmain : ∀ d k b fuel,
      L.length - k = d → k ≤ L.length →
      fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel →
      SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
        climbEmit step b (L.drop k) := by
    intro d
    induction d with
    | zero =>
      intro k b fuel hd hk hfuel
      have hk0 : k = L.length := by omega
      have hgt : Int.ofNat (L.length - 1) < Int.ofNat k :=
        (ofNat_lt_iff (L.length - 1) k).mpr (by omega)
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = 1 :=
        fuelRange_gt hgt
      have hone : 1 ≤ fuel := by rw [← hfr]; exact hfuel
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hk0,
        hhi L.length b (Nat.le_refl _), pure_eq_ok]
      change after (Int.ofNat L.length, b) = climbEmit step b (List.drop L.length L)
      rw [hafter, pure_eq_ok, List.drop_eq_nil_of_le (Nat.le_refl _), climbEmit.eq_def]
    | succ d ih =>
      intro k b fuel hd hk hfuel
      have hlt : k < L.length := by omega
      have hleTo : k ≤ L.length - 1 := by omega
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = L.length - k := by
        rw [fuelRange_le hleTo]
        omega
      have hge1 : 1 ≤ fuel := by
        rw [hfr] at hfuel
        omega
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hbody k b hlt]
      have hdrop := drop_get_cons L k hlt
      cases hs : step b (L[k]'hlt) ((L.drop (k + 1)).isEmpty) with
      | error e =>
        rw [hdrop, climbEmit.eq_2, hs]
        rfl
      | ok b' =>
        rw [ok_bind, pure_eq_ok]
        cases hflag : (L.drop (k + 1)).isEmpty
        · have hn : ¬ ((false : Bool) = true) := by decide
          rw [if_neg hn]
          change SudoRt.runLoopOn (Int.ofNat (k + 1), b') (fuel - 1) body after onRet = _
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [hs, ok_bind]
          have hlt1 : k + 1 < L.length := by
            have hk1 : k + 1 ≤ L.length := by omega
            have hdec := drop_isEmpty_eq L (k + 1) hk1
            rw [hflag] at hdec
            have hne : ¬ k + 1 = L.length := by
              intro heq
              rw [heq, decide_eq_true rfl] at hdec
              cases hdec
            omega
          have hnext : L.length - (k + 1) = d := by omega
          have hk1 : k + 1 ≤ L.length := by omega
          have hto : k + 1 ≤ L.length - 1 := by omega
          have hfuel1 :
              fuelRange (Int.ofNat (k + 1)) (Int.ofNat (L.length - 1)) ≤ fuel - 1 := by
            rw [fuelRange_le hto]
            omega
          exact ih (k + 1) b' (fuel - 1) hnext hk1 hfuel1
        · rw [if_pos rfl]
          change after (Int.ofNat k, b') = _
          rw [hafter, pure_eq_ok]
          have hk1 : k + 1 ≤ L.length := by omega
          have hdec := drop_isEmpty_eq L (k + 1) hk1
          rw [hflag] at hdec
          have heq : k + 1 = L.length := by
            simpa [decide_eq_true_eq] using hdec.symm
          have hnil : L.drop (k + 1) = [] := by
            rw [heq]
            exact List.drop_eq_nil_of_le (Nat.le_refl _)
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [hs, ok_bind, hnil, climbEmit.eq_1]
  exact hmain (L.length - k) k b fuel rfl hk hfuel

/-- `runLoop_drop`, with the step equality only where `P i b` holds. An `.ok`
    step must land in `P (i + 1)`. The fuel induction is the same. -/
theorem runLoop_drop_inv
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (L : List Nat) (k : Nat) (b : Ecbs.Board)
    (body : Int × Ecbs.Board → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (P : Nat → Ecbs.Board → Prop)
    (hP : P k b)
    (hpos : 0 < L.length) (hk : k ≤ L.length) (fuel : Nat)
    (hfuel : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel)
    (hbody : ∀ i (b : Ecbs.Board) (hi : i < L.length),
      P i b →
      body (Int.ofNat i, b) =
        (step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) >>= fun b' =>
          pure (if (L.drop (i + 1)).isEmpty = true then
            SudoRt.Flow.brk (Int.ofNat i, b')
          else
            SudoRt.Flow.cont (Int.ofNat (i + 1), b'))))
    (hkeep : ∀ i (b b' : Ecbs.Board) (hi : i < L.length),
      P i b →
      step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) = .ok b' →
      P (i + 1) b')
    (hhi : ∀ i (b : Ecbs.Board), L.length ≤ i →
      body (Int.ofNat i, b) = pure (SudoRt.Flow.brk (Int.ofNat i, b)))
    (hafter : ∀ i (b : Ecbs.Board), after (Int.ofNat i, b) = pure b) :
    SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
      climbEmit step b (L.drop k) := by
  have hmain : ∀ d k b fuel,
      L.length - k = d → k ≤ L.length →
      fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel →
      P k b →
      SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
        climbEmit step b (L.drop k) := by
    intro d
    induction d with
    | zero =>
      intro k b fuel hd hk hfuel _hP
      have hk0 : k = L.length := by omega
      have hgt : Int.ofNat (L.length - 1) < Int.ofNat k :=
        (ofNat_lt_iff (L.length - 1) k).mpr (by omega)
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = 1 :=
        fuelRange_gt hgt
      have hone : 1 ≤ fuel := by rw [← hfr]; exact hfuel
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hk0,
        hhi L.length b (Nat.le_refl _), pure_eq_ok]
      change after (Int.ofNat L.length, b) = climbEmit step b (List.drop L.length L)
      rw [hafter, pure_eq_ok, List.drop_eq_nil_of_le (Nat.le_refl _), climbEmit.eq_def]
    | succ d ih =>
      intro k b fuel hd hk hfuel hP
      have hlt : k < L.length := by omega
      have hleTo : k ≤ L.length - 1 := by omega
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = L.length - k := by
        rw [fuelRange_le hleTo]
        omega
      have hge1 : 1 ≤ fuel := by
        rw [hfr] at hfuel
        omega
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hbody k b hlt hP]
      have hdrop := drop_get_cons L k hlt
      cases hs : step b (L[k]'hlt) ((L.drop (k + 1)).isEmpty) with
      | error e =>
        rw [hdrop, climbEmit.eq_2, hs]
        rfl
      | ok b' =>
        rw [ok_bind, pure_eq_ok]
        cases hflag : (L.drop (k + 1)).isEmpty
        · have hP' : P (k + 1) b' := hkeep k b b' hlt hP hs
          have hn : ¬ ((false : Bool) = true) := by decide
          rw [if_neg hn]
          change SudoRt.runLoopOn (Int.ofNat (k + 1), b') (fuel - 1) body after onRet = _
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [hs, ok_bind]
          have hlt1 : k + 1 < L.length := by
            have hk1 : k + 1 ≤ L.length := by omega
            have hdec := drop_isEmpty_eq L (k + 1) hk1
            rw [hflag] at hdec
            have hne : ¬ k + 1 = L.length := by
              intro heq
              rw [heq, decide_eq_true rfl] at hdec
              cases hdec
            omega
          have hnext : L.length - (k + 1) = d := by omega
          have hk1 : k + 1 ≤ L.length := by omega
          have hto : k + 1 ≤ L.length - 1 := by omega
          have hfuel1 :
              fuelRange (Int.ofNat (k + 1)) (Int.ofNat (L.length - 1)) ≤ fuel - 1 := by
            rw [fuelRange_le hto]
            omega
          exact ih (k + 1) b' (fuel - 1) hnext hk1 hfuel1 hP'
        · rw [if_pos rfl]
          change after (Int.ofNat k, b') = _
          rw [hafter, pure_eq_ok]
          have hk1 : k + 1 ≤ L.length := by omega
          have hdec := drop_isEmpty_eq L (k + 1) hk1
          rw [hflag] at hdec
          have heq : k + 1 = L.length := by
            simpa [decide_eq_true_eq] using hdec.symm
          have hnil : L.drop (k + 1) = [] := by
            rw [heq]
            exact List.drop_eq_nil_of_le (Nat.le_refl _)
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [hs, ok_bind, hnil, climbEmit.eq_1]
  exact hmain (L.length - k) k b fuel rfl hk hfuel hP

/-- `runLoop_drop_inv` when `after` is not the identity. `after` may read the
    board and ignore the index. The result is the fold bound into that tail.
    Same fuel induction; the base case and the last index call `after`. -/
theorem runLoop_drop_inv_bind
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (L : List Nat) (k : Nat) (b : Ecbs.Board)
    (body : Int × Ecbs.Board → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (afterB : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (P : Nat → Ecbs.Board → Prop)
    (hP : P k b)
    (hpos : 0 < L.length) (hk : k ≤ L.length) (fuel : Nat)
    (hfuel : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel)
    (hbody : ∀ i (b : Ecbs.Board) (hi : i < L.length),
      P i b →
      body (Int.ofNat i, b) =
        (step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) >>= fun b' =>
          pure (if (L.drop (i + 1)).isEmpty = true then
            SudoRt.Flow.brk (Int.ofNat i, b')
          else
            SudoRt.Flow.cont (Int.ofNat (i + 1), b'))))
    (hkeep : ∀ i (b b' : Ecbs.Board) (hi : i < L.length),
      P i b →
      step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) = .ok b' →
      P (i + 1) b')
    (hhi : ∀ i (b : Ecbs.Board), L.length ≤ i →
      body (Int.ofNat i, b) = pure (SudoRt.Flow.brk (Int.ofNat i, b)))
    (hafter : ∀ i (b : Ecbs.Board), after (Int.ofNat i, b) = afterB b) :
    SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
      climbEmit step b (L.drop k) >>= afterB := by
  have hmain : ∀ d k b fuel,
      L.length - k = d → k ≤ L.length →
      fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel →
      P k b →
      SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
        climbEmit step b (L.drop k) >>= afterB := by
    intro d
    induction d with
    | zero =>
      intro k b fuel hd hk hfuel _hP
      have hk0 : k = L.length := by omega
      have hgt : Int.ofNat (L.length - 1) < Int.ofNat k :=
        (ofNat_lt_iff (L.length - 1) k).mpr (by omega)
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = 1 :=
        fuelRange_gt hgt
      have hone : 1 ≤ fuel := by rw [← hfr]; exact hfuel
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hk0,
        hhi L.length b (Nat.le_refl _), pure_eq_ok]
      change after (Int.ofNat L.length, b) =
        climbEmit step b (List.drop L.length L) >>= afterB
      rw [hafter, List.drop_eq_nil_of_le (Nat.le_refl _), climbEmit.eq_1, ok_bind]
    | succ d ih =>
      intro k b fuel hd hk hfuel hP
      have hlt : k < L.length := by omega
      have hleTo : k ≤ L.length - 1 := by omega
      have hfr : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) = L.length - k := by
        rw [fuelRange_le hleTo]
        omega
      have hge1 : 1 ≤ fuel := by
        rw [hfr] at hfuel
        omega
      rw [show fuel = (fuel - 1) + 1 from by omega, runLoopOn_succ, hbody k b hlt hP]
      have hdrop := drop_get_cons L k hlt
      cases hs : step b (L[k]'hlt) ((L.drop (k + 1)).isEmpty) with
      | error e =>
        rw [hdrop, climbEmit.eq_2, hs]
        change Except.error e = Except.error e >>= afterB
        rw [error_bind]
      | ok b' =>
        rw [ok_bind, pure_eq_ok]
        cases hflag : (L.drop (k + 1)).isEmpty
        · have hP' : P (k + 1) b' := hkeep k b b' hlt hP hs
          have hn : ¬ ((false : Bool) = true) := by decide
          rw [if_neg hn]
          change SudoRt.runLoopOn (Int.ofNat (k + 1), b') (fuel - 1) body after onRet = _
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [bind_assoc, hs, ok_bind]
          have hlt1 : k + 1 < L.length := by
            have hk1 : k + 1 ≤ L.length := by omega
            have hdec := drop_isEmpty_eq L (k + 1) hk1
            rw [hflag] at hdec
            have hne : ¬ k + 1 = L.length := by
              intro heq
              rw [heq, decide_eq_true rfl] at hdec
              cases hdec
            omega
          have hnext : L.length - (k + 1) = d := by omega
          have hk1 : k + 1 ≤ L.length := by omega
          have hto : k + 1 ≤ L.length - 1 := by omega
          have hfuel1 :
              fuelRange (Int.ofNat (k + 1)) (Int.ofNat (L.length - 1)) ≤ fuel - 1 := by
            rw [fuelRange_le hto]
            omega
          exact ih (k + 1) b' (fuel - 1) hnext hk1 hfuel1 hP'
        · rw [if_pos rfl]
          change after (Int.ofNat k, b') = _
          rw [hafter]
          have hk1 : k + 1 ≤ L.length := by omega
          have hdec := drop_isEmpty_eq L (k + 1) hk1
          rw [hflag] at hdec
          have heq : k + 1 = L.length := by
            simpa [decide_eq_true_eq] using hdec.symm
          have hnil : L.drop (k + 1) = [] := by
            rw [heq]
            exact List.drop_eq_nil_of_le (Nat.le_refl _)
          rw [hdrop, climbEmit.eq_2, hflag]
          rw [hflag] at hs
          rw [hs, ok_bind, hnil, climbEmit.eq_1, ok_bind]
  exact hmain (L.length - k) k b fuel rfl hk hfuel hP

/-- The same loop is the tail-carrying fold `climbEmit_foldlM` already proves.
    `st.2.tail.isEmpty` is `i = L.length - 1` for the element at that index.
    The loop's `after` returns the board, which is the pair's first component. -/
theorem runLoop_foldl
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (L : List Nat) (k : Nat) (b : Ecbs.Board)
    (body : Int × Ecbs.Board → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (after : Int × Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (hpos : 0 < L.length) (hk : k ≤ L.length) (fuel : Nat)
    (hfuel : fuelRange (Int.ofNat k) (Int.ofNat (L.length - 1)) ≤ fuel)
    (hbody : ∀ i (b : Ecbs.Board) (hi : i < L.length),
      body (Int.ofNat i, b) =
        (step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) >>= fun b' =>
          pure (if (L.drop (i + 1)).isEmpty = true then
            SudoRt.Flow.brk (Int.ofNat i, b')
          else
            SudoRt.Flow.cont (Int.ofNat (i + 1), b'))))
    (hhi : ∀ i (b : Ecbs.Board), L.length ≤ i →
      body (Int.ofNat i, b) = pure (SudoRt.Flow.brk (Int.ofNat i, b)))
    (hafter : ∀ i (b : Ecbs.Board), after (Int.ofNat i, b) = pure b) :
    SudoRt.runLoopOn (Int.ofNat k, b) fuel body after onRet =
      ((L.drop k).foldlM (fun (st : Ecbs.Board × List Nat) r => do
          let b' ← step st.1 r st.2.tail.isEmpty
          pure (b', st.2.tail)) (b, L.drop k)).bind (fun st => pure st.1) := by
  rw [climbEmit_foldlM, runLoop_drop step L k b body after onRet hpos hk fuel hfuel hbody hhi hafter]
  cases h : climbEmit step b (L.drop k) with
  | error e => simp [h, Except.map, Except.bind]
  | ok b' =>
    simp [h, Except.map, pure_eq_ok, Except.bind]

end EcbsLink2.Link2
