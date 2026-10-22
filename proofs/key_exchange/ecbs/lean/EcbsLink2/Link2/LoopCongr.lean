/-
  Two loop bodies that agree on an invariant give the same run, when the
  invariant is preserved by `cont`. The exit (`brk`, `ret`, or a trap) is
  the same on both sides because the bodies agree there too.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `natIter` does not read the step at fuel 0, and the two steps agree on
    every state that satisfies `Inv`. A `cont` state stays in `Inv`. -/
private theorem natIter_inv {σ ρ : Type}
    (Inv : σ → Prop) (fuel : Nat) (s0 : σ) (hs0 : Inv s0)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (hagree : ∀ s, Inv s → step s = step' s)
    (hpres : ∀ s s', Inv s → step s = .ok (SudoRt.Flow.cont s') → Inv s') :
    SudoRt.natIter (ρ := ρ) fuel step s0 =
      SudoRt.natIter (ρ := ρ) fuel step' s0 := by
  induction fuel generalizing s0 with
  | zero =>
    rfl
  | succ fuel ih =>
    rw [natIter_succ_do, natIter_succ_do, hagree s0 hs0]
    cases hst : step' s0 with
    | error _ =>
      rfl
    | ok fl =>
      cases fl with
      | ret _ =>
        rfl
      | brk _ =>
        rfl
      | cont s' =>
        simp only [ok_bind, pure_eq_ok]
        exact ih s' (hpres s0 s' hs0 ((hagree s0 hs0).trans hst))

/-- Two bodies that agree on every state satisfying `Inv` give the same run,
    when `cont` stays inside `Inv`. -/
theorem runLoopOn_congr {σ ρ α : Type}
    (Inv : σ → Prop) (s0 : σ) (hs0 : Inv s0) (fuel : Nat)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (hagree : ∀ s, Inv s → step s = step' s)
    (hpres : ∀ s s', Inv s → step s = .ok (SudoRt.Flow.cont s') → Inv s')
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ) s0 fuel step' after onRet := by
  rw [runLoopOn_def, runLoopOn_def, natIter_inv Inv fuel s0 hs0 step step' hagree hpres]

/-- What a loop step does, with the `ret` payload erased. Two steps of
    different `ρ` can still drive the same loop when neither returns. -/
inductive LoopAct (σ : Type) where
  | err : SudoRt.Trap → LoopAct σ
  | cont : σ → LoopAct σ
  | brk : σ → LoopAct σ
  | ret : LoopAct σ

def loopAct {σ ρ : Type} : Except SudoRt.Trap (SudoRt.Flow σ ρ) → LoopAct σ
  | .error e => .err e
  | .ok (.cont s) => .cont s
  | .ok (.brk s) => .brk s
  | .ok (.ret _) => .ret

/-- Steps with the same `cont` / `brk` / trap, and no `ret`, give the same
    run. The two `onRet` handlers are not used. -/
theorem runLoopOn_act {σ ρ ρ' α : Type}
    (s0 : σ) (fuel : Nat)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ'))
    (hact : ∀ s, loopAct (step s) = loopAct (step' s))
    (hno : ∀ s r, step s ≠ .ok (SudoRt.Flow.ret r))
    (hno' : ∀ s r, step' s ≠ .ok (SudoRt.Flow.ret r))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α)
    (onRet' : ρ' → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ') s0 fuel step' after onRet' := by
  induction fuel generalizing s0 with
  | zero =>
    rw [runLoopOn_def, runLoopOn_def]
    rfl
  | succ fuel ih =>
    rw [runLoopOn_succ, runLoopOn_succ]
    cases hst : step s0 with
    | error e =>
      cases hst' : step' s0 with
      | error e' =>
        have h := hact s0
        rw [hst, hst'] at h
        simp only [loopAct] at h
        cases h
        rfl
      | ok fl =>
        have h := hact s0
        rw [hst, hst'] at h
        cases fl with
        | ret r =>
          exact absurd hst' (hno' s0 r)
        | brk _ =>
          simp only [loopAct] at h
          cases h
        | cont _ =>
          simp only [loopAct] at h
          cases h
    | ok fl =>
      cases fl with
      | ret r =>
        exact absurd hst (hno s0 r)
      | brk s =>
        cases hst' : step' s0 with
        | error _ =>
          have h := hact s0
          rw [hst, hst'] at h
          simp only [loopAct] at h
          cases h
        | ok fl' =>
          cases fl' with
          | ret r =>
            exact absurd hst' (hno' s0 r)
          | brk s' =>
            have h := hact s0
            rw [hst, hst'] at h
            simp only [loopAct] at h
            cases h
            rfl
          | cont _ =>
            have h := hact s0
            rw [hst, hst'] at h
            simp only [loopAct] at h
            cases h
      | cont s =>
        cases hst' : step' s0 with
        | error _ =>
          have h := hact s0
          rw [hst, hst'] at h
          simp only [loopAct] at h
          cases h
        | ok fl' =>
          cases fl' with
          | ret r =>
            exact absurd hst' (hno' s0 r)
          | brk _ =>
            have h := hact s0
            rw [hst, hst'] at h
            simp only [loopAct] at h
            cases h
          | cont s' =>
            have h := hact s0
            rw [hst, hst'] at h
            simp only [loopAct] at h
            cases h
            exact ih s

end EcbsLink2.Link2
