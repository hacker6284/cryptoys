/-
  `unfold_matchers` / `unfold_matchers at h`: unfold every matcher application
  (`f.match_n …`, the auxiliary definitions Lean generates for `match`) in the goal or in the
  named hypotheses, to `casesOn` form.

  Why: proofs that compare an emitted function with a local copy must not name the emit's
  generated matchers. Lean shares a matcher between definitions of the same shape and
  numbers them per module, so a name like `rot_slice.match_2` is an accident of one emit
  (v2) and does not exist in another (v3). This tactic finds them by `isMatcher` instead.

  It is not restricted to the emitted namespace (`Megadreifach.`): the `at h` use in
  MegaDreifach's PadRef unfolds the matchers of the local copies (`byteCheckStep`, `copyStep`,
  namespace `MegaDreifach.Link2`) so that both sides end in the same `casesOn` form, and a
  version-neutral tool should not hard-code one emit's namespace.

  It fails when a location has no matcher application, so a stale call (after the emit or the
  copy changes shape) is an error, not a silent no-op. Each new goal / hypothesis type is
  definitionally equal to the old one (`replaceTargetDefEq` / `replaceLocalDeclDefEq`; the
  kernel re-checks the proof). A proof tool only: no theorems, no definitions of an
  algorithm (`selfTestSel` exists only for the self-test at the end of this file). Core Lean only, so every package that requires `audit` can use it.
-/
import Lean

namespace UnfoldMatchers

open Lean Meta Elab Tactic

/-- Unfold every matcher application in `e`; the flag says whether any was found. -/
def unfoldIn (e : Expr) : MetaM (Expr × Bool) := do
  let e ← instantiateMVars e
  let changed ← IO.mkRef false
  let e' ← Meta.transform e (post := fun e => do
    let .const n _ := e.getAppFn | return .done e
    unless ← isMatcher n do return .done e
    match ← unfoldDefinition? e with
    | some e' =>
      changed.set true
      return .visit e'.headBeta
    | none => return .done e)
  return (e', ← changed.get)

/-- `unfold_matchers` unfolds every matcher application in the goal; `unfold_matchers at h`
in hypothesis `h` (`at h ⊢`, `at *` as usual). Fails where nothing was unfolded. -/
syntax (name := unfoldMatchers) "unfold_matchers" (Parser.Tactic.location)? : tactic

@[tactic unfoldMatchers] def evalUnfoldMatchers : Tactic := fun stx => do
  let loc := expandOptLocation stx[1]
  withLocation loc
    (atLocal := fun fvar => liftMetaTactic1 fun g => do
      let (t', found) ← unfoldIn (← fvar.getType)
      unless found do
        throwError "unfold_matchers: no matcher application in {mkFVar fvar}"
      return some (← g.replaceLocalDeclDefEq fvar t'))
    (atTarget := liftMetaTactic1 fun g => do
      let (t', found) ← unfoldIn (← g.getType)
      unless found do
        throwError "unfold_matchers: no matcher application in the goal"
      return some (← g.replaceTargetDefEq t'))
    (failed := fun _ => throwError "unfold_matchers: no matcher application found")

/-! Self-test (elaborated with this library): one goal it unfolds, and goals where it must fail. -/

/-- A one-`match` function for the self-test. -/
def selfTestSel (n : Nat) : Bool := match n with | 0 => true | _ => false

example : selfTestSel 0 = true := by
  unfold selfTestSel
  unfold_matchers
  fail_if_success unfold_matchers
  rfl

example (h : (1 : Nat) = 1) : (2 : Nat) = 2 := by
  fail_if_success unfold_matchers at h
  fail_if_success unfold_matchers
  rfl

end UnfoldMatchers
