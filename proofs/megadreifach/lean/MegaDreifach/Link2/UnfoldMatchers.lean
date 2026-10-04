/-
  `unfold_matchers`: unfold every matcher application (`f.match_n …`, the auxiliary
  definitions Lean generates for `match`) in the goal, to `casesOn` form.

  Why: proofs that compare an emitted function with a local copy must not name the emit's
  generated matchers. Lean shares a matcher between definitions of the same shape and
  numbers them per module, so a name like `rot_slice.match_2` is an accident of one emit
  (v2) and does not exist in another (v3). This tactic finds them by `isMatcher` instead.
  The new goal is definitionally equal to the old one (`replaceTargetDefEq`; the kernel
  re-checks it). A proof tool only: no definition of the algorithm. Zero sorry.
-/
import Lean

namespace MegaDreifach.Link2

open Lean Meta Elab Tactic in
/-- Unfold every matcher application in the main goal (see the module docstring). -/
elab "unfold_matchers" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    let .const n _ := e.getAppFn | return .done e
    unless ← isMatcher n do return .done e
    match ← unfoldDefinition? e with
    | some e' => return .visit (e'.headBeta)
    | none => return .done e)
  replaceMainGoal [← g.replaceTargetDefEq t']

end MegaDreifach.Link2
