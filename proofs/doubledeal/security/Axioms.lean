/-
  Axiom audit, Mathlib side. Run by `python3 ../check_axioms.py security`.

  Prints the axioms of EVERY theorem declared in a `DoubleDealSecurity.*`
  module, private ones included (no hand-written list), then `audited N`. The checker allows only propext,
  Classical.choice and Quot.sound, except that the theorems named in its
  KNOWN_SORRY set (the open conjecture `roundBody_covariant_iff_id` and the two
  theorems that rest on it) may also use `sorryAx`. Any other axiom, any other
  theorem using `sorryAx`, an `axiom` declared in the package (used or not), or
  a stale KNOWN_SORRY entry fails.
-/
import DoubleDealSecurity

open Lean Elab Command in
elab "#audit_all" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    unless (env.header.moduleNames[i.toNat]!).getRoot == `DoubleDealSecurity do continue
    -- compiler auxiliaries (`_elambda`, `_spec`, ...) are internal names;
    -- `private` declarations are audited under their user-facing name
    if ((privateToUserName? n).getD n).isInternal then continue
    if ci matches .axiomInfo _ then
      logInfo m!"'{n}' is an axiom declared in the package"
      continue
    unless ci matches .thmInfo _ do continue
    let axs ← collectAxioms n
    logInfo m!"'{n}' depends on axioms: {axs.toList}"
    count := count + 1
  logInfo m!"audited {count}"

#audit_all
