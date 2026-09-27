/-
  `#audit_all Root`: print the axioms of EVERY theorem declared in a module under
  `Root` (private ones included), then `audited N`. Used by `Axioms.lean`
  (Root = DoubleDealSecurity) and `AxiomsHeavy.lean` (Root = DoubleDealSecurityHeavy);
  parsed by `../check_axioms.py`.
-/
import Lean

open Lean Elab Command in
elab "#audit_all " root:ident : command => do
  let env ← getEnv
  let root := root.getId
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    unless (env.header.moduleNames[i.toNat]!).getRoot == root do continue
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
