/-
  `#audit_all Root`: print the axioms of EVERY theorem declared in a module under
  `Root` (private ones included), then `audited N`. Used by `Axioms.lean`
  (Root = DoubleDealSecurity) and `AxiomsHeavy.lean` (Root = DoubleDealSecurityHeavy);
  then an ERROR for every `.lean` file under `Root/` that this environment did not
  load (so an unimported module cannot escape the audit; errors cannot be spoofed
  by printed output). Must run from the package directory. Parsed by `../check_axioms.py`.
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
  -- every module file under `<root>/` must be loaded in this environment, or the
  -- audit never saw it. Checked here (an error cannot be spoofed by printed output).
  let loaded := env.header.moduleNames.filter (·.getRoot == root)
  let dir : System.FilePath := root.toString
  let files := (← (dir.walkDir : IO _)).filter (·.extension == some "lean")
  if files.isEmpty then logError m!"no module files found under {dir}/ (run from the package directory)"
  for f in files do
    let comps := (f.withExtension "").components
    let m := comps.foldl (fun acc c => Name.str acc c) Name.anonymous
    unless loaded.contains m do
      logError m!"module {m} is not imported by {root}.lean (the audit never loaded it)"
