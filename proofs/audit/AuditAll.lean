/-
  `#audit_all Root`: print the axioms of EVERY theorem declared in a module under
  `Root` (private ones included), then `audited N`; then an ERROR for every `.lean`
  file under `Root/` that this environment did not load (so an unimported module
  cannot escape the audit; errors cannot be spoofed by printed output), and an
  ERROR `DUP n` for every name declared under `Root` that more than one module
  declares (see below). Must run from the package directory.

  The one copy of this command. It lives in its own core-only lake package
  (`proofs/audit`, no Mathlib) so that every audited package can require it by
  path: the DoubleDeal security package (Mathlib) and MegaDreifach
  (dependency-free). Used by their `Axioms.lean` / `AxiomsHeavy.lean`; the output
  is parsed by the single gate `proofs/doubledeal/check_axioms.py`.
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
  -- every name declared under `<root>` must have exactly one declaring module.
  -- Lean 4.14 silently merges an identical theorem imported from two modules, so the
  -- constant table cannot show this; each module's `constNames` still lists it. The
  -- other owner may be outside the roots (an identical redeclaration of a Mathlib or
  -- core name). Skipped: private names (module-local, cannot collide) and reserved
  -- (auto-generated) names, which several modules may generate on demand for the same
  -- definition.
  let mods := env.header.moduleNames.zip env.header.moduleData
  let mut mine : NameSet := {}
  for (mod, d) in mods do
    if mod.getRoot == root then
      for n in d.constNames do
        unless isPrivateName n || isReservedName env n do mine := mine.insert n
  let mut owners : NameMap (Array Name) := {}
  for (mod, d) in mods do
    for n in d.constNames do
      if mine.contains n then owners := owners.insert n ((owners.findD n #[]).push mod)
  for (n, ms) in owners do
    if ms.size > 1 then
      let declaredIn := ", ".intercalate ((ms.map toString).qsort (· < ·)).toList
      logError m!"DUP {n}: declared in more than one module: {declaredIn}"
