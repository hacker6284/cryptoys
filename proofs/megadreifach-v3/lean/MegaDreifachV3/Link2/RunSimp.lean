/-
  The simp set `run_proj`: the `rfl` projections of the run steps (`turnRun`, `countFind`,
  `countRelook`, `countRegisterLooks` onto `g` and the five counters), declared in
  Link2/RunStep.lean. A separate file because a simp attribute must be registered in a module
  imported by the files that use it.
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

register_simp_attr run_proj
