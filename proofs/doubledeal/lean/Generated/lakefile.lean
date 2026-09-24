-- DO NOT EDIT. Generated from doubledeal.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
import Lake
open Lake DSL

package sudo

lean_lib SudoRt
lean_lib Doubledeal

@[default_target]
lean_exe doubledeal_test where
  root := `doubledeal_test
