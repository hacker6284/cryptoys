-- DO NOT EDIT. Generated from doubledeal_v10.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
import Lake
open Lake DSL

package sudo

lean_lib SudoRt
lean_lib Doubledeal_v10

@[default_target]
lean_exe doubledeal_v10_test where
  root := `doubledeal_v10_test
  moreLinkArgs := if System.Platform.isOSX then
    #["-Wl,-rename_segment,__DATA_CONST,__DATA",
      "-Wl,-rpath,@loader_path"]
    else #[]
