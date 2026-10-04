-- DO NOT EDIT. Generated from ecbs.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
import Lake
open Lake DSL

package sudo

lean_lib SudoRt
lean_lib Ecbs

@[default_target]
lean_exe ecbs_test where
  root := `ecbs_test
  moreLinkArgs := if System.Platform.isOSX then
    #["-Wl,-rename_segment,__DATA_CONST,__DATA",
      "-Wl,-rpath,@loader_path"]
    else #[]
