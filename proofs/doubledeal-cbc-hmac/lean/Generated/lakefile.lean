-- DO NOT EDIT. Generated from doubledeal_cbc_hmac.sudo by tools/emit_lean.py.
-- Algorithm source of truth is the .sudo file. Regenerate with
--   proofs/emit_lean.sh
-- This is not a sudo↔Lean semantic-equivalence theorem.
import Lake
open Lake DSL

package sudo

lean_lib SudoRt
lean_lib Megadreifach
lean_lib Doubledeal_cbc_hmac

@[default_target]
lean_exe doubledeal_cbc_hmac_test where
  root := `doubledeal_cbc_hmac_test
  moreLinkArgs := if System.Platform.isOSX then
    #["-Wl,-rename_segment,__DATA_CONST,__DATA",
      "-Wl,-rpath,@loader_path"]
    else #[]
