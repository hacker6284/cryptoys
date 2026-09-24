/-
  Known-answer *metadata* checks (layer (b) evidence).
  Does not evaluate E_m / full Hash — that is M13, still OPEN.
  Trust base: compiled Lean (`lake exe megadreifach`), not kernel `decide`.
-/
import MegaDreifach.Basic
import MegaDreifach.Pad
import MegaDreifach.Vectors

namespace MegaDreifach

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    return true
  else
    IO.eprintln s!"FAIL {name}"
    return false

/-- SHA-2 pad length for a message of `msgLen` bytes, B=28. -/
def expectedPaddedLen (msgLen : Nat) : Nat :=
  msgLen + 1 + padZ msgLen + 8

def checkVec (v : Vectors.HashVec) : IO Bool := do
  let wantPad := expectedPaddedLen v.msgLen
  let ok1 ← check s!"{v.name}.padded_len" (wantPad == v.paddedLen)
  let ok2 ← check s!"{v.name}.n_blocks" (v.paddedLen / Vectors.padBlock == v.nBlocks)
  let ok3 ← check s!"{v.name}.digest_width" (v.digestHex.length == 58) -- 29 bytes hex
  let ok4 ← check s!"{v.name}.pad_mod" (v.paddedLen % Vectors.padBlock == 0)
  return ok1 && ok2 && ok3 && ok4

def runVectorChecks : IO UInt32 := do
  IO.println "MegaDreifach KAT metadata (pad / blocks / digest width)"
  let mut nOk : Nat := 0
  let mut nAll : Nat := 0
  for v in Vectors.vectors do
    let ok ← checkVec v
    nAll := nAll + 1
    if ok then nOk := nOk + 1
  let okG ← check "groupOrder_hex_len" (Vectors.groupOrderHex.length == 59)
  let okI ← check "iv_cook12_hex_width" (Vectors.ivCook12DigestHex.length == 58)
  -- Lean `|G|` decimal, for the exe banner (not a hex parser).
  IO.println s!"  groupOrder (Lean) = {groupOrder}"
  IO.println s!"  groupOrder hex    = {Vectors.groupOrderHex}"
  IO.println s!"  KAT metadata {nOk}/{nAll}; extras {okG && okI}"
  if nOk == nAll && okG && okI then
    return 0
  else
    return 1

end MegaDreifach
