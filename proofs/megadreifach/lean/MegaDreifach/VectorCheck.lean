/-
  Known-answer *metadata* checks (layer (b) evidence): pad length, block
  count, digest width, and that `msgHex` decodes to `msgLen` bytes.
  Trust base: compiled Lean (`lake exe megadreifach`), not kernel `decide`.
  The digests themselves are proved (M13, done): the heavy library
  `MegaDreifachHeavy/Kat.lean` kernel-checks every
  `v_Hash (embed (hexBytes v.msgHex)) = .ok (embed (hexBytes v.digestHex))`.
-/
import MegaDreifach.Basic
import MegaDreifach.Pad
import MegaDreifach.Vectors
import MegaDreifach.Hex

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
  let ok5 ← check s!"{v.name}.msg_len" (v.msgHex.length == 2 * v.msgLen &&
    (hexBytes v.msgHex).length == v.msgLen)
  let ok6 ← check s!"{v.name}.digest_bytes" ((hexBytes v.digestHex).length == Vectors.digestLen)
  return ok1 && ok2 && ok3 && ok4 && ok5 && ok6

def runVectorChecks : IO UInt32 := do
  IO.println "MegaDreifach KAT metadata (pad / blocks / digest width / message bytes)"
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
