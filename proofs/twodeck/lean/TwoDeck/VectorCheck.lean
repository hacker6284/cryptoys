/-
  Known-answer checks: Lean model vs vectors exported from twodeck.sudo
  (via the sudoc JS target). Trust base is compiled Lean evaluation
  (`lake exe twodeck`), not kernel `decide`. See proofs/twodeck/README.md.
-/
import TwoDeck.Concrete
import TwoDeck.Vectors
import TwoDeck.PassKey
import TwoDeck.Factoradic

namespace TwoDeck

def checkEq (name : String) (got want : List Nat) : IO Bool := do
  if got == want then
    return true
  else
    IO.eprintln s!"FAIL {name}:\n  got  {got}\n  want {want}"
    return false

def checkEq2 (name : String) (got want : List (List Nat)) : IO Bool := do
  if got == want then
    return true
  else
    IO.eprintln s!"FAIL {name}:\n  got  {got}\n  want {want}"
    return false

def tally (acc : Nat × Nat) (ok : Bool) : Nat × Nat :=
  if ok then (acc.1 + 1, acc.2 + 1) else (acc.1, acc.2 + 1)

def checkEncrypt (v : Vectors.EncryptVec) : IO (Nat × Nat) := do
  let c := encryptDeck v.message v.key
  let p := decryptDeck v.cipher v.key
  let okE ← checkEq s!"{v.name}.encrypt" c v.cipher
  let okD ← checkEq s!"{v.name}.decrypt" p v.message
  return tally (tally (0, 0) okE) okD

def checkPassKey (v : Vectors.PassKeyVec) : IO Bool :=
  checkEq v.name (passToKeyCutFallback v.input) v.output

def checkExpand (v : Vectors.ExpandKeysVec) : IO Bool :=
  checkEq2 v.name (expandKeys v.k0) v.keys

def checkCounter (v : Vectors.CounterDeckVec) : IO Bool :=
  checkEq v.name (counterDeck v.nonce v.index) v.deck

def checkMix (v : Vectors.MixColumnsVec) : IO Bool :=
  checkEq v.name (mixColumnsDeck v.input) v.output

def checkSum (v : Vectors.SumRanksVec) : IO Bool :=
  checkEq v.name (sumRanksDeck v.input) v.output

def checkShift (v : Vectors.ShiftRowsVec) : IO Bool :=
  checkEq v.name (shiftRowsDeck v.input) v.output

def checkUnkeyed (v : Vectors.UnkeyedFullVec) : IO Bool :=
  checkEq v.name (unkeyedFullDeck v.input) v.output

def checkCompose (v : Vectors.ComposeVec) : IO Bool :=
  checkEq v.name (composeDeck v.message v.key) v.output

def checkCtr (v : Vectors.CtrEncryptVec) : IO Bool :=
  checkEq2 v.name (ctrEncryptBlocks v.blocks v.key v.nonce) v.output

def foldChecks {α} (f : α → IO Bool) (xs : List α) (acc : Nat × Nat) : IO (Nat × Nat) :=
  xs.foldlM (fun a x => do return tally a (← f x)) acc

def runVectorChecks : IO Nat := do
  let acc := (0, 0)
  let acc ← Vectors.encryptVecs.foldlM (fun a v => do
      let (ok, n) ← checkEncrypt v
      return (a.1 + ok, a.2 + n)) acc
  let acc ← foldChecks checkPassKey Vectors.passkeyVecs acc
  let acc ← foldChecks checkExpand Vectors.expandKeysVecs acc
  let acc ← foldChecks checkCounter Vectors.counterDeckVecs acc
  let acc ← foldChecks checkMix Vectors.mixColumnsVecs acc
  let acc ← foldChecks checkSum Vectors.sumRanksVecs acc
  let acc ← foldChecks checkShift Vectors.shiftRowsVecs acc
  let acc ← foldChecks checkUnkeyed Vectors.unkeyedFullVecs acc
  let acc ← foldChecks checkCompose Vectors.composeVecs acc
  let acc ← foldChecks checkCtr Vectors.ctrEncryptVecs acc
  let (ok, n) := acc
  if ok ≠ n then
    IO.eprintln s!"vector checks: {ok}/{n} passed"
    IO.Process.exit 1
  IO.println s!"vector checks: {ok}/{n} passed (compiled Lean evaluation)"
  return n

end TwoDeck
