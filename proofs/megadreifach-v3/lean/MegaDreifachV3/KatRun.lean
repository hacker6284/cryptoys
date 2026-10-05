/-
  Known-answer check of the emitted v3 code (compiled Lean, `lake exe megadreifach_v3_kat`).

  Runs the functions emitted from primitives/hash/megadreifach/v3/megadreifach.sudo
  (Generated/, module `Megadreifach`) on every vector of
  primitives/hash/megadreifach/kats/megaminx_hash_kats_v3.json (mirrored into
  MegaDreifachV3/Vectors.lean by proofs/megadreifach-v3/vectors/json_to_lean.py) and compares:
  - Hash and its alias MegaDreifach on the 8 messages, and pad_message's length;
  - HashDeck / MegaDreifachDeck on the hash_deck deal, and Hash of 28 zero bytes when the
    file says they match;
  - HashDeckBody / MegaDreifachBody, and HashDeckBodyFrom at IV-COOK12, on all 8 body vectors;
  - position_to_bytes of IV-COOK12 against iv_cook12_digest_hex.

  Trust base: the Lean compiler and runtime, not the kernel. This is a test of the emitted code
  against the published vectors, not a theorem, and nothing here is a security claim. The KAT
  JSON is itself produced from the sudoc JS build of the same .sudo (kats/regen_v3.mjs), so the
  check is JS build vs Lean build of one source, not an independent implementation.
  This file computes no digest itself; the hex decoder below is a test helper.
-/
import Megadreifach
import MegaDreifachV3.Vectors

namespace MegaDreifachV3.KatRun

open Megadreifach

/-- Lower-case hex to bytes (test helper; the generator rejects any other hex). -/
def hexNibble (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def hexBytes (s : String) : Array Int :=
  let rec go : List Char → Array Int → Array Int
    | a :: b :: rest, acc => go rest (acc.push (Int.ofNat (16 * hexNibble a + hexNibble b)))
    | _, acc => acc
  go s.toList #[]

def dealInts (d : Array Nat) : Array Int := d.map Int.ofNat

def showRes (r : Except SudoRt.Trap (Array Int)) : String :=
  match r with
  | .ok a => s!"ok {a.toList}"
  | .error _ => "trap"

def same (r : Except SudoRt.Trap (Array Int)) (want : Array Int) : Bool :=
  match r with
  | .ok a => a == want
  | .error _ => false

def check (name : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then
    IO.println s!"ok   {name}"
  else
    IO.eprintln s!"FAIL {name} {detail}"
  return ok

/-- The number of checks the current KAT file gives (8 messages × 3, hash_deck × 3, 8 body
    vectors × 3, the IV digest). The run fails unless exactly this many ran, so an emptied or
    truncated vector list cannot pass. -/
def expectedChecks : Nat := 52

def run : IO UInt32 := do
  IO.println "MegaDreifach v3 KATs against the compiled emitted code (not a kernel proof)"
  let mut nOk : Nat := 0
  let mut nAll : Nat := 0
  for v in Vectors.vectors do
    let msg := hexBytes v.msgHex
    let want := hexBytes v.digestHex
    let r := v_Hash msg
    for (what, ok, det) in [
        (s!"{v.name}: Hash", same r want, showRes r),
        (s!"{v.name}: MegaDreifach", same (v_MegaDreifach msg) want, ""),
        (s!"{v.name}: pad_message length {v.paddedLen}",
          (match pad_message msg with
           | .ok p => p.size == v.paddedLen && p.size / Vectors.padBlock == v.nBlocks
           | .error _ => false), "")] do
      nAll := nAll + 1
      if ← check what ok det then nOk := nOk + 1
  let hd := Vectors.hashDeck
  let hdWant := hexBytes hd.digestHex
  let deckChecks : List (String × Bool) :=
    [("hash_deck: HashDeck", same (v_HashDeck (dealInts hd.deal)) hdWant),
     ("hash_deck: MegaDreifachDeck", same (v_MegaDreifachDeck (dealInts hd.deal)) hdWant)] ++
    (if Vectors.hashDeckMatchesZero28 then
      [("hash_deck: Hash of 28 zero bytes", same (v_Hash (Array.mkArray 28 0)) hdWant)]
     else [])
  for (what, ok) in deckChecks do
    nAll := nAll + 1
    if ← check what ok then nOk := nOk + 1
  let iv? := iv_cook12
  for b in Vectors.bodyVectors do
    let deal := dealInts b.deal
    let want := hexBytes b.digestHex
    let fromIv := match iv? with
      | .ok iv => same (v_HashDeckBodyFrom deal iv) want
      | .error _ => false
    for (what, ok) in [
        (s!"{b.name}: HashDeckBody", same (v_HashDeckBody deal) want),
        (s!"{b.name}: MegaDreifachBody", same (v_MegaDreifachBody deal) want),
        (s!"{b.name}: HashDeckBodyFrom at IV-COOK12", fromIv)] do
      nAll := nAll + 1
      if ← check what ok then nOk := nOk + 1
  let ivOk := match iv? with
    | .ok iv => same (position_to_bytes iv) (hexBytes Vectors.ivCook12DigestHex)
    | .error _ => false
  nAll := nAll + 1
  if ← check "iv_cook12_digest_hex: position_to_bytes of IV-COOK12" ivOk then nOk := nOk + 1
  IO.println s!"MegaDreifach v3 KATs: {nOk}/{nAll} checks passed"
  if nAll != expectedChecks then
    IO.println s!"FAIL: expected {expectedChecks} checks, ran {nAll} (vector lists changed or empty)"
  return if nOk == nAll && nAll == expectedChecks then 0 else 1

end MegaDreifachV3.KatRun
