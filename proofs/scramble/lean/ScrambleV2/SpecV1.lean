/-
  The v1 model, written from SPEC "scramble_v1" (superseded), on top of the shared cube,
  moves, Rule B, closer / seat and digest of `ScrambleV2.Spec`. The trace is not modelled.
  Proof-only. No algorithm change.
-/
import ScrambleV2.Spec

namespace ScrambleV2

/-- SPEC `scramble_v1` move table: each nybble is one move (face, quarter turns). -/
def v1Move : Nat → Face × Nat
  | 0 => (.U, 1) | 1 => (.U, 3) | 2 => (.D, 1) | 3 => (.D, 3)
  | 4 => (.L, 1) | 5 => (.L, 3) | 6 => (.R, 1) | 7 => (.R, 3)
  | 8 => (.F, 1) | 9 => (.F, 3) | 10 => (.B, 1) | 11 => (.B, 3)
  | 12 => (.U, 2) | 13 => (.D, 2) | 14 => (.L, 2) | _ => (.R, 2)

def moveV1 (cube : Cube) (n : Nat) : Cube := turnsN (v1Move n).1 (v1Move n).2 cube

/-- A block: its 8 moves, then Rule B. -/
def blockV1 (cube : Cube) (blk : List Nat) : Option Cube := ruleB (blk.foldl moveV1 cube)

/-- SPEC `scramble_v1` pad cycle. -/
def cycleV1 : List Nat := [6, 0, 7, 1, 8, 2, 9, 3]

/-- The first `n` nybbles of the repeated v1 cycle (the emitted `tape_f`). -/
def tapeF (n : Nat) : List Nat := (List.range n).map fun i => cycleV1.getD (i % 8) 0

/-- SPEC `scramble_v1` padding: append the marker `8`; with `n = (8 - (length mod 8)) mod 8`
    append the first `n` nybbles of the cycle; while shorter than 24, append the cycle again.
    After the first two steps the length is a multiple of 8, so "append the cycle while
    shorter than 24" is appending the first `24 - length` nybbles of the repeated cycle. -/
def padV1 (ny : List Nat) : List Nat :=
  let t := ny ++ [8]
  let t := t ++ cycleV1.take ((8 - t.length % 8) % 8)
  t ++ tapeF (24 - t.length)

/-- Walk the complete blocks of 8 nybbles (block `j` is nybbles `8j … 8j+7`); a trailing
    partial block is not walked (a padded tape has none). -/
def walkV1 (cube : Cube) (tape : List Nat) : Option Cube :=
  (List.range (tape.length / 8)).foldlM (fun c j => blockV1 c ((tape.drop (8 * j)).take 8)) cube

/-- The v1 digest of a message: walk the padded tape from the solved cube, seat, read. -/
def digestV1? (msg : List Nat) : Option (List Nat) := do
  let c ← walkV1 solvedCube (padV1 (nybbles msg))
  let c ← seat c
  digestOf c

def digestV1 (msg : List Nat) : List Nat := (digestV1? msg).getD []

end ScrambleV2
