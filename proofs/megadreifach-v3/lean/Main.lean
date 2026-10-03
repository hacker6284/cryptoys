import MegaDreifachV3

def main : IO UInt32 := do
  IO.println "MegaDreifach v3 (ZP26) Lean package: emitted code from v3/megadreifach.sudo."
  IO.println "Link 2 so far: compose, face_move, face_turn, inverse (no export is linked yet)."
  IO.println "This run is a compiled KAT test, not a proof,"
  IO.println "and nothing here is a security claim (see proofs/ANTI_DRIFT.md)."
  MegaDreifachV3.KatRun.run
