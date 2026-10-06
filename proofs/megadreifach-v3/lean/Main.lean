import MegaDreifachV3

def main : IO UInt32 := do
  IO.println "MegaDreifach v3 (ZP26) Lean package: emitted code from v3/megadreifach.sudo."
  IO.println "Link 2 (separate kernel theorems, MegaDreifachV3.Link2): every export = the hand-written model, under the stated input conditions (README export table)."
  IO.println "This run is a compiled KAT test, not a proof,"
  IO.println "and nothing here is a security claim (see proofs/ANTI_DRIFT.md)."
  MegaDreifachV3.KatRun.run
