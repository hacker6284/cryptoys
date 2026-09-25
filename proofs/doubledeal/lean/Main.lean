import DoubleDeal

def main : IO Unit := do
  IO.println "DoubleDeal Lean correctness formalization"
  IO.println "Proved: layer bijections, Nr=6 round-trip under abstract Compose keys,"
  IO.println "        PassKey content-preservation and injectivity,"
  IO.println "        concrete PassKey schedule inherits encrypt6_rt,"
  IO.println "        factoradic unrankPerm permutes its items (injectivity only for 3!),"
  IO.println "        CTR prefix stability, Compose KP uniqueness."
  IO.println "These are correctness / algebraic theorems about the proof-only"
  IO.println "skeleton, not bit-security. Link 2 refines Generated.encrypt"
  IO.println "on CardBound messages and transfers PassKey S3/S4 onto"
  IO.println "Except Trap (see proofs/LINK2.md), not emitter soundness."
  let _ ← DoubleDeal.runVectorChecks
