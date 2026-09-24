import TwoDeck

def main : IO Unit := do
  IO.println "TwoDeck Lean correctness formalization"
  IO.println "Proved: layer bijections, Nr=6 round-trip under abstract Compose keys,"
  IO.println "        PassKey content-preservation and injectivity,"
  IO.println "        factoradic permutation,"
  IO.println "        CTR prefix stability, Compose KP uniqueness."
  IO.println "These are correctness / algebraic theorems, not bit-security."
