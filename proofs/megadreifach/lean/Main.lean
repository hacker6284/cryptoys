import MegaDreifach

def main : IO UInt32 := do
  IO.println "MegaDreifach Lean correctness formalization"
  IO.println "Proved: position model + legality (M1),"
  IO.println "        compose assoc / inverse round-trip (M2),"
  IO.println "        digest-rank packing + 29-byte injectivity on in-range ranks (M3),"
  IO.println "        factoradic φ injectivity for n < 2^224 (M4),"
  IO.println "        pad B=28 injectivity and length recovery (M5),"
  IO.println "        DM algebra / 3-solve invariant (M6),"
  IO.println "        HashDeckBody require_permutation (M7),"
  IO.println "        G2 one-card injectivity as a net-distinctness reduction (M8)."
  IO.println "Open: concrete 60×52 net distinctness; abs-G2 L2 (M9); full KAT digests (M13)."
  IO.println "These are correctness / algebraic theorems about the proof-only"
  IO.println "model, not Generated.v_Hash, and not bit-security (see ANTI_DRIFT.md)."
  MegaDreifach.runVectorChecks
