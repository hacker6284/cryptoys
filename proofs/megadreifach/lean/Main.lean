import MegaDreifach

def main : IO UInt32 := do
  IO.println "MegaDreifach v2 (C36) Lean formalization (correctness; Generated from megadreifach.sudo v2)"
  IO.println "Proved: position model + legality (M1),"
  IO.println "        compose assoc / inverse round-trip (M2),"
  IO.println "        digest encoding injective on reachable positions (M3; no unrank),"
  IO.println "        factoradic φ injectivity for n < 2^224 (M4),"
  IO.println "        pad B=28 injectivity and length recovery (M5),"
  IO.println "        DM algebra / 3-solve invariant (M6),"
  IO.println "        HashDeckBody require_permutation (M7),"
  IO.println "        G2 one-card injectivity as a net-distinctness reduction (M8)."
  IO.println "Link 2: Generated.v_Hash = algebraic MD fold on PadWf (v_Hash_refines);"
  IO.println "        8 v2 KATs as v_Hash theorems in lean_lib MegaDreifachHeavy (M13)."
  IO.println "Security layer (v2; reductions, not a security claim): MD reduction; step-word / parity lemmas."
  IO.println "The v1 weakness proofs (SwapCollision, CornerDriven, FreeStart) are in the frozen"
  IO.println "        package proofs/deprecated/megadreifach-v1 (namespace MegaDreifachV1)."
  IO.println "Open: concrete 60×52 net distinctness; abs-G2 L2 (M9); v_HashDeck (phi_inv is closed);"
  IO.println "        digest unrank (surjectivity)."
  IO.println "These are correctness / algebraic theorems; sudo = Generated is trusted,"
  IO.println "and nothing here is a bit-security claim (see ANTI_DRIFT.md)."
  MegaDreifach.runVectorChecks
