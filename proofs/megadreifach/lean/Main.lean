import MegaDreifach

def main : IO UInt32 := do
  IO.println "MegaDreifach v1 Lean formalization (correctness; pinned to the deprecated v1, not v2)"
  IO.println "Proved: position model + legality (M1),"
  IO.println "        compose assoc / inverse round-trip (M2),"
  IO.println "        digest encoding injective on reachable positions (M3; no unrank),"
  IO.println "        factoradic φ injectivity for n < 2^224 (M4),"
  IO.println "        pad B=28 injectivity and length recovery (M5),"
  IO.println "        DM algebra / 3-solve invariant (M6),"
  IO.println "        HashDeckBody require_permutation (M7),"
  IO.println "        G2 one-card injectivity as a net-distinctness reduction (M8)."
  IO.println "Link 2: Generated.v_Hash = algebraic MD fold on PadWf (v_Hash_refines);"
  IO.println "        8 KATs as v_Hash theorems in lean_lib MegaDreifachHeavy (M13)."
  IO.println "Security layer (MegaDreifach v1; reductions and weaknesses, not a security claim): MD reduction;"
  IO.println "        a kernel-checked IV-anchored Hash collision (SwapCollision)."
  IO.println "Open: concrete 60×52 net distinctness; abs-G2 L2 (M9); phi_inv / v_HashDeck;"
  IO.println "        digest unrank (surjectivity)."
  IO.println "These are correctness / algebraic theorems; sudo = Generated is trusted,"
  IO.println "and nothing here is a bit-security claim (see ANTI_DRIFT.md)."
  MegaDreifach.runVectorChecks
