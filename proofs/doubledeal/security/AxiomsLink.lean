/-
  Axiom audit, Mathlib-free side (`DoubleDealSecurityLink`). Separate file:
  it cannot share an environment with Mathlib (PassKey's Function shims).
-/
import DoubleDealSecurityLink

#print axioms DoubleDeal.SecurityLink.keyPos_map_key
#print axioms DoubleDeal.SecurityLink.generated_encrypt_map_iff
#print axioms DoubleDeal.SecurityLink.encryptDeck_KC_KD_not_equivariant
#print axioms DoubleDeal.SecurityLink.generated_encrypt_KC_KD_not_equivariant
