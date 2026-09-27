/-
  Axiom audit for the frozen v9 vulnerability-proof package.
  `python3 proofs/doubledeal/check_axioms.py v9-deprecated` runs this file and
  fails if a theorem below depends on an axiom other than propext,
  Classical.choice and Quot.sound (for example `Lean.ofReduceBool`, which
  `native_decide` would add). CI runs it in the doubledeal-v9-deprecated job.
-/
import DoubleDealV9

#print axioms DoubleDealV9.Witness.v9_KC_QH_swap_commutes_on_witness
#print axioms DoubleDealV9.Witness.encrypt_message
#print axioms DoubleDealV9.Witness.encrypt_message_sigma
#print axioms DoubleDealV9.Witness.expand_keys_key
#print axioms DoubleDealV9.Witness.key_is_deck
#print axioms DoubleDealV9.Witness.message_is_deck
#print axioms DoubleDealV9.Glue.encrypt_of_stages
#print axioms DoubleDealV9.Glue.expand_keys_of_passkeys
