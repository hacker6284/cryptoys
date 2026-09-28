/-
  Axiom audit for the frozen v10 GridCycle witness package.
  `python3 proofs/doubledeal/check_axioms.py v10-deprecated` runs this file and
  fails if a theorem below depends on an axiom other than propext,
  Classical.choice and Quot.sound (for example `Lean.ofReduceBool`, which a
  native decision procedure would add).
-/
import DoubleDealV10

#print axioms DoubleDealV10.Witness.v10_KC_KD_swap_commutes_with_gridcycle
#print axioms DoubleDealV10.Witness.mix_columns_deck
#print axioms DoubleDealV10.Witness.mix_columns_deck_sigma
#print axioms DoubleDealV10.Witness.deck_is_deck
#print axioms DoubleDealV10.Witness.sigma_moves_mix
