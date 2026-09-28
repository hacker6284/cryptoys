/-
  Axiom audit for the DoubleDeal top theorems.
  `python3 proofs/doubledeal/check_axioms.py` runs this file and fails if any
  theorem below depends on an axiom other than propext, Classical.choice and
  Quot.sound (for example `sorryAx`, or `Lean.ofReduceBool` from native_decide).
  CI runs it in the doubledeal-lean job.
-/
import DoubleDeal

-- Link 2: emitted functions refine the algebraic model.
#print axioms DoubleDeal.Link2.encrypt_refines
#print axioms DoubleDeal.Link2.full_round_refines
#print axioms DoubleDeal.Link2.final_round_refines
#print axioms DoubleDeal.Link2.mix_columns_refines
#print axioms DoubleDeal.Link2.overflow_seat_refines
#print axioms DoubleDeal.Link2.scan_row_refines
#print axioms DoubleDeal.Link2.sum_ranks_refines
#print axioms DoubleDeal.Link2.index_of_refines

-- Algebraic model: layer bijections and round trip.
#print axioms DoubleDeal.invSumRanksV10_sumRanksV10
#print axioms DoubleDeal.sumRanksV10_invSumRanksV10
-- The @[csimp] lemmas used by compiled evaluation (lake exe doubledeal).
#print axioms DoubleDeal.sumRanksV10_eq_LL
#print axioms DoubleDeal.invSumRanksV10_eq_LL
#print axioms DoubleDeal.invMixColumns_mixColumns
#print axioms DoubleDeal.mixColumns_invMixColumns
#print axioms DoubleDeal.encrypt6_rt
#print axioms DoubleDeal.encrypt6_decrypt6
#print axioms DoubleDeal.encryptDeckFn_decryptDeckFn
