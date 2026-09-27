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
#print axioms DoubleDeal.invSumRanks_sumRanks
#print axioms DoubleDeal.invMixColumns_mixColumns
#print axioms DoubleDeal.encrypt6_rt
