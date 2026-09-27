/-
  Axiom audit, Mathlib side (`DoubleDealSecurity`). Run by check_axioms.py.
  While T1 is a draft, the DRAFT-SORRY theorems report `sorryAx` and the gate
  fails on purpose.
-/
import DoubleDealSecurity

-- Proved
#print axioms DoubleDeal.Security.compose_commutes
#print axioms DoubleDeal.Security.shiftRows_commutes
#print axioms DoubleDeal.Security.sumRanks_commutes_of_shift
#print axioms DoubleDeal.Security.v8_shift_iff_rank_preserving
#print axioms DoubleDeal.Security.v8_sumRanks_commutes_of_rank_preserving
#print axioms DoubleDeal.Security.v9_shift_iff
#print axioms DoubleDeal.Security.seat2_inj
#print axioms DoubleDeal.Security.mixColumns_KC_KD_fails
#print axioms DoubleDeal.Security.mixColumns_KC_KS_fails
#print axioms DoubleDeal.Security.v8_mixColumns_KC_KD_fails
#print axioms DoubleDeal.Security.fullRound_commutes
#print axioms DoubleDeal.Security.encryptN_commutes
#print axioms DoubleDeal.Security.v8_rank_preserving_commutes_except_gridCycle
#print axioms DoubleDeal.Security.v8_same_rank_swap_commutes_except_gridCycle
#print axioms DoubleDeal.Security.swap_KC_KD_app
#print axioms DoubleDeal.Security.V8Vectors.mix_columns_identity
#print axioms DoubleDeal.Security.V8Vectors.mix_columns_reverse
#print axioms DoubleDeal.Security.V8Vectors.mix_columns_mul17
#print axioms DoubleDeal.Security.V8Vectors.sum_ranks_mul17
#print axioms DoubleDeal.Security.V8Vectors.unkeyed_full_identity
#print axioms DoubleDeal.Security.V8Vectors.unkeyed_full_reverse
#print axioms DoubleDeal.Security.V8Vectors.unkeyed_full_mul17
#print axioms DoubleDeal.Security.sumRanks_commutes_iff
#print axioms DoubleDeal.Security.v9_sumRanks_commutes_iff
#print axioms DoubleDeal.Security.v9_no_swap_commutes_sumRanks
#print axioms DoubleDeal.Security.sumRanks_shift_of_commutes
#print axioms DoubleDeal.Security.mixColumns_rel_iff_walk
#print axioms DoubleDeal.Security.mixColumns_commutes_iff_id
#print axioms DoubleDeal.Security.v8_mixColumns_commutes_iff_id
#print axioms DoubleDeal.Security.walkW_rel_iff
#print axioms DoubleDeal.Security.walkW_only_id
#print axioms DoubleDeal.Security.seatW_surj
#print axioms DoubleDeal.Security.V8.seat2_eq
#print axioms DoubleDeal.Security.v8_mixColumns_KC_KS_fails
#print axioms DoubleDeal.Security.firstDeck_isDeck
#print axioms DoubleDeal.Security.fullRound_not_commutes_of_stem
#print axioms DoubleDeal.Security.unkeyedNoMix_onto_decks
#print axioms DoubleDeal.Security.unkeyedNoMix_invUnkeyedNoMix
#print axioms DoubleDeal.Security.encrypt6_constKey
#print axioms DoubleDeal.Security.round_of_encrypt6

-- Link 2 transfer (emitted encrypt)
#print axioms DoubleDeal.Security.keyPos_relabel_key
#print axioms DoubleDeal.Security.generated_encrypt_relabel_iff
#print axioms DoubleDeal.Security.encryptDeck_KC_KD_not_equivariant
#print axioms DoubleDeal.Security.generated_encrypt_not_relabel_equivariant

-- Draft (rest on DRAFT-SORRY lemmas)
#print axioms DoubleDeal.Security.fullRound_commutes_iff_id
#print axioms DoubleDeal.Security.encrypt6_commutes_iff_id
