#!/usr/bin/env python3
"""Axiom gate for the Lean proof packages (the single gate: DoubleDeal and MegaDreifach).

    python3 proofs/doubledeal/check_axioms.py            # core package (lean/)
    python3 proofs/doubledeal/check_axioms.py security   # Mathlib package (security/)
    python3 proofs/doubledeal/check_axioms.py security-heavy  # heavy library (after
                                          # `lake build DoubleDealSecurityHeavy`)
    python3 proofs/doubledeal/check_axioms.py v9-deprecated  # frozen v9 witness package
    python3 proofs/doubledeal/check_axioms.py v10-deprecated # frozen v10 GridCycle witness
    python3 proofs/doubledeal/check_axioms.py megadreifach   # proofs/megadreifach/lean (default lib)
    python3 proofs/doubledeal/check_axioms.py megadreifach-heavy  # its heavy library (after
                                          # `lake build MegaDreifachHeavy`)
    python3 proofs/doubledeal/check_axioms.py megadreifach-v1-deprecated  # frozen v1 package
                                          # (proofs/deprecated/megadreifach-v1/lean)
    python3 proofs/doubledeal/check_axioms.py cbc-hmac-v1-deprecated  # frozen v1 package
                                          # (proofs/deprecated/doubledeal-cbc-hmac-v1/lean,
                                          # DoubleDeal-CBC-HMAC v1 Link 2)
    python3 proofs/doubledeal/check_axioms.py megadreifach-v3  # MegaDreifach v3 package
                                          # (proofs/megadreifach-v3/lean)
    python3 proofs/doubledeal/check_axioms.py scramble  # proofs/scramble/lean
                                          # (Scramble Link 2: v2 and v1 digest paths)
    python3 proofs/doubledeal/check_axioms.py bs  # proofs/key_exchange/bs/lean
                                          # (BS Link 2: arithmetic, walk, check, exchange)
    python3 proofs/doubledeal/check_axioms.py ecbs  # proofs/key_exchange/ecbs/lean
                                          # (ECBS Link 2: tier, coordinate, band, keypad)

Runs `lake env lean Axioms.lean` in the package (after `lake build`) and parses
the "'X' depends on axioms: [...]" reports. Allowed: propext, Classical.choice,
Quot.sound. Anything else (sorryAx, Lean.ofReduceBool from native_decide, a user
axiom) fails, as does a Lean error.

- core: audits the theorems listed with `#print axioms` in lean/Axioms.lean;
  each listed theorem must be reported.
- v9-deprecated: like core, for proofs/deprecated/doubledeal-v9/lean/Axioms.lean
  (the kernel-checked K♣↔Q♥ witness on the emitted frozen v9 encrypt).
- v10-deprecated: like core, for proofs/deprecated/doubledeal-v10/lean/Axioms.lean
  (the kernel-checked single-deck K♣↔K♦ witness on the emitted frozen v10 mix_columns).
- security: security/Axioms.lean audits EVERY theorem declared in a
  `DoubleDealSecurity.*` module, private ones included (`#audit_all`), and the
  parsed report count must equal the `audited N` line Lean prints. KNOWN_SORRY (names
  that may also use `sorryAx`) is EMPTY for this package, so no theorem may use
  `sorryAx`. A KNOWN_SORRY entry that is not reported, or no longer uses sorryAx, fails
  (stale allowlist); so does any `axiom` declared in the package, used or not.
- security-heavy: security/AxiomsHeavy.lean audits every theorem declared in a
  `DoubleDealSecurityHeavy.*` module (the heavy kernel witnesses, not a default
  build target), with the same rules and no KNOWN_SORRY. Every theorem declared in
  security/DoubleDealSecurityHeavy/ must be listed in HEAVY_THEOREMS and vice versa
  (checked in both security modes, so the default job cannot silently drop the
  heavy target), and every listed theorem must be reported by the heavy audit.
  The heavy audit also checks the Lean-generated theorems (e.g. equation lemmas) of
  those modules, which have no source declaration and are pinned in HEAVY_GENERATED:
  every audited theorem not in HEAVY_THEOREMS must be in HEAVY_GENERATED, and every
  HEAVY_GENERATED entry must be audited (so a theorem the source scan misses fails
  instead of passing as generated).
- megadreifach / megadreifach-heavy: like security / security-heavy (mode "all",
  no KNOWN_SORRY) for proofs/megadreifach/lean, roots `MegaDreifach` and
  `MegaDreifachHeavy`. Its heavy source must declare the 8 headline `kat_*`
  theorems (MD_HEAVY_THEOREMS; the `step_*` / `alg_*` helpers need not be listed),
  checked in both modes.
- megadreifach-v1-deprecated: like megadreifach (mode "all", key "full") for the
  frozen v1 package proofs/deprecated/megadreifach-v1/lean (root `MegaDreifachV1`);
  required: the theorems its README cites (MD_V1_README_THEOREMS).
- megadreifach-v3: like megadreifach-v1-deprecated (mode "all", key "full", no KNOWN_SORRY)
  for proofs/megadreifach-v3/lean (root `MegaDreifachV3`); required: the theorems its
  README cites (MD_V3_README_THEOREMS); min is the audited count (355).
  `--selftest` checks its "Emitted function" column against
  primitives/hash/megadreifach/v3/megadreifach.sudo (LINK2_EXPORT_TABLES).
- cbc-hmac-v1-deprecated: like megadreifach (mode "all", key "full", no KNOWN_SORRY) for
  the frozen v1 package proofs/deprecated/doubledeal-cbc-hmac-v1/lean (root
  `DoubleDealCbcHmac`, the v1 Link 2 package, superseded by DoubleDeal-CBC-Sandwich v2);
  required: the Link 2 theorem of every exported function of the frozen
  v1/doubledeal_cbc_hmac.sudo (CBC_HMAC_LINK2).
  `--selftest` also requires every `export func` of the package's sudo to appear in
  its README's "Emitted function" column, and only exports there (LINK2_EXPORT_TABLES).
- scramble: like cbc-hmac-v1-deprecated (mode "all", key "full", no KNOWN_SORRY) for
  proofs/scramble/lean (root `ScrambleV2`, the Scramble Link 2 package: v2 digest-only
  and traced headlines, several updates, v1 digest-only; trace step fields, not letters);
  required: the theorems proofs/scramble/README.md cites
  (SCRAMBLE_LINK2). `--selftest` checks its "Emitted function" column against
  primitives/hash/scramble/scramble.sudo too (LINK2_EXPORT_TABLES).
- bs: like scramble (mode "all", key "full", no KNOWN_SORRY) for
  proofs/key_exchange/bs/lean (root `BsLink2`, the BS Link 2 package); required: the
  theorems proofs/key_exchange/bs/lean/README.md cites (BS_LINK2). `--selftest` checks
  its "Emitted function" column against primitives/key_exchange/bs/bs.sudo
  (LINK2_EXPORT_TABLES).

`#audit_all` is the one command in the core-only package proofs/audit (required by
path by both the security package and MegaDreifach); in mode "all" this script
builds it (`lake build AuditAll`) before running the audit file.

Keying. By default reports are keyed by the user-facing name (a `private` theorem
under the name it is written with), and a private/public collision fails. With
`"key": "full"` they are keyed by the full constant name instead, so private
theorems of the same user name in different modules stay distinct constants.
MegaDreifach needs this: Lean generates private match-equation theorems
(`<def>.match_1.eq_1`, for Generated definitions) on demand in each module that
unfolds them, and a few modules keep small private helpers of the same name.
A public theorem whose name is also the user name of a private one fails in BOTH
keyings (a private copy of a public lemma, or two different lemmas under one
name); only private/private collisions are tolerated under `"key": "full"`.
Public names cannot collide with each other either way (Lean rejects them in one
environment, and `#audit_all` reports an identical re-declaration as `DUP`).

    python3 proofs/doubledeal/check_axioms.py --selftest   # keying rules on synthetic reports
    python3 proofs/doubledeal/check_axioms.py --selftest-lean  # Lean elaborates the source-scan
                          # fixture; its theorem names must equal the scanner's (needs `lean`)
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parent
# Every theorem/lemma the source scan (`heavy_source_theorems`) finds in
# security/DoubleDealSecurityHeavy/ (checked against the source in both security modes;
# audited by `security-heavy`).
# The heavy audit (`#audit_all`: every theorem constant of a DoubleDealSecurityHeavy.*
# module) also reports theorems with no source declaration: Lean-generated ones (e.g.
# equation lemmas), which Lean creates on demand when a proof unfolds a definition
# (`simp only [f, ...]` creates `f.eq_1`) and stores in that proof's module. They are
# pinned in HEAVY_GENERATED (after this set); `security-heavy` fails on an audited
# theorem in neither set and on a HEAVY_GENERATED entry it does not audit. Like every
# audited theorem they must still use only the allowed axioms.
HEAVY_DIR = ROOT / "security" / "DoubleDealSecurityHeavy"
HEAVY_THEOREMS = {
    "DoubleDeal.Security.realKey_enc_id",
    "DoubleDeal.Security.realKey_enc_v10Sym10",
    "DoubleDeal.Security.realKey_enc_v10Sym01",
    "DoubleDeal.Security.realKey_enc_v10Sym02",
    "DoubleDeal.Security.realKey_enc_v10Sym03",
    "DoubleDeal.Security.v10Sym10_not_commutes_realE",
    "DoubleDeal.Security.v10Sym01_not_commutes_realE",
    "DoubleDeal.Security.v10Sym02_not_commutes_realE",
    "DoubleDeal.Security.v10Sym03_not_commutes_realE",
    "DoubleDeal.Security.generated_encrypt_realKey_not_v10Sym_equivariant",
    # DoubleDealSecurityHeavy/GridCycleSurvival.lean (GridCycle survival of v10Sym 0 3)
    "DoubleDeal.Security.GridCycleSurvival.of_chunks",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_0",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_1",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_2",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KC_3",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_0",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_1",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_2",
    "DoubleDeal.Security.GridCycleSurvival.chunk_KS_3",
    "DoubleDeal.Security.GridCycleSurvival.check3_KC",
    "DoubleDeal.Security.GridCycleSurvival.check3_KS",
    "DoubleDeal.Security.GridCycleSurvival.gc_survival_v10Sym03_le",
    "DoubleDeal.Security.GridCycleSurvival.gc_survival_v10Sym_le",
    # DoubleDealSecurityHeavy/TrailBound.lean (unconditional multi-round characteristic bounds)
    "DoubleDeal.Security.TrailBound.trail_card_le_64",
    "DoubleDeal.Security.TrailBound.trail_card_le_4420_v10Sym",
    # DoubleDealSecurityHeavy/RealSchedule.lean (real PassKey schedule; one round's bound)
    "DoubleDeal.Security.RealSchedule.realTrail_card_le_64",
    # DoubleDealSecurityHeavy/Differential.lean (paths inside v10Sym only; not the differential)
    "DoubleDeal.Security.Differential.staysInV10_card_le_4420",
    "DoubleDeal.Security.Differential.realStaysInV10_card_le_4420",
    "DoubleDeal.Security.FullCipher.fullTrail_card_le_4420_v10Sym",
    "DoubleDeal.Security.FullCipher.fullTrail_card_le_64",
    "DoubleDeal.Security.FullCipher.fullStaysInV10_card_le_4420",
    "DoubleDeal.Security.FullCipher.realFullTrail_card_le_64",
    "DoubleDeal.Security.FullCipher.realFullStaysInV10_card_le_4420",
    # DoubleDealSecurityHeavy/CovariantNarrow.lean and the generated CovariantNarrowChecks.lean
    # (pair_ok_*, cell0PairsCheck_ok, check_e*, checks_all: cell0_witness.py --lean): the
    # covariant round statement for every transposition, and the reduction to the
    # remaining prime-order case. The pair list is cell0Pairs (CovariantNarrowLists.lean).
    *(f"DoubleDeal.Security.CovariantNarrow.pair_ok_{i}_{j}"
      for i, j in ((1, 2), (1, 3), (1, 5), (1, 8), (1, 12), (1, 34))),
    "DoubleDeal.Security.CovariantNarrow.cell0PairsCheck_ok",
    *(f"DoubleDeal.Security.CovariantNarrow.check_e{e}" for e in range(1, 52)),
    "DoubleDeal.Security.CovariantNarrow.checks_all",
    "DoubleDeal.Security.CovariantNarrow.cov0Checks_ok",
    "DoubleDeal.Security.CovariantNarrow.roundBody_not_covariant_swap",
    "DoubleDeal.Security.CovariantNarrow.roundBody_not_commutes_swap",
    "DoubleDeal.Security.CovariantNarrow.roundBody_covariant_iff_id_of_prime_nonswap",
    "DoubleDeal.Security.CovariantNarrow.prime_nonswap_case_iff",
    # DoubleDealSecurityHeavy/CovariantAffine.lean and the generated CovariantAffineChecks.lean
    # (check_lin_k_g for the 71 (k, g) != (0, 0), lin_checks_all: aff_witness.py --lean): the
    # covariant round statement for the 3692 affine relabellings outside v10Sym (the
    # normalizer of v10Sym minus v10Sym; true by the holomorph count, not a Lean theorem)
    *(f"DoubleDeal.Security.CovariantAffine.check_lin_{n // 6}_{n % 6}" for n in range(1, 72)),
    "DoubleDeal.Security.CovariantAffine.lin_checks_all",
    "DoubleDeal.Security.CovariantAffine.affChecks_ok",
    "DoubleDeal.Security.CovariantAffine.not_cell0Cov_lin",
    "DoubleDeal.Security.CovariantAffine.roundBody_not_covariant_affine",
    "DoubleDeal.Security.CovariantAffine.roundBody_not_covariant_affine_right",
    "DoubleDeal.Security.CovariantAffine.roundBody_covariant_affine_iff",
    # DoubleDealSecurityHeavy/RankPartition.lean and the generated RankPartitionChecks.lean
    # (fam_struct_D, fam_c0_D_k_i: rank_family.py --lean): a sigma with Cell0Cov sigma tau
    # (in particular every covariant sigma) permutes the 13 rank classes; one step toward
    # PrimeNonSwapCase, NOT the covariant round statement
    *(f"DoubleDeal.Security.RankPartition.fam_struct_{d}" for d in range(3)),
    *(f"DoubleDeal.Security.RankPartition.fam_c0_{n // 9}_{n // 3 % 3}_{n % 3}"
      for n in range(27)),
    "DoubleDeal.Security.RankPartition.fam_c0_all",
    "DoubleDeal.Security.RankPartition.rankChecks_ok",
    "DoubleDeal.Security.RankPartition.cell0Cov_rank",
    "DoubleDeal.Security.RankPartition.cell0Cov_rank_iff",
    "DoubleDeal.Security.RankPartition.covariant_rank",
    "DoubleDeal.Security.RankPartition.cell0Subgroup_le_rankStab",
    # DoubleDealSecurityHeavy/V10Sym.lean and the generated V10SymChecks.lean (aff_struct,
    # aff_c0_k_i, tau_g0_i, tau_cand_l, lab_struct, lab_kill_e: v10sym_witness.py --lean):
    # every sigma with Cell0Cov sigma tau is a v10Sym and tau = sigma, hence
    # roundBody_covariant_iff_id (not stated in the default library) and the unconditional
    # fullRound_commutes_iff_id and encrypt6_commutes_iff_id (from the default-library
    # _of_covariant reductions)
    "DoubleDeal.Security.RankAffine.aff_struct",
    *(f"DoubleDeal.Security.RankAffine.aff_c0_{n // 3}_{n % 3}" for n in range(9)),
    "DoubleDeal.Security.RankAffine.aff_c0_all",
    "DoubleDeal.Security.RankAffine.affRankChecks_ok",
    *(f"DoubleDeal.Security.TauEq.tau_g0_{i}" for i in range(2)),
    *(f"DoubleDeal.Security.TauEq.tau_cand_{l}" for l in range(1, 13)),
    "DoubleDeal.Security.TauEq.tau_cand_all",
    "DoubleDeal.Security.TauEq.tauChecks_ok",
    "DoubleDeal.Security.LabelStep.lab_struct",
    *(f"DoubleDeal.Security.LabelStep.lab_kill_{e}" for e in range(1, 4)),
    "DoubleDeal.Security.LabelStep.lab_kill_all",
    "DoubleDeal.Security.LabelStep.labelChecks_ok",
    "DoubleDeal.Security.RankAffine.cell0Cov_rk_affine",
    "DoubleDeal.Security.TauEq.cell0Cov_tau",
    "DoubleDeal.Security.LabelStep.v10SymChecks_ok",
    "DoubleDeal.Security.LabelStep.cell0Cov_mem_v10Sym",
    "DoubleDeal.Security.LabelStep.cell0Cov_iff",
    "DoubleDeal.Security.roundBody_covariant_iff_id",
    "DoubleDeal.Security.fullRound_commutes_iff_id",
    "DoubleDeal.Security.encrypt6_commutes_iff_id",
    "DoubleDeal.Security.CovariantNarrow.primeNonSwapCase",
}
# Lean-generated theorems of the heavy modules (no source declaration; see the comment
# above HEAVY_THEOREMS). chunkOK.eq_1: `of_chunks` unfolds `chunkOK` with `simp only`.
HEAVY_GENERATED = {
    "DoubleDeal.Security.GridCycleSurvival.chunkOK.eq_1",
    # cell0PairsCheck_ok (generated CovariantNarrowChecks.lean) unfolds `pairsCheck` and
    # `cell0Pairs` with `simp only`.
    "DoubleDeal.Security.CovariantNarrow.pairsCheck.eq_1",
    "DoubleDeal.Security.CovariantNarrow.cell0Pairs.eq_1",
}
# proofs/megadreifach/lean (MegaDreifach v2): the 8 v2 hash KATs in
# MegaDreifachHeavy/Kat.lean. The names match the vectors of
# primitives/hash/megadreifach/kats/megaminx_hash_kats_v2.json, and
# vectors/json_to_lean.py --check checks their statements against the JSON.
MD_LEAN = ROOT.parent / "megadreifach" / "lean"
MD_HEAVY_DIR = MD_LEAN / "MegaDreifachHeavy"

# Every theorem that proofs/megadreifach/README.md cites by name (backticked), resolved
# against the sources of the default library (MegaDreifach v2). Structure fields like
# `cp` / `ep` are not theorem declarations, so they drop out. Rule: a README citation
# must stay present and pass the axiom audit, so renaming or deleting a cited theorem
# fails the default gate.
# `check_axioms.py --selftest` re-derives the list (md_readme_cited) and fails if it
# differs from this set; update both together when the README changes.
MD_README_THEOREMS = {
    "MegaDreifach.G2Cov.g2Step_cov",
    "MegaDreifach.G2Nets.g2Step_fst_ne",
    "MegaDreifach.G2Nets.g2Step_ne",
    "MegaDreifach.G2Nets.net2_ne",
    "MegaDreifach.G2Nets.nets_nodup",
    "MegaDreifach.G2Nets.phiCard_net2_ne",
    "MegaDreifach.G2Nets.twoCard_same_first_ne",
    "MegaDreifach.M9.m9_canon",
    "MegaDreifach.M9.twoCard_diff_first_ne",
    "MegaDreifach.M9.twoCard_ne",
    "MegaDreifach.Link2.abs_reorient_refines",
    "MegaDreifach.Link2.big_add_byte",
    "MegaDreifach.Link2.big_add_nat",
    "MegaDreifach.Link2.big_divmod_nat",
    "MegaDreifach.Link2.big_divmod_small_refines",
    "MegaDreifach.Link2.big_factorial_51",
    "MegaDreifach.Link2.big_factorial_acc3",
    "MegaDreifach.Link2.big_factorial_refines",
    "MegaDreifach.Link2.big_factorial_three",
    "MegaDreifach.Link2.big_factorial_two",
    "MegaDreifach.Link2.big_from_be_byte",
    "MegaDreifach.Link2.big_from_be_limb2",
    "MegaDreifach.Link2.big_from_be_limb2_array",
    "MegaDreifach.Link2.big_from_be_pad",
    "MegaDreifach.Link2.big_from_be_pad_array",
    "MegaDreifach.Link2.big_from_be_short",
    "MegaDreifach.Link2.big_from_be_short_array",
    "MegaDreifach.Link2.big_from_be_zero_pad",
    "MegaDreifach.Link2.big_from_be_zeros",
    "MegaDreifach.Link2.big_from_be_zeros_fromBE",
    "MegaDreifach.Link2.big_mul_acc3",
    "MegaDreifach.Link2.big_mul_gen_refines",
    "MegaDreifach.Link2.big_mul_left_nat",
    "MegaDreifach.Link2.big_mul_left_refines",
    "MegaDreifach.Link2.big_mul_nat",
    "MegaDreifach.Link2.big_mul_nat_gen",
    "MegaDreifach.Link2.big_mul_one",
    "MegaDreifach.Link2.big_mul_one_three",
    "MegaDreifach.Link2.big_mul_three",
    "MegaDreifach.Link2.big_mul_two",
    "MegaDreifach.Link2.big_mul_wide_refines",
    "MegaDreifach.Link2.big_to_be_gen",
    "MegaDreifach.Link2.body_from_refines",
    "MegaDreifach.Link2.body_from_refines_full",
    "MegaDreifach.Link2.chain_loop",
    "MegaDreifach.Link2.colour_on_refines",
    "MegaDreifach.Link2.colours_at_refines",
    "MegaDreifach.Link2.compose_left_cancel",
    "MegaDreifach.Link2.compose_refines",
    "MegaDreifach.Link2.compose_refines_array",
    "MegaDreifach.Link2.corner_after_noon_refines",
    "MegaDreifach.Link2.corner_slot_refines",
    "MegaDreifach.Link2.divmod_cube",
    "MegaDreifach.Link2.divmod_sq",
    "MegaDreifach.Link2.dm_step_refines",
    "MegaDreifach.Link2.edge_colours_at_refines",
    "MegaDreifach.Link2.edge_faces_refines",
    "MegaDreifach.Link2.edge_slot_refines",
    "MegaDreifach.Link2.em_block_refines",
    "MegaDreifach.Link2.even_perm_rank_big_refines",
    "MegaDreifach.Link2.even_perm_rank_big_refines_20",
    "MegaDreifach.Link2.even_perm_rank_big_refines_array",
    "MegaDreifach.Link2.even_perm_rank_big_refines_gen",
    "MegaDreifach.Link2.f3_step_refines",
    "MegaDreifach.Link2.face_turn_refines",
    "MegaDreifach.Link2.fromBE_pad_lt_limb8",
    "MegaDreifach.Link2.g2_step_refines",
    "MegaDreifach.Link2.gripOk_f3Step",
    "MegaDreifach.Link2.gripOk_g2Step",
    "MegaDreifach.Link2.injective_surjective_fin",
    "MegaDreifach.Link2.inverse_refines",
    "MegaDreifach.Link2.iv_cook12_refines",
    "MegaDreifach.Link2.lehmerUnrank_lehmerRank",
    "MegaDreifach.Link2.magCmp_lt_natLimbs",
    "MegaDreifach.Link2.mag_add_limbs",
    "MegaDreifach.Link2.mag_add_nat",
    "MegaDreifach.Link2.mag_cmp_eq",
    "MegaDreifach.Link2.mag_sub_nat",
    "MegaDreifach.Link2.mag_sub_three_le",
    "MegaDreifach.Link2.pack_ori2_refines",
    "MegaDreifach.Link2.pack_ori2_refines_array",
    "MegaDreifach.Link2.pack_ori3_refines",
    "MegaDreifach.Link2.pack_ori3_refines_array",
    "MegaDreifach.Link2.pad_message_refines",
    "MegaDreifach.Link2.pad_message_refines_array",
    "MegaDreifach.Link2.pad_z_refines",
    "MegaDreifach.Link2.peel_leading_51",
    "MegaDreifach.Link2.peel_leading_below",
    "MegaDreifach.Link2.peel_leading_below_digit",
    "MegaDreifach.Link2.peel_leading_cap",
    "MegaDreifach.Link2.peel_leading_cube",
    "MegaDreifach.Link2.peel_leading_factorial",
    "MegaDreifach.Link2.peel_leading_factorial_three",
    "MegaDreifach.Link2.peel_leading_factorial_two",
    "MegaDreifach.Link2.peel_leading_limb",
    "MegaDreifach.Link2.peel_leading_one",
    "MegaDreifach.Link2.peel_leading_one_digit",
    "MegaDreifach.Link2.peel_leading_one_three",
    "MegaDreifach.Link2.peel_leading_one_three_digit",
    "MegaDreifach.Link2.peel_leading_sq",
    "MegaDreifach.Link2.peel_leading_zero",
    "MegaDreifach.Link2.peel_leading_zero_digit",
    "MegaDreifach.Link2.peel_leading_zero_digit_three",
    "MegaDreifach.Link2.peel_leading_zero_three",
    "MegaDreifach.Link2.peel_leading_zero_two",
    "MegaDreifach.Link2.phiChunkStep_51",
    "MegaDreifach.Link2.phiChunkStep_lt",
    "MegaDreifach.Link2.phiInvFind_breaks",
    "MegaDreifach.Link2.phiInvStep_51",
    "MegaDreifach.Link2.phiInvStep_lt",
    "MegaDreifach.Link2.phiUnrank_lehmerRank",
    "MegaDreifach.Link2.phi_chunk_refines",
    "MegaDreifach.Link2.phi_chunk_refines_array",
    "MegaDreifach.Link2.phi_inv_refines",
    "MegaDreifach.Link2.phi_inv_refines_array",
    "MegaDreifach.Link2.position_to_bytes_refines",
    "MegaDreifach.Link2.position_to_bytes_refines_array",
    "MegaDreifach.Link2.position_to_bytes_refines_gen",
    "MegaDreifach.Link2.read_grip_refines",
    "MegaDreifach.Link2.require_permutation_refines",
    "MegaDreifach.Link2.require_permutation_refines_array",
    "MegaDreifach.Link2.spin_about_up_refines",
    "MegaDreifach.Link2.v_HashDeckBody_refines",
    "MegaDreifach.Link2.v_HashDeck_eq_v_Hash",
    "MegaDreifach.Link2.v_HashDeck_refines",
    "MegaDreifach.Link2.v_HashDeck_refines_array",
    "MegaDreifach.Link2.v_HashDeck_two_blocks",
    "MegaDreifach.Link2.v_Hash_eq_hashBlocks",
    "MegaDreifach.Link2.v_Hash_refines",
    "MegaDreifach.Link2.v_Hash_refines_array",
    "MegaDreifach.Link2.v_MegaDreifachDeck_refines",
    "MegaDreifach.Link2.v_MegaDreifach_refines",
    "MegaDreifach.Link2.visual_noon_refines",
    "MegaDreifach.Security.blocks_suffix_free",
    "MegaDreifach.Security.dm_forward_bad_count",
    "MegaDreifach.Security.dm_inverse_bad_count",
    "MegaDreifach.Security.evenRank_inj",
    "MegaDreifach.Security.extract_collision_comp",
    "MegaDreifach.Security.extract_second_preimage_comp",
    "MegaDreifach.Security.f3Step_fst",
    "MegaDreifach.Security.g2Step_fst",
    "MegaDreifach.Security.isLegal_chR",
    "MegaDreifach.Security.isLegal_chainMsg",
    "MegaDreifach.Security.md_collision",
    "MegaDreifach.Security.pad_suffix_free",
    "MegaDreifach.Security.positionToBytes_inj_legal",
    "MegaDreifach.Security.positionToBytes_inj_reachable",
    "MegaDreifach.Security.v_Hash_collision_comp",
    "MegaDreifach.Security.v_Hash_second_preimage_comp",
    "MegaDreifach.Security.word_dmStep",
    "MegaDreifach.Security.word_emBlock",
}

# proofs/deprecated/megadreifach-v1/lean (frozen MegaDreifach v1: the v1 grip-rule weakness
# modules and their import closure, namespace MegaDreifachV1). Every theorem its README
# cites by name; `--selftest` re-derives the list the same way as MD_README_THEOREMS.
MD_V1_LEAN = ROOT.parent / "deprecated" / "megadreifach-v1" / "lean"
MD_V1_README = MD_V1_LEAN.parent / "README.md"
MD_V1_README_THEOREMS = {
    "MegaDreifachV1.Link2.v_Hash_refines",
    "MegaDreifachV1.Security.SwapCollision.v_Hash_swap_collision",
    "MegaDreifachV1.Security.digest_top_collision",
    "MegaDreifachV1.Security.dmStep_collision_of_sq",
    "MegaDreifachV1.Security.dmStep_pseudo_collision",
    "MegaDreifachV1.Security.dmStep_word",
    "MegaDreifachV1.Security.emBlock_word",
    "MegaDreifachV1.Security.foldl_dmBlock_sameCorners",
}

# proofs/megadreifach-v3/lean (MegaDreifach v3, the ZP26 card phase): every theorem its
# README cites by name; `--selftest` re-derives the list the same way as MD_README_THEOREMS.
# Link 2 of all 12 v3 exports (MegaDreifachV3.Link2) and the layers under them.
MD_V3_LEAN = ROOT.parent / "megadreifach-v3" / "lean"
MD_V3_README = MD_V3_LEAN.parent / "README.md"
MD_V3_README_THEOREMS = {f"MegaDreifachV3.Link2.{n}" for n in [
    "compose_refines", "face_move_refines", "face_turn_refines", "inverse_refines",
    "pad_message_refines", "pad_message_refines_array", "require_permutation_refines",
    "require_permutation_refines_array", "position_to_bytes_refines_gen",
    "position_to_bytes_refines", "phi_chunk_refines", "phi_chunk_refines_array",
    "phi_inv_refines", "phi_inv_refines_array",
    "triples_ok", "lowest_nbr_index_refines", "suit_nbrs_refines",
    "edge_face_of_refines", "corner_face_of_refines", "edgeFaceOf_found",
    "cornerFaceOf_found", "corner_cover", "card_edge_found", "card_corner_found",
    "turn_run_refines", "count_find_refines", "count_relook_refines",
    "count_register_looks_refines", "card_colour_refines", "card_step_refines",
    "echo_colour_refines", "em_run_refines", "em_block_refines", "emBlock_inj",
    "dm_step_refines", "dmStep_inj", "injPos_chainPre",
    "iv_cook12_refines", "v_Hash_refines", "v_Hash_refines_array", "v_MegaDreifach_refines",
    "v_HashDeck_refines", "v_HashDeck_refines_array", "v_HashDeck_two_blocks",
    "v_MegaDreifachDeck_refines", "body_from_refines",
    "v_HashDeckBody_refines", "v_MegaDreifachBody_refines", "v_HashDeckBodyFrom_refines",
    "v_MegaDreifachBodyFrom_refines", "v_HashDecksBody_refines", "injPos_decksPre"]} | {f"MegaDreifachV3.Em.{n}" for n in [
    "edgeFaceOf_spec", "cornerFaceOf_spec", "turnedFace_countUp", "turnedFace_king",
    "echoColour_countUp", "cardStep_g_last", "dealFold_g_last", "echoRun_g_last",
    "emBlock_any_counters"]} | {f"MegaDreifachV3.Security.{n}" for n in [
    "dmStep_same_h_iff", "emBlock_eq_of_dmStep_eq", "dmStep_same_h_iff_chainPre",
    "word_emBlock", "word_dmStep", "word_chainPre", "isLegal_chainPre",
    "evenRank_inj", "positionToBytes_inj_legal", "positionToBytes_inj_chainPre",
    "pad_suffix_free", "blocks_suffix_free", "chainPre_eq_chR",
    "chain_block_count", "chain_block_count_le", "vhashAlg_eq_iff",
    "extract_collision_comp", "v_Hash_collision_comp",
    "extract_second_preimage_comp", "v_Hash_second_preimage_comp",
    "compValid_emBlock_of_same_h",
    "edge_read_words_injective", "corner_read_words_injective",
    "emitted_edge_read_word_eq", "emitted_corner_read_word_eq",
    "emitted_edge_read_words_injective", "emitted_corner_read_words_injective",
    "edgeGroup_ok", "cornerGroup_ok"]}

MD_HEAVY_THEOREMS = {f"MegaDreifach.Link2.Kat.kat_{k}" for k in
                     ["empty", "short_abc", "short_one", "edge_27", "edge_28", "edge_29",
                      "multi_56", "multi_100"]}
# proofs/deprecated/doubledeal-cbc-hmac-v1/lean (frozen): the v1 Link 2 theorems, one per
# exported function of primitives/aead/doubledeal-cbc-hmac/v1/doubledeal_cbc_hmac.sudo
# (frozen v1; v2 is DoubleDeal-CBC-Sandwich and has no Link 2 yet) (the generated code equals
# the hand-written model `DoubleDealCbcHmac.Spec` on byte inputs), plus the empty-master
# rejection and the full unpad characterization. Cited by
# proofs/deprecated/doubledeal-cbc-hmac-v1/README.md.
CBC_HMAC_LEAN = ROOT.parent / "deprecated" / "doubledeal-cbc-hmac-v1" / "lean"
CBC_HMAC_LINK2 = {f"DoubleDealCbcHmac.Link2.{n}" for n in [
    "xor_bytes_refines", "hmac_normalize_key_refines", "v_HMAC_refines",
    "v_HMAC_MegaDreifach_refines", "pad_iso7816_refines", "unpad_iso7816_char",
    "unpad_iso7816_refines", "unpad_iso7816_rejects", "mac_input_refines",
    "derive_keys_refines", "derive_keys_empty", "cbc_chain_from_cipher_block_refines",
    "tags_equal_refines"]}
# proofs/scramble/lean (Scramble Link 2; scope in its README): every theorem
# proofs/scramble/README.md cites by name; `--selftest` re-derives the list the same way
# as MD_README_THEOREMS.
SCRAMBLE_LEAN = ROOT.parent / "scramble" / "lean"
SCRAMBLE_LINK2 = {
    "ScrambleV2.Kat.kat_empty",
    "ScrambleV2.Kat.kat_a",
    "ScrambleV2.Kat.kat_A7",
    "ScrambleV2.Kat.kat_hello",
    "ScrambleV2.Kat.kat_cube",
    "ScrambleV2.Link2.digestV2_isSome",
    "ScrambleV2.Link2.reach_solved",
    "ScrambleV2.Link2.reach_quarter",
    "ScrambleV2.Link2.reach_rotate",
    "ScrambleV2.Link2.centerOf_reach",
    "ScrambleV2.Link2.cubieAt_reach",
    "ScrambleV2.Link2.rotateTo_reach",
    "ScrambleV2.Link2.ruleB_reach",
    "ScrambleV2.Link2.turn_cubie_refines",
    "ScrambleV2.Link2.quarter_refines",
    "ScrambleV2.Link2.apply_turns_refines",
    "ScrambleV2.Link2.cross_refines",
    "ScrambleV2.Link2.dot_refines",
    "ScrambleV2.Link2.mul_vec_refines",
    "ScrambleV2.Link2.apply_matrix_refines",
    "ScrambleV2.Link2.reorient_refines",
    "ScrambleV2.Link2.fresh_refines",
    "ScrambleV2.Link2.scramble_v2_refines",
    "ScrambleV2.Link2.scramble_v2_digest_refines",
    "ScrambleV2.Link2.push_step_digest",
    "ScrambleV2.Link2.push_step_traced",
    "ScrambleV2.Link2.do_move_refines",
    "ScrambleV2.Link2.do_rule_digest",
    "ScrambleV2.Link2.apply_v2_symbol_digest",
    "ScrambleV2.Link2.cubie_at_refines",
    "ScrambleV2.Link2.is_center_refines",
    "ScrambleV2.Link2.has_color_refines",
    "ScrambleV2.Link2.hasCode_posed",
    "ScrambleV2.Link2.center_dir_refines",
    "ScrambleV2.Link2.sticker_on_refines",
    "ScrambleV2.Link2.color_char_refines",
    "ScrambleV2.Link2.is_ud_refines",
    "ScrambleV2.Link2.edge_bit_refines",
    "ScrambleV2.Link2.corner_piece_refines",
    "ScrambleV2.Link2.edge_piece_refines",
    "ScrambleV2.Link2.fact_refines",
    "ScrambleV2.Link2.rank_perm_refines",
    "ScrambleV2.Link2.digest_bytes_refines",
    "ScrambleV2.Link2.index_bytes_refines",
    "ScrambleV2.Link2.Reach.index_bytes",
    "ScrambleV2.Link2.Reach.facelets_of",
    "ScrambleV2.Link2.solved_cube_refines",
    "ScrambleV2.Link2.solved_facelets_ok",
    "ScrambleV2.Link2.letter_refines",
    "ScrambleV2.Link2.hex_digit_refines",
    "ScrambleV2.Link2.move_name_refines",
    "ScrambleV2.Link2.pad_v2",
    "ScrambleV2.Link2.padV2_eq",
    "ScrambleV2.Link2.apply_ready_v2_digest",
    "ScrambleV2.Link2.update_v2_digest",
    "ScrambleV2.Link2.finish_digest",
    "ScrambleV2.Link2.evaluate_v2_digest",
    "ScrambleV2.Link2.scramble_v2_digest_refines_digestV2",
    "ScrambleV2.Link2.push_step_gen",
    "ScrambleV2.Link2.do_move_gen",
    "ScrambleV2.Link2.do_rule_gen",
    "ScrambleV2.Link2.apply_v2_symbol_gen",
    "ScrambleV2.Link2.apply_ready_v2_gen",
    "ScrambleV2.Link2.update_v2_gen",
    "ScrambleV2.Link2.finish_gen",
    "ScrambleV2.Link2.evaluate_v2_gen",
    "ScrambleV2.Link2.updates_v2",
    "ScrambleV2.Link2.updates_evaluate_v2",
    "ScrambleV2.Link2.scramble_v2_refines_digestV2",
    "ScrambleV2.Link2.padV2_length",
    "ScrambleV2.Kat.kat_v1_empty",
    "ScrambleV2.Kat.kat_v1_a",
    "ScrambleV2.Kat.kat_v1_A7",
    "ScrambleV2.Kat.kat_v1_hello",
    "ScrambleV2.Kat.kat_v1_cube",
    "ScrambleV2.Link2.apply_v1_block_digest",
    "ScrambleV2.Link2.apply_ready_v1_digest",
    "ScrambleV2.Link2.pad_v1",
    "ScrambleV2.Link2.padV1_eq",
    "ScrambleV2.Link2.update_v1_digest",
    "ScrambleV2.Link2.evaluate_v1_digest",
    "ScrambleV2.Link2.walkV1_append8",
    "ScrambleV2.Link2.scramble_v1_digest_refines",
    "ScrambleV2.Link2.scramble_v1_digest_refines_digestV1",
}

# proofs/key_exchange/bs/lean (BS Link 2; scope in its README): every theorem that README
# cites by name; `--selftest` re-derives the list the same way as MD_README_THEOREMS.
BS_LEAN = ROOT.parent / "key_exchange" / "bs" / "lean"
BS_LINK2 = {
    "BsLink2.Spec.T1_p",
    "BsLink2.Spec.T2_p",
    "BsLink2.Link2.tier_T1_refines",
    "BsLink2.Link2.tier_T2_refines",
    "BsLink2.Link2.tier_T6_wf",
    "BsLink2.Link2.multiply_refines",
    "BsLink2.Link2.tidy_refines",
    "BsLink2.Link2.check_received_refines",
    "BsLink2.Link2.send_public_value_refines",
    "BsLink2.Link2.public_value_refines",
    "BsLink2.Link2.shared_secret_refines",
    "BsLink2.Link2.exchange_agree_of_accepted",
    "BsLink2.Link2.drop_spec",
    "BsLink2.Link2.lay_spec",
    "BsLink2.Link2.pay_toll_spec",
    "BsLink2.Link2.multiply_spec",
    "BsLink2.Link2.slide_spec",
    "BsLink2.Link2.tidy_spec",
    "BsLink2.Link2.cube_spec",
    "BsLink2.Link2.walk_public_spec",
    "BsLink2.Link2.walk_shared_spec",
    "BsLink2.Link2.call_the_shots_spec",
    "BsLink2.Link2.is_trits_spec",
    "BsLink2.Link2.is_empty_spec",
    "BsLink2.Link2.is_lone_white_spec",
    "BsLink2.Link2.eq_embed_toReg",
    "BsLink2.Link2.read_key_spec",
    "BsLink2.Link2.readKey_trits",
    "BsLink2.Link2.expOf_readKey_pos",
    "BsLink2.Link2.expOf_readKey_ge",
    "BsLink2.Link2.length_readKey_le",
    "BsLink2.Link2.ship_holes_spec",
    "BsLink2.Link2.ship_pass_spec",
    "BsLink2.Link2.peg_pass_spec",
    "BsLink2.Link2.public_value_refines_of_read",
    "BsLink2.Link2.shared_secret_refines_of_read",
    "BsLink2.Link2.exchange_cells_refines",
    "BsLink2.Link2.exchange_refines",
    "BsLink2.Link2.exchange_alice_rejects",
    "BsLink2.Link2.exchange_bob_rejects",
    "BsLink2.Link2.dice_refines",
    "BsLink2.Link2.build_key_grid_refines",
    "BsLink2.Link2.build_key_grid_dice",
    "BsLink2.Link2.build_key_grid_wf",
    "BsLink2.Link2.build_spec",
    "BsLink2.Link2.hole_step_spec",
    "BsLink2.Link2.row_step_spec",
    "BsLink2.Link2.throw_row_cup_spec",
    "BsLink2.Link2.grow_until_it_bumps_spec",
    "BsLink2.Link2.build_eq",
    "BsLink2.Link2.build_wf",
    "BsLink2.Link2.growUntilItBumps_room",
    "BsLink2.Spec.TollPi.T6_toll_eq",
    "BsLink2.Spec.TollPi.pi50_le_lower",
    "BsLink2.Spec.TollPi.upper_lt_pi50_succ",
    "BsLink2.Spec.TollPi.lower_lt_upper",
    "BsLink2.Spec.TollPi.floor_eq_pi50",
    "BsLink2.Spec.TollPi.lower_in_bracket",
    "BsLink2.Spec.TollPi.pi50_leading_digits",
}
# Link 2 packages whose README has an "Emitted function" table: every `export func` of
# the sudo must appear (backticked) in that column, and the column must name only
# exports (S6 of the #140 review). MegaDreifach v2 is not listed yet: its README has no
# "Emitted function" column (its Link 2 rows are Stone / Claim / Status). 8 of its 11
# exports have a Link 2 `_refines` theorem (pad_message, require_permutation,
# position_to_bytes, Hash, MegaDreifach, HashDeck, MegaDreifachDeck, HashDeckBody); the
# one-line wrappers MegaDreifachBody, HashDeckBodyFrom and MegaDreifachBodyFrom have
# none. Registering it (wrapper theorems plus an 11-row table) is a planned follow-up.
# Scramble is listed: its table has a row for each of the 8 exports. `scramble_v1_digest`
# has three theorems; the traced `scramble_v1` and the demo's `apply_move` rows say they are
# not claimed (no theorem), so those gaps are in the table rather than silent. BS is listed: its table has a row for each of
# the 11 exports (build_letting_go went with letting go, SPEC §4.2: nobody lets go).
# ECBS is listed: its table has a row for each of the 19 exports. The board machine
# (new_board, place, fold, multiply, the exchange) says it is not claimed.

# proofs/key_exchange/ecbs/lean (ECBS Link 2; scope in its README): every theorem that
# README cites by name. `--selftest` re-derives the list.
ECBS_LEAN = ROOT.parent / "key_exchange" / "ecbs" / "lean"
ECBS_LINK2 = {
    "EcbsLink2.Link2.tier_demo_refines",
    "EcbsLink2.Link2.tier_toy_refines",
    "EcbsLink2.Link2.tier_hobby_refines",
    "EcbsLink2.Link2.tier_serious_refines",
    "EcbsLink2.Link2.tier_rejects",
    "EcbsLink2.Link2.phase_names_refines",
    "EcbsLink2.Link2.op_names_refines",
    "EcbsLink2.Link2.with_script_refines",
    "EcbsLink2.Link2.flip_refines",
    "EcbsLink2.Link2.prefix_refines",
    "EcbsLink2.Link2.is_empty_refines",
    "EcbsLink2.Link2.is_trits_refines",
    "EcbsLink2.Link2.npeg_refines",
    "EcbsLink2.Link2.coordinate_refines",
    "EcbsLink2.Link2.keypad_first_refines",
    "EcbsLink2.Link2.keypad_second_refines",
    "EcbsLink2.Link2.occupied_refines",
    "EcbsLink2.Link2.band_held_refines",
    "EcbsLink2.Link2.band_bench_refines",
    "EcbsLink2.Link2.band_traps",
    "EcbsLink2.Link2.place_refines",
    "EcbsLink2.Link2.put_refines",
    "EcbsLink2.Link2.value_held_refines",
    "EcbsLink2.Link2.value_after_set",
    "EcbsLink2.Link2.home_set_read",
    "EcbsLink2.Link2.laneDest_eq",
    "EcbsLink2.Link2.laneDest2_eq",
    "EcbsLink2.Link2.schoolCol_refines",
    "EcbsLink2.Link2.school_loop_refines",
    "EcbsLink2.Link2.foldGeom_refines",
    "EcbsLink2.Link2.foldGeom_dest",
    "EcbsLink2.Link2.fold_loop_refines",
    "EcbsLink2.Link2.lane_fold_refines",
    "EcbsLink2.Link2.lane_fold_eq",
    "EcbsLink2.Link2.laneFold_high",
    "EcbsLink2.Link2.mulPipeline_spec",
    "EcbsLink2.Link2.mul_refines",
    "EcbsLink2.Link2.mul_refines_nocopy",
    "EcbsLink2.Link2.comb_cell",
    "EcbsLink2.Link2.comb_loop_refines",
    "EcbsLink2.Link2.cube_refines",
    "EcbsLink2.Link2.folded_read",
    "EcbsLink2.Link2.new_board_refines",
    "EcbsLink2.Link2.multiply_refines",
    "EcbsLink2.Link2.cube_number_refines",
    "EcbsLink2.Link2.mulSchool_step",
    "EcbsLink2.Link2.copy_band_refines",
    "EcbsLink2.Link2.settle_off",
    "EcbsLink2.Link2.settle_refines",
}
LINK2_EXPORT_TABLES = {
    "megadreifach-v3": (ROOT.parent.parent / "primitives" / "hash" / "megadreifach" / "v3"
                        / "megadreifach.sudo", MD_V3_README),
    "cbc-hmac-v1-deprecated": (ROOT.parent.parent / "primitives" / "aead" / "doubledeal-cbc-hmac"
                               / "v1" / "doubledeal_cbc_hmac.sudo", CBC_HMAC_LEAN.parent / "README.md"),
    "scramble": (ROOT.parent.parent / "primitives" / "hash" / "scramble" / "scramble.sudo",
                 SCRAMBLE_LEAN.parent / "README.md"),
    "bs": (ROOT.parent.parent / "primitives" / "key_exchange" / "bs" / "bs.sudo",
           BS_LEAN / "README.md"),
    "ecbs": (ROOT.parent.parent / "primitives" / "key_exchange" / "ecbs" / "ecbs.sudo",
             ECBS_LEAN / "README.md"),
}
PACKAGES = {
    "lean": {"dir": ROOT / "lean", "mode": "list", "known_sorry": set(), "min": 1},
    "v9-deprecated": {"dir": ROOT.parent / "deprecated" / "doubledeal-v9" / "lean", "mode": "list",
                      "known_sorry": set(), "min": 1},
    "v10-deprecated": {"dir": ROOT.parent / "deprecated" / "doubledeal-v10" / "lean", "mode": "list",
                       "known_sorry": set(), "min": 1},
    "security": {
        "dir": ROOT / "security",
        "mode": "all",
        # Empty: the package has no sorry. roundBody_covariant_iff_id (formerly the one
        # DRAFT-SORRY) is proved in the heavy library (HEAVY_THEOREMS), with
        # fullRound_commutes_iff_id and encrypt6_commutes_iff_id; the default library has
        # their _of_covariant reductions (required below). Keep in sync with ALLOWED_SORRY
        # in security/checks/scan_sorry.py.
        "known_sorry": set(),
        "min": 100,  # sanity: the audit must actually see the package
        # Headline theorems that must be reported (and axiom-clean) by the audit.
        "required": {
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_le",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_le'",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_threeCycle",
            "DoubleDeal.Security.SumRanksDP.sumRanksV10_survival_lower",
            # CovariantNarrow (roadmap M4): reductions of the covariant round statement
            "DoubleDeal.Security.CovariantNarrow.prime_case_iff",
            "DoubleDeal.Security.CovariantNarrow.roundBody_covariant_iff_id_of_prime",
            "DoubleDeal.Security.CovariantNarrow.not_covariant_swap_of_check",
            "DoubleDeal.Security.CovariantNarrow.prime_nonswap_case_iff_of_check",
            # the consequences of the covariant round statement, as reductions (hypothesis
            # hcov : CovariantOnlyId, a def in Rounds.lean, not audited; unconditional forms in
            # the heavy library, HEAVY_THEOREMS)
            "DoubleDeal.Security.fullRound_commutes_iff_id_of_covariant",
            "DoubleDeal.Security.encrypt6_commutes_iff_id_of_covariant",
            # RankPartition: rank classes are preserved, GIVEN the finite checks RankChecks
            # (discharged in the heavy library); not the covariant round statement
            "DoubleDeal.Security.StemPosition.stemPos_zero",
            "DoubleDeal.Security.StemCoupling.rowRead_congr",
            "DoubleDeal.Security.StemCoupling.agree_row",
            "DoubleDeal.Security.StemCoupling.rowAmts_eq_of_agree",
            "DoubleDeal.Security.rel_permDeck",
            "DoubleDeal.Security.RankPartition.rank_eq_of_family",
            "DoubleDeal.Security.RankPartition.family_of_checks",
            "DoubleDeal.Security.RankPartition.cell0Cov_rank_of_checks",
            "DoubleDeal.Security.RankPartition.cell0Cov_rank_iff_of_checks",
            "DoubleDeal.Security.RankPartition.covariant_rank_of_checks",
            "DoubleDeal.Security.RankPartition.cell0Subgroup_le_rankStab_of_checks",
            # the one home of the v10Sym seat-26 fact and of conjugation (CovariantNarrow)
            "DoubleDeal.Security.CovariantNarrow.cell0Cov_v10Sym",
            "DoubleDeal.Security.CovariantNarrow.v10Sym_mem_cell0Subgroup",
            "DoubleDeal.Security.CovariantNarrow.cell0Cov_conj",
            # RankAffine, TauEq, LabelStep: every sigma with Cell0Cov sigma tau is a v10Sym
            # and tau = sigma, GIVEN the finite checks V10SymChecks (discharged in the heavy
            # library, which proves roundBody_covariant_iff_id from it)
            # the card coordinates (one home: SumRanksV10.lean)
            "DoubleDeal.Security.rk_eq_iff",
            "DoubleDeal.Security.rk_v10Sym",
            "DoubleDeal.Security.rk_v10Sym_inv",
            "DoubleDeal.Security.rk_cardOfRk",
            "DoubleDeal.Security.rank_scaleP",
            "DoubleDeal.Security.crd_ri_lbl",
            "DoubleDeal.Security.ext_crd",
            "DoubleDeal.Security.v10Sym_crd",
            "DoubleDeal.Security.xor4_eq_iff",
            "DoubleDeal.Security.RankPartition.FamilyQ.wsum_eq",
            "DoubleDeal.Security.RankPartition.Family.toQ",
            "DoubleDeal.Security.RankAffine.rk_sum_of_family2",
            "DoubleDeal.Security.RankAffine.family2_of_checks",
            "DoubleDeal.Security.RankAffine.affine_of_second_diff",
            "DoubleDeal.Security.RankAffine.cell0Cov_rk_affine_of_checks",
            "DoubleDeal.Security.TauEq.rowAmts_congr",
            "DoubleDeal.Security.TauEq.cand_of_cell0Cov",
            "DoubleDeal.Security.TauEq.tau_step",
            "DoubleDeal.Security.TauEq.tau_eq_of_rk",
            "DoubleDeal.Security.TauEq.cell0Cov_tau_of_checks",
            "DoubleDeal.Security.LabelStep.colAmt_congr_label",
            "DoubleDeal.Security.LabelStep.conj_tr",
            "DoubleDeal.Security.LabelStep.chain_const",
            "DoubleDeal.Security.LabelStep.c0Row_tr_eq",
            "DoubleDeal.Security.LabelStep.d01_of_cell0",
            "DoubleDeal.Security.LabelStep.tr_const_of_mem",
            "DoubleDeal.Security.LabelStep.perm4_xor",
            "DoubleDeal.Security.LabelStep.rankPres_mem_v10Sym",
            "DoubleDeal.Security.LabelStep.cell0Cov_mem_v10Sym_of_checks",
            "DoubleDeal.Security.LabelStep.cell0Cov_iff_of_checks",
            "DoubleDeal.Security.LabelStep.roundBody_covariant_iff_id_of_checks",
            "DoubleDeal.Security.LabelStep.primeNonSwapCase_of_checks",
            # RealSchedule (roadmap M5): real PassKey schedule
            "DoubleDeal.Security.RealSchedule.masterList_injective",
            "DoubleDeal.Security.RealSchedule.exists_masterList_eq",
            "DoubleDeal.Security.RealSchedule.encryptDeckFn_masterList",
            "DoubleDeal.Security.RealSchedule.card_roundKey",
            "DoubleDeal.Security.RealSchedule.card_image_roundKey_pair",
            "DoubleDeal.Security.RealSchedule.card_image_roundKey_pair_lt",
            "DoubleDeal.Security.RealSchedule.card_roundKey_top_eq",
            "DoubleDeal.Security.RealSchedule.realTrail_card_le_26",
            "DoubleDeal.Security.RealSchedule.realTrail_card_le_64_of_not_v10Sym",
            "DoubleDeal.Security.RealSchedule.realTrail_card_le_64_of_check",
            # TrailBound (roadmap M2): multi-round characteristic, independent keys
            "DoubleDeal.Security.TrailBound.trail_rounds_rel",
            "DoubleDeal.Security.TrailBound.trail_card_le_of_round",
            "DoubleDeal.Security.TrailBound.round_le_26",
            "DoubleDeal.Security.TrailBound.round_le_64_of_check",
            "DoubleDeal.Security.TrailBound.trail_card_le_26",
            "DoubleDeal.Security.TrailBound.trail_card_le_64_of_not_v10Sym",
            "DoubleDeal.Security.TrailBound.trail_card_le_64_of_check",
            "DoubleDeal.Security.TrailBound.trail_card_le_4420_v10Sym_of_check",
            # Differential (roadmap M6): structure only; no numeric bound on the full differential
            "DoubleDeal.Security.Differential.card_trail_le_diffCount",
            "DoubleDeal.Security.Differential.diffCount_zero",
            "DoubleDeal.Security.Differential.diffCount_eq_of_isDeck",
            "DoubleDeal.Security.Differential.diffCount_succ",
            "DoubleDeal.Security.Differential.diffCount_one",
            "DoubleDeal.Security.Differential.sum_dp1Count",
            "DoubleDeal.Security.Differential.sum_diffCount",
            "DoubleDeal.Security.Differential.dp1Count_one_left",
            "DoubleDeal.Security.Differential.diffCount_one_left",
            "DoubleDeal.Security.Differential.dp1Count_to_one",
            "DoubleDeal.Security.Differential.diffCount_to_one",
            "DoubleDeal.Security.Differential.dp1Count_v10Sym_le_agree",
            "DoubleDeal.Security.Differential.dp1Count_v10Sym_eq_zero",
            "DoubleDeal.Security.Differential.dp1Count_v10Sym_v10Sym_eq_zero",
            "DoubleDeal.Security.Differential.staysInV10_iff_trail",
            "DoubleDeal.Security.Differential.staysInV10_card_le_26",
            "DoubleDeal.Security.Differential.staysInV10_card_le_4420_of_check",
            "DoubleDeal.Security.Differential.realStaysInV10_card_le_26",
            "DoubleDeal.Security.Differential.realStaysInV10_card_le_4420_of_check",
            "DoubleDeal.Security.Differential.realDiffCount_one",
            # FullCipher (roadmap M7): whole cipher incl. the final no-mix round; no numeric
            # bound on the full-cipher differential; real schedule: the proof's first mix round only
            "DoubleDeal.Security.FullCipher.encryptN_eq_rounds",
            "DoubleDeal.Security.FullCipher.encryptL_eq",
            "DoubleDeal.Security.FullCipher.encryptN_eq_encryptL",
            "DoubleDeal.Security.FullCipher.encryptDeckFn_masterList_eq",
            "DoubleDeal.Security.generated_encrypt_map2_iff",
            "DoubleDeal.Security.generated_encrypt_rel_iff",
            "DoubleDeal.Security.TrailBound.unkeyedNoMix_rel_iff",
            "DoubleDeal.Security.TrailBound.card_filter_snoc",
            "DoubleDeal.Security.Differential.relDiff_eq_iff",
            "DoubleDeal.Security.Differential.sum_dpCount",
            "DoubleDeal.Security.Differential.sum_dpCount_left",
            "DoubleDeal.Security.FullCipher.finalRound_rel_self_iff",
            "DoubleDeal.Security.FullCipher.dpFCount_self_eq_survivors",
            "DoubleDeal.Security.FullCipher.dpFCount_self_le_64",
            "DoubleDeal.Security.FullCipher.dpFCount_v10Sym",
            "DoubleDeal.Security.FullCipher.dpFCount_to_v10Sym",
            "DoubleDeal.Security.FullCipher.sum_dpFCount",
            "DoubleDeal.Security.FullCipher.sum_dpFCount_left",
            "DoubleDeal.Security.FullCipher.fullTrail_encryptL",
            "DoubleDeal.Security.FullCipher.card_fullTrail",
            "DoubleDeal.Security.FullCipher.card_fullTrail_le",
            "DoubleDeal.Security.FullCipher.card_fullTrail_v10Sym",
            "DoubleDeal.Security.FullCipher.fullTrail_card_le_26",
            "DoubleDeal.Security.FullCipher.fullTrail_card_le_64_of_not_v10Sym",
            "DoubleDeal.Security.FullCipher.fullTrail_card_le_4420_v10Sym_of_check",
            "DoubleDeal.Security.FullCipher.fullTrail_card_le_64_of_check",
            "DoubleDeal.Security.FullCipher.fullDiffCount_eq",
            "DoubleDeal.Security.FullCipher.fullDiffCount_zero",
            "DoubleDeal.Security.FullCipher.exists_fullDiffCount_zero_gt",
            "DoubleDeal.Security.FullCipher.fullDiffCount_le_sup",
            "DoubleDeal.Security.FullCipher.fullDiffCount_v10Sym",
            "DoubleDeal.Security.FullCipher.fullStaysInV10_iff",
            "DoubleDeal.Security.FullCipher.card_fullStaysInV10",
            "DoubleDeal.Security.FullCipher.fullStaysInV10_card_le_26",
            "DoubleDeal.Security.FullCipher.fullStaysInV10_card_le_4420_of_check",
            "DoubleDeal.Security.FullCipher.realFullTrail_card_le_26",
            "DoubleDeal.Security.FullCipher.realFullTrail_card_le_64_of_not_v10Sym",
            "DoubleDeal.Security.FullCipher.realFullTrail_card_le_64_of_check",
            "DoubleDeal.Security.FullCipher.realFullStaysInV10_card_le_26",
            "DoubleDeal.Security.FullCipher.realFullStaysInV10_card_le_4420_of_check",
            "DoubleDeal.Security.FullCipher.generated_encrypt_of_realFullTrail",
            "DoubleDeal.Security.FullCipher.generated_encrypt_of_realFullStaysInV10",
            "DoubleDeal.Security.FullCipher.fullDiffCount_eq_of_isDeck",
            "DoubleDeal.Security.FullCipher.fullDiffCount_one_left",
            "DoubleDeal.Security.FullCipher.fullDiffCount_to_one",
            "DoubleDeal.Security.FullCipher.fullDiffCount_eq_card_beforeFinal",
            # column transfer through the final round: a REDUCTION (the column hypothesis is
            # StemUnion.dpFCount_col_le_64 outside v10Sym); not_col_v10Sym says the route is
            # closed into v10Sym
            "DoubleDeal.Security.FullCipher.fullDiffCount_le_of_col",
            "DoubleDeal.Security.FullCipher.not_col_v10Sym",
            # StemPosition (off-diagonal stem bound, first slice): the stem as a position map and
            # the support gap of gamma^-1 * beta; structure only, no count of decks, no part
            # of the off-diagonal stem bound (helpers srcRow / cmFlat_inj2 are named apart from SumRanksDP.rowOf /
            # SumRanksDP.cmFlat_injective)
            "DoubleDeal.Security.StemPosition.unkeyedNoMix_eq_comp",
            "DoubleDeal.Security.StemPosition.stemPosOf_injective",
            "DoubleDeal.Security.StemPosition.stemPos_injective",
            "DoubleDeal.Security.StemPosition.conj_of_stem_rel",
            "DoubleDeal.Security.StemPosition.seatMap_eq_iff",
            "DoubleDeal.Security.StemPosition.card_seatMap_eq",
            "DoubleDeal.Security.StemPosition.card_fixed_eq",
            "DoubleDeal.Security.StemPosition.card_moved_eq",
            "DoubleDeal.Security.StemPosition.card_moved_cases",
            "DoubleDeal.Security.StemPosition.card_moved_zero_or_ge_four",
            # StemCoupling (off-diagonal stem bound, second slice): decks with a prescribed conjugate
            # q (moving <= 1 position per row) and prescribed row amounts are at most 81/4096
            # of the decks with that conjugate; no bound on dpFCount by itself (the support-4
            # assembly is StemSupportFour below)
            "DoubleDeal.Security.StemCoupling.rowAmts_eq_iff",
            "DoubleDeal.Security.StemCoupling.card_hit_le_three",
            "DoubleDeal.Security.StemCoupling.double_count",
            "DoubleDeal.Security.StemCoupling.card_cond_act_le",
            "DoubleDeal.Security.StemCoupling.coupling",
            # StemSupportFour (off-diagonal stem bound, third slice): the 4-card case of the off-diagonal stem bound,
            # 64 * dpFCount beta gamma <= 52! when gamma^-1 * beta moves exactly 4 cards, and
            # supports 1-3, 5-7 count no deck (support >= 8: StemUnion below)
            "DoubleDeal.Security.StemSupportFour.qPerm_moves_le_one",
            "DoubleDeal.Security.StemSupportFour.ratio_eq_qPerm",
            "DoubleDeal.Security.StemSupportFour.ratio_eq_qPerm_of_support_four",
            "DoubleDeal.Security.StemSupportFour.ratio_moves_le_one_of_support_four",
            "DoubleDeal.Security.StemSupportFour.card_conjSet_le_odd",
            "DoubleDeal.Security.StemSupportFour.card_conjSet_le_two",
            "DoubleDeal.Security.StemSupportFour.sum_card_conjSet_le",
            "DoubleDeal.Security.StemSupportFour.dpFCount_bound_of_support_four",
            "DoubleDeal.Security.StemSupportFour.dpFCount_le_of_support_four",
            "DoubleDeal.Security.StemSupportFour.dpFCount_eq_zero_of_support_lt_eight_ne_four",
            # StemUnion (off-diagonal stem bound, final slice): the support >= 8 case by a
            # union bound (general ratio formula, agreement count, cycle-representative
            # bound); the column bound into gamma outside v10Sym, hence
            # 64 * fullDiffCount <= 52!^(n+2) for alpha != 1 and gamma outside v10Sym
            # (independent keys; the same 1/64 for every n, nothing proved about decay;
            # gamma in v10Sym not covered; not a security claim)
            "DoubleDeal.Security.StemUnion.seatMap_shift",
            "DoubleDeal.Security.StemUnion.ratio_eq_ratioQ",
            "DoubleDeal.Security.StemUnion.exists_rep",
            "DoubleDeal.Security.StemUnion.apply_rep_not_rep",
            "DoubleDeal.Security.StemUnion.two_mul_card_reps_le",
            "DoubleDeal.Security.StemUnion.card_conjSet_le_reps",
            "DoubleDeal.Security.StemUnion.card_agree_eq",
            "DoubleDeal.Security.StemUnion.card_zR_eq",
            "DoubleDeal.Security.StemUnion.card_zC_eq",
            "DoubleDeal.Security.StemUnion.card_params",
            "DoubleDeal.Security.StemUnion.paramCount_check",
            "DoubleDeal.Security.StemUnion.zRows_eq_zR",
            "DoubleDeal.Security.StemUnion.zCols_eq_zC",
            "DoubleDeal.Security.StemUnion.mem_ratioCell",
            "DoubleDeal.Security.StemUnion.dpFCount_le_union",
            "DoubleDeal.Security.StemUnion.dpFCount_le_of_support_ge_eight",
            "DoubleDeal.Security.StemUnion.dpFCount_le_of_ne",
            "DoubleDeal.Security.StemUnion.dpFCount_col_le_64",
            "DoubleDeal.Security.StemUnion.fullDiffCount_le_64",
            # OneRoundDP (roadmap B1, one mix round): any eps_1 < 1 implies the covariant round
            # statement (proved in the heavy library), and on the rows outside v10Sym alone already does; the 51 v10Sym rows
            # are bounded (1/52, and 1/17 for v10Sym 0 3); rows outside v10Sym are NOT proved;
            # not a security claim
            "DoubleDeal.Security.OneRoundDP.dp1Count_eq_of_covPair",
            "DoubleDeal.Security.OneRoundDP.covariant_iff_id_of_dp1_lt",
            "DoubleDeal.Security.OneRoundDP.covariant_iff_id_of_dp1Bound",
            "DoubleDeal.Security.OneRoundDP.scoop_rmFlat",
            "DoubleDeal.Security.OneRoundDP.rmFlat_inj",
            "DoubleDeal.Security.OneRoundDP.mixColumns_seat2",
            "DoubleDeal.Security.OneRoundDP.seat2_ne_start",
            "DoubleDeal.Security.OneRoundDP.seat2Idx_ne_26",
            "DoubleDeal.Security.OneRoundDP.mixRound_v10Sym_reads",
            "DoubleDeal.Security.OneRoundDP.card_seat_link_le",
            "DoubleDeal.Security.OneRoundDP.sameSeat2_subset",
            "DoubleDeal.Security.OneRoundDP.sameSeat2_eq_empty",
            "DoubleDeal.Security.OneRoundDP.card_agree_le_fifty",
            "DoubleDeal.Security.OneRoundDP.dp1Count_v10Sym_le_sum",
            "DoubleDeal.Security.OneRoundDP.dp1Count_v10Sym_self_le",
            "DoubleDeal.Security.OneRoundDP.dp1_le_v10Sym",
            "DoubleDeal.Security.OneRoundDP.dp1_le_v10Sym_zero_three",
            "DoubleDeal.Security.OneRoundDP.dp1_le_v10Sym_all",
            "DoubleDeal.Security.OneRoundDP.seat2_eq_of_seat2Idx_eq",
            "DoubleDeal.Security.OneRoundDP.covariant_iff_id_of_dp1_lt_off_v10Sym",
            # row/column sums of fullDiffCount (used by LinearMasks, M8b)
            "DoubleDeal.Security.FullCipher.sum_fullDiffCount",
            "DoubleDeal.Security.FullCipher.sum_fullDiffCount_left",
            # generic one-step facts behind fullDiffCount_one_left / _to_one (M8a review):
            # decks to decks, and (for _to_one) an explicit injectivity hypothesis
            "DoubleDeal.Security.Differential.dpCount_one_left",
            "DoubleDeal.Security.Differential.dpCount_to_one",
            # layer outputs as permutations (shared by D4 and OneRoundDP)
            "DoubleDeal.Security.Differential.permDeck_layerPerm",
            "DoubleDeal.Security.Differential.layerPerm_injective",
            # Linear (roadmap M8a): sums of squared correlations as autocorrelations weighted
            # by differential counts; L1 and the final-key step for arbitrary layers that
            # send decks to decks, L2-L4 for DoubleDeal's encryptL; independent full-permutation keys only; no numeric
            # bound; nothing proved for the real PassKey schedule
            "DoubleDeal.Security.Linear.sum_sq_corr_finalKey",
            "DoubleDeal.Security.Linear.sumSqCorrLayer_eq",
            "DoubleDeal.Security.Linear.fullSumSqCorr_eq",
            "DoubleDeal.Security.Linear.fullSumSqCorr_eq_final",
            "DoubleDeal.Security.Linear.fullSumSqCorr_split",
            # LinearMasks (roadmap M8b): single-card masks and the sign mask; identities
            # only, no numeric bound; independent full-permutation keys only; L10 one
            # keyed layer only
            "DoubleDeal.Security.LinearMasks.autoCorr_cardMask",
            "DoubleDeal.Security.LinearMasks.fullSumSqCorr_cardMask",
            "DoubleDeal.Security.LinearMasks.fullSumSqCorr_cardMask_seat",
            "DoubleDeal.Security.LinearMasks.alignCount_eq",
            "DoubleDeal.Security.LinearMasks.corr_keyedLayer_sign",
        },
    },
    "security-heavy": {
        "dir": ROOT / "security",
        "axioms": "AxiomsHeavy.lean",
        "mode": "all",
        "known_sorry": set(),
        "min": 1,
        "required": HEAVY_THEOREMS,
    },
    "megadreifach": {
        "dir": MD_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 500,  # sanity: the audit must actually see the library
        # Required: every theorem the MegaDreifach README cites (MD_README_THEOREMS; the
        # selftest re-derives that list from the README and the Lean sources).
        "required": MD_README_THEOREMS,
    },
    "megadreifach-v1-deprecated": {
        "dir": MD_V1_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 500,  # sanity: the audit must actually see the package
        "required": MD_V1_README_THEOREMS,
    },
    "megadreifach-v3": {
        "dir": MD_V3_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        # sanity: the audit must see the whole package (the real audited count; raise as
        # Link 2 grows, lower only with a reason in the commit).
        # Printed count after per-group read-word decide! (plan item C).
        # 354 was the single decide!; +2 group theorems, −1 private embedPos_inj
        # (that lemma now lives in MegaDreifach.Link2).
        "min": 355,
        "required": MD_V3_README_THEOREMS,
    },
    "cbc-hmac-v1-deprecated": {
        "dir": CBC_HMAC_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 50,  # sanity: the audit must actually see the package
        "required": CBC_HMAC_LINK2,
    },
    "scramble": {
        "dir": SCRAMBLE_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 100,  # sanity: the audit must actually see the package
        "required": SCRAMBLE_LINK2,
    },
    "bs": {
        "dir": BS_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 150,  # sanity: the audit must actually see the package
        "required": BS_LINK2,
    },
    "ecbs": {
        "dir": ECBS_LEAN,
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": 1120,  # measured: check_axioms.py ecbs reports 1120 theorems
        "required": ECBS_LINK2,
    },
    "megadreifach-heavy": {
        "dir": MD_LEAN,
        "axioms": "AxiomsHeavy.lean",
        "mode": "all",
        "key": "full",
        "known_sorry": set(),
        "min": len(MD_HEAVY_THEOREMS),
        "required": MD_HEAVY_THEOREMS,
    },
}
# Heavy-library registries, checked in both modes of each family (so the default
# job notices a dropped or renamed heavy target). exact: the source must declare
# exactly the registered theorems; otherwise it must declare at least them.
REGISTRIES = {
    "security": {"dir": HEAVY_DIR, "theorems": HEAVY_THEOREMS, "exact": True,
                 "what": "HEAVY_THEOREMS"},
    "megadreifach": {"dir": MD_HEAVY_DIR, "theorems": MD_HEAVY_THEOREMS, "exact": False,
                     "what": "MD_HEAVY_THEOREMS"},
}


def heavy_source_theorems(heavy_dir=HEAVY_DIR):
    """Fully qualified names of the theorems declared in a heavy source dir, private
    ones included (the audit reports them under their user-facing name). Same scope
    tracking as `lean_source_theorems`."""
    return lean_source_theorems(heavy_dir, private=True)


def heavy_generated_problems(audited, listed, generated):
    """security-heavy: `listed` (HEAVY_THEOREMS) and `generated` (HEAVY_GENERATED) are
    disjoint, every audited theorem not in `listed` is in `generated`, and every
    `generated` entry is audited."""
    both = listed & generated
    extra = set(audited) - listed
    return ([f"{n} is in both HEAVY_THEOREMS and HEAVY_GENERATED" for n in sorted(both)]
            + [f"audited {n} is in neither HEAVY_THEOREMS nor HEAVY_GENERATED (source scan "
               "missed a declaration, or a new generated lemma?)"
               for n in sorted(extra - generated)]
            + [f"HEAVY_GENERATED entry {n} was not audited; remove it"
               for n in sorted(generated - both - set(audited))])


def heavy_registry_problems(reg):
    src = heavy_source_theorems(reg["dir"])
    what, names, where = reg["what"], reg["theorems"], reg["dir"].name + "/"
    bad = []
    if reg["exact"]:
        bad += [f"heavy theorem {n} is not listed in {what}" for n in sorted(src - names)]
    bad += [f"{what} entry {n} is not declared in {where} (dropped or renamed?)"
            for n in sorted(names - src)]
    if not src:
        bad.append(f"no theorems found in {where} (heavy target missing?)")
    return bad


MD_README = MD_LEAN.parent / "README.md"
# A theorem/lemma declaration line: optional `open … in` / `set_option … in` prefixes
# (any number, on the same line), an optional attribute, modifiers, then the name.
_DECL = re.compile(r"^\s*(?:(?:open|set_option)\s[^\n]*?\sin\s+)*"
                   r"(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|noncomputable)\s+)*)"
                   r"(?:theorem|lemma)\s+([^\s(:{\[]+)")
_SCOPE = re.compile(r"^\s*(?:noncomputable\s+)?(namespace|section|mutual|end)\b\s*([\w.']*)")


def lean_text_theorems(text, private=False):
    """Theorem names declared in one Lean file's text, fully qualified by tracking the
    namespace / section / mutual / end scopes (comments stripped; `namespace A.B` opens
    two scopes, closed by `end A.B` or by `end B` then `end A`; `_root_.` names are not
    qualified). Private ones only if `private`. No Lean needed.

    Line-based, not a Lean parser: nested block comments, /- inside a line comment,
    nonrec, attributes containing ], «…» names and declarations split across lines are
    not handled; the heavy gate fails loudly on any miss."""
    names = set()
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    stack = []  # one entry per open scope: a namespace component, or None (section / mutual)
    for line in text.splitlines():
        line = line.split("--", 1)[0]
        m = _SCOPE.match(line)
        if m:
            kind, arg = m.groups()
            parts = arg.split(".") if arg else []
            n = max(len(parts), 1)
            if kind == "namespace":
                stack += parts
            elif kind == "end":
                del stack[-n:]
            else:  # section (one scope per name component) / mutual
                stack += [None] * n
            continue
        d = _DECL.match(line)
        if d and (private or "private" not in d.group(1)):
            n = d.group(2)
            names.add(n.removeprefix("_root_.") if n.startswith("_root_.")
                      else ".".join([c for c in stack if c] + [n]))
    return names


MD_SCAN_SKIP = ("Generated", "MegaDreifachHeavy", ".lake")  # MegaDreifach default library


def lean_source_theorems(root, skip=(".lake",), private=False):
    """Theorem names declared under `root` (public only unless `private`), fully
    qualified; see `lean_text_theorems`. No Lean needed."""
    names = set()
    for path in sorted(root.rglob("*.lean")):
        if any(part in skip for part in path.relative_to(root).parts):
            continue
        names |= lean_text_theorems(path.read_text(), private)
    return names


def md_readme_cited(readme=MD_README, root=MD_LEAN):
    """The README's backticked identifiers that name a theorem of the default library
    (the token equals the name or a dotted suffix of it; must be unambiguous)."""
    tokens = set(re.findall(r"`([A-Za-z_][\w.']*)`", readme.read_text()))
    decls = lean_source_theorems(root, skip=MD_SCAN_SKIP)
    cited, bad = set(), []
    for t in sorted(tokens):
        hits = {n for n in decls if n == t or n.endswith("." + t)}
        if len(hits) > 1:
            bad.append(f"README token `{t}` is ambiguous: {sorted(hits)}")
        cited |= hits
    return cited, bad


SUDO_EXPORT = re.compile(r"^\s*export\s+func\s+([A-Za-z_]\w*)", re.M)
EMITTED_HEADER = "Emitted function"


def sudo_exports(text):
    """The `export func` names of a sudo source (`//` comments stripped)."""
    code = "\n".join(line.split("//", 1)[0] for line in text.splitlines())
    return set(SUDO_EXPORT.findall(code))


def readme_emitted(text):
    """(names, tables): the backticked names in the first column of the README tables
    whose first header cell is "Emitted function", and how many such tables there are
    (the caller requires exactly one)."""
    rows, tables, in_table = set(), 0, False
    for line in text.splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")] \
            if line.lstrip().startswith("|") else None
        if cells is None:
            in_table = False
            continue
        if not in_table:
            if cells[0] == EMITTED_HEADER:
                tables, in_table = tables + 1, True
            continue
        if set(cells[0]) <= set("-: "):
            continue  # the |---| separator row
        rows |= set(re.findall(r"`([A-Za-z_]\w*)`", cells[0]))
    return rows, tables


def export_table_problems(sudo_text, readme_text):
    """Problems with the README's "Emitted function" column against the sudo exports:
    an export not in the column, a column entry that is not an export, no table, no
    exports."""
    exports, (emitted, tables) = sudo_exports(sudo_text), readme_emitted(readme_text)
    if not exports:
        return ["the sudo has no `export func`"]
    if tables == 0:
        return [f'no README table with a "{EMITTED_HEADER}" column']
    if tables > 1:
        return [f'{tables} README tables have a "{EMITTED_HEADER}" column (duplicate '
                "table: ambiguous, keep one)"]
    return ([f"export {n} is not in the README's {EMITTED_HEADER} column"
             for n in sorted(exports - emitted)]
            + [f"README {EMITTED_HEADER} {n} is not an export of the sudo"
               for n in sorted(emitted - exports)])


REPORT = re.compile(r"'(\S+?)' depends on axioms: \[([^\]]*)\]")
PRIVATE = re.compile(r"^_private\.[\w.']+?\.0\.")


def key_reports(found, full):
    """Key the (name, axioms) reports; return (seen, problems).

    default: private theorems under their user-facing name, so any two reports with
    the same user name (private/public or private/private) fail. full: keyed by the
    constant name (distinct private constants stay distinct), but a public theorem
    that shares its user name with a private one still fails."""
    seen, bad = {}, []
    for name, axs in found:
        key = name if full else PRIVATE.sub("", name)
        if key in seen:
            bad.append(f"duplicate audited name {key} (private/public collision)"
                       if not full else f"duplicate axiom report for {key}")
        seen[key] = axs
    if full:
        public = {n for n, _ in found if not PRIVATE.match(n)}
        for name, _ in found:
            user = PRIVATE.sub("", name)
            if user != name and user in public:
                bad.append(f"private theorem {name} has the user name of public theorem {user} "
                           "(private/public collision; keep one public lemma or rename)")
    return seen, bad


# Source-scan fixture: one-line `open … in` / `set_option … in` declarations and
# several namespaces per file (both missed by the earlier first-namespace regex scan),
# dotted namespaces and ends, sections, `noncomputable section`, `mutual`, `_root_`,
# comments. Valid core Lean 4.14 (no Mathlib `lemma`): `--selftest-lean` (CI job
# doubledeal-security) elaborates it and requires Lean's theorem names to be exactly
# HEAVY_SCAN_EXPECTED; `--selftest` checks the scanner against the same set.
HEAVY_SCAN_FIXTURE = """namespace A
theorem a : True := trivial
open Nat in theorem b : True := trivial
set_option maxHeartbeats 400000 in theorem c : True := trivial
open Nat in set_option maxHeartbeats 400000 in @[simp] private theorem c2 : True := trivial
end A
namespace B.C
protected theorem d : True := trivial
end C
theorem e : True := trivial
end B
noncomputable section
theorem f : True := trivial
end
namespace D
section S.T
/-- doc -/ theorem g : True := trivial
end S.T
theorem _root_.Z.h : True := trivial
/- theorem hidden : True := trivial -/
-- theorem hidden2 : True := trivial
mutual
theorem i : True := trivial
end
end D
theorem j : True := trivial
"""
HEAVY_SCAN_EXPECTED = {"A.a", "A.b", "A.c", "A.c2", "B.C.d", "B.e", "f", "D.g", "Z.h", "D.i",
                       "j"}
# Scanner-only (NOT elaborated: `lemma` is Mathlib/Batteries syntax, not core Lean).
SCAN_LEMMA_SNIPPET = "namespace L\nlemma m : True := trivial\nend L\n"
# Appended to the fixture by `--selftest-lean`: print every non-internal theorem the file
# declares, under its user-facing name.
_LIST_THEOREMS = """
open Lean Elab Command in
elab "#list_file_theorems" : command => do
  for (n, ci) in (← getEnv).constants.map₂.toList do
    let u := (privateToUserName? n).getD n
    if ci matches .thmInfo _ then
      unless u.isInternal do logInfo m!"THM {u}"
#list_file_theorems
"""


def axiom_problems(expected, seen, known_sorry):
    """Per-theorem axiom rules: each expected name must be reported and use only ALLOWED;
    a KNOWN_SORRY name may (and must) also use sorryAx, nothing else. Returns
    (problems, number of clean theorems, one line per allowlisted known-sorry theorem)."""
    bad, ok, known = [], 0, []
    for name in expected:
        if name not in seen:
            bad.append(f"no axiom report for {name}")
            continue
        axs = seen[name]
        if name in known_sorry:
            if axs - ALLOWED - {"sorryAx"}:
                bad.append(f"{name} uses {sorted(axs - ALLOWED - {'sorryAx'})}")
            elif "sorryAx" not in axs:
                bad.append(f"{name} is in KNOWN_SORRY but no longer uses sorryAx; remove it")
            else:
                known.append(f"known-sorry {name}: {sorted(axs)}")
        elif axs - ALLOWED:
            bad.append(f"{name} uses {sorted(axs - ALLOWED)}")
        else:
            ok += 1
    return bad, ok, known


def selftest_lean():
    """Elaborate HEAVY_SCAN_FIXTURE with `lean` (core only; run from a directory whose
    lean-toolchain is the audited one) and require its theorems to be exactly
    HEAVY_SCAN_EXPECTED, i.e. what the scanner finds."""
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "ScanFixture.lean"
        f.write_text("import Lean\n" + HEAVY_SCAN_FIXTURE + _LIST_THEOREMS)
        r = subprocess.run(["lean", str(f)], capture_output=True, text=True)
    out = r.stdout + r.stderr
    got = set(re.findall(r"THM (\S+)", out))
    ok = r.returncode == 0 and not re.search(r"\berror\b", out) and got == HEAVY_SCAN_EXPECTED
    print(f"check_axioms selftest-lean: {'ok' if ok else 'FAIL'} Lean elaborates the scan "
          f"fixture and declares {len(got)} theorems"
          + ("" if ok else f"; missing {sorted(HEAVY_SCAN_EXPECTED - got)}, extra "
             f"{sorted(got - HEAVY_SCAN_EXPECTED)}; lean exit {r.returncode}:\n{out}"))
    return 0 if ok else 1


def selftest():
    """The keying rules on synthetic reports (no Lean needed)."""
    pa = "_private.MegaDreifach.Link2.A.0.MegaDreifach.Link2.h"
    pb = "_private.MegaDreifach.Link2.B.0.MegaDreifach.Link2.h"
    pub = "MegaDreifach.Link2.h"
    cases = [  # (reports, full, expected number of problems)
        ([pa, "X.y"], True, 0),
        ([pa, pb], True, 0),      # private/private: tolerated under key "full"
        ([pa, pb], False, 1),     # ... but not under user-name keying
        ([pa, pub], True, 1),     # private/public: fails under key "full"
        ([pub, pa, pb], True, 2),
        ([pa, pub], False, 1),    # ... and under user-name keying
    ]
    failed = 0
    for names, full, want in cases:
        _, bad = key_reports([(n, set()) for n in names], full)
        ok = len(bad) == want
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} key={'full' if full else 'user'} "
              f"{names}: {len(bad)} problem(s), expected {want}")
    # Per-theorem axiom rules (axiom_problems), on synthetic reports: first with a scratch
    # allowlist {"A.c"}, then with the real (empty) KNOWN_SORRY of the security package.
    std = {"propext", "Classical.choice", "Quot.sound"}
    for what, seen_, known_sorry, want, want_known in [
            ("clean", {"A.t": std}, set(), [], 0),
            ("allowlisted sorry", {"A.t": std, "A.c": std | {"sorryAx"}}, {"A.c"}, [], 1),
            ("sorry not allowlisted", {"A.t": {"sorryAx"}}, set(), ["A.t uses ['sorryAx']"], 0),
            ("allowlisted, sorry gone", {"A.c": std}, {"A.c"}, ["no longer uses sorryAx"], 0),
            ("allowlisted, other axiom", {"A.c": {"sorryAx", "Lean.ofReduceBool"}}, {"A.c"},
             ["A.c uses ['Lean.ofReduceBool']"], 0),
            ("native_decide", {"A.t": {"Lean.ofReduceBool"}}, set(), ["A.t uses ['Lean.ofReduceBool']"], 0),
            ("security KNOWN_SORRY: the former conjecture with sorry",
             {"DoubleDeal.Security.roundBody_covariant_iff_id": std | {"sorryAx"}},
             PACKAGES["security"]["known_sorry"],
             ["DoubleDeal.Security.roundBody_covariant_iff_id uses ['sorryAx']"], 0)]:
        bad, _, known_l = axiom_problems(sorted(seen_), seen_, known_sorry)
        ok = (len(bad) == len(want) and all(w in b for w, b in zip(want, bad))
              and len(known_l) == want_known)
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} axiom rules ({what}): "
              f"{len(bad)} problem(s), expected {len(want)}" + ("" if ok else f": {bad}"))
    empty = not PACKAGES["security"]["known_sorry"]
    failed += not empty
    print(f"check_axioms selftest: {'ok' if empty else 'FAIL'} security KNOWN_SORRY is empty"
          + ("" if empty else f": {sorted(PACKAGES['security']['known_sorry'])}"))
    # security-heavy: audited = HEAVY_THEOREMS + HEAVY_GENERATED, exactly.
    lst, gen = {"A.t"}, {"A.f.eq_1"}
    for what, audited, listed, want in [
            ("exact", {"A.t", "A.f.eq_1"}, lst, []),
            ("unlisted, not generated", {"A.t", "A.f.eq_1", "A.b"}, lst,
             ["audited A.b is in neither"]),
            ("stale generated", {"A.t"}, lst,
             ["HEAVY_GENERATED entry A.f.eq_1 was not audited"]),
            ("unlisted and stale", {"A.t", "A.c"}, lst,
             ["audited A.c is in neither", "HEAVY_GENERATED entry A.f.eq_1 was not audited"]),
            ("in both sets", {"A.t", "A.f.eq_1"}, lst | gen,
             ["A.f.eq_1 is in both HEAVY_THEOREMS and HEAVY_GENERATED"])]:
        bad = heavy_generated_problems(audited, listed, gen)
        ok = len(bad) == len(want) and all(w in b for w, b in zip(want, bad))
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} HEAVY_GENERATED {what}: "
              f"{len(bad)} problem(s), expected {len(want)}")
    # MD_README_THEOREMS / MD_V1_README_THEOREMS / CBC_HMAC_LINK2 / SCRAMBLE_LINK2 / BS_LINK2 /
    # ECBS_LINK2 must be exactly the theorems the MegaDreifach README / the frozen v1
    # package's README / the DoubleDeal-CBC-HMAC proofs README / the Scramble proofs README /
    # the BS Link 2 README / the ECBS Link 2 README cites.
    for what, listed, readme, root in [
            ("MD_README_THEOREMS", MD_README_THEOREMS, MD_README, MD_LEAN),
            ("MD_V1_README_THEOREMS", MD_V1_README_THEOREMS, MD_V1_README, MD_V1_LEAN),
            ("MD_V3_README_THEOREMS", MD_V3_README_THEOREMS, MD_V3_README, MD_V3_LEAN),
            ("CBC_HMAC_LINK2", CBC_HMAC_LINK2, CBC_HMAC_LEAN.parent / "README.md",
             CBC_HMAC_LEAN),
            ("SCRAMBLE_LINK2", SCRAMBLE_LINK2, SCRAMBLE_LEAN.parent / "README.md",
             SCRAMBLE_LEAN),
            ("BS_LINK2", BS_LINK2, BS_LEAN / "README.md", BS_LEAN),
            ("ECBS_LINK2", ECBS_LINK2, ECBS_LEAN / "README.md", ECBS_LEAN)]:
        cited, bad = md_readme_cited(readme=readme, root=root)
        for b in bad:
            print(f"check_axioms selftest: FAIL {b}")
        missing, extra = sorted(cited - listed), sorted(listed - cited)
        ok = not bad and not missing and not extra
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} {what} matches the "
              f"{len(cited)} theorems cited in {readme.relative_to(ROOT.parent.parent)}"
              + (f"; cited but not listed: {missing}" if missing else "")
              + (f"; listed but not cited: {extra}" if extra else ""))
    # Every sudo export is in the README's "Emitted function" column (and only exports
    # are): the real packages, then planted negatives, including the real cbc-hmac README
    # with one row dropped, which must be reported as exactly that export missing. One
    # line per package; a broken real table is one FAIL line naming every problem.
    real_bad = {}
    for pkg, (sudo, readme) in sorted(LINK2_EXPORT_TABLES.items()):
        bad = real_bad[pkg] = export_table_problems(sudo.read_text(), readme.read_text())
        failed += bool(bad)
        print(f"check_axioms selftest: {'ok' if not bad else 'FAIL'} {pkg}: "
              f"{len(sudo_exports(sudo.read_text()))} exports of "
              f"{sudo.relative_to(ROOT.parent.parent)} vs the {EMITTED_HEADER} column of "
              f"{readme.relative_to(ROOT.parent.parent)}: "
              + ("; ".join(bad) if bad else "match"))
    sudo_fx = ("// export func commented(x: int) -> int\nexport func a(x: int) -> int\n"
               "    return x\nfunc helper(x: int) -> int\n    return x\n"
               "export func b_c(x: int) -> int // trailing\n    return x\n")
    table = "| Emitted function | Theorem |\n| --- | --- |\n| `a` | `a_refines` |\n"
    cases = [
        ("complete", sudo_fx, table + "| `b_c` | `b_c_refines` |\n", []),
        ("two exports in one cell", sudo_fx, table.replace("`a` |", "`a` / `b_c` |"), []),
        ("missing export", sudo_fx, table, ["export b_c is not"]),
        ("entry not exported", sudo_fx,
         table + "| `b_c` | `b_c_refines` |\n| `helper` | `h` |\n", ["README Emitted function helper"]),
        ("commented export listed", sudo_fx,
         table + "| `b_c` | x |\n| `commented` | x |\n", ["README Emitted function commented"]),
        ("no table", sudo_fx, "| Function | Theorem |\n| --- | --- |\n| `a` | x |\n",
         ["no README table"]),
        ("duplicate table", sudo_fx,
         table + "| `b_c` | x |\n\nText.\n\n" + table + "| `b_c` | x |\n",
         ["2 README tables have"]),
        ("no exports", "func a(x: int) -> int\n", table, ["the sudo has no"])]
    sudo, readme = LINK2_EXPORT_TABLES["cbc-hmac-v1-deprecated"]
    real_readme = readme.read_text()
    dropped = [l for l in real_readme.splitlines() if l.startswith("| `tags_equal` |")]
    cases.append(("real cbc-hmac README without the tags_equal row", sudo.read_text(),
                  "\n".join(l for l in real_readme.splitlines() if l not in dropped),
                  ["export tags_equal is not"] if len(dropped) == 1 else ["(fixture row absent)"]))
    for what, sudo_text, readme_text, want in cases:
        if what.startswith("real cbc-hmac") and real_bad["cbc-hmac-v1-deprecated"]:
            print(f"check_axioms selftest: skipped export table ({what}): the real table "
                  "already fails above")
            continue
        bad = export_table_problems(sudo_text, readme_text)
        ok = len(bad) == len(want) and all(w in b for w, b in zip(want, bad))
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} export table ({what}): "
              f"{len(bad)} problem(s), expected {len(want)}" + ("" if ok else f": {bad}"))
    # The source scan on HEAVY_SCAN_FIXTURE (see there), on the scanner-only `lemma`
    # snippet, and per file: a namespace left open at the end of one file must not
    # qualify the next file's names.
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "F.lean").write_text(HEAVY_SCAN_FIXTURE)
        (Path(d) / "U.lean").write_text("namespace U\ntheorem u : True := trivial\n")
        (Path(d) / "V.lean").write_text("theorem v : True := trivial\n")
        in_dir = heavy_source_theorems(Path(d))
    for what, names, want in [
            ("lean_text_theorems (private included)",
             lean_text_theorems(HEAVY_SCAN_FIXTURE, private=True), HEAVY_SCAN_EXPECTED),
            ("lean_text_theorems (public)", lean_text_theorems(HEAVY_SCAN_FIXTURE),
             HEAVY_SCAN_EXPECTED - {"A.c2"}),
            ("lean_text_theorems (scanner-only lemma snippet)",
             lean_text_theorems(SCAN_LEMMA_SNIPPET), {"L.m"}),
            ("lean_text_theorems (unclosed namespace, then a new file)",
             lean_text_theorems("namespace U\ntheorem u : True := trivial\n")
             | lean_text_theorems("theorem v : True := trivial\n"), {"U.u", "v"}),
            ("heavy_source_theorems (the fixture plus the two files above)", in_dir,
             HEAVY_SCAN_EXPECTED | {"U.u", "v"})]:
        ok = names == want
        failed += not ok
        print(f"check_axioms selftest: {'ok' if ok else 'FAIL'} {what}: {len(names)} names"
              + ("" if ok else f"; missing {sorted(want - names)}, extra {sorted(names - want)}"))
    return 1 if failed else 0


def main(argv) -> int:
    pkg = argv[1] if len(argv) > 1 else "lean"
    if pkg == "--selftest":
        return selftest()
    if pkg == "--selftest-lean":
        return selftest_lean()
    if pkg not in PACKAGES:
        print(f"usage: check_axioms.py [{'|'.join(PACKAGES)}]", file=sys.stderr)
        return 2
    cfg = PACKAGES[pkg]
    axioms = cfg.get("axioms", "Axioms.lean")
    if cfg["mode"] == "all":
        # `#audit_all` lives in the shared core-only package proofs/audit
        build = subprocess.run(["lake", "build", "AuditAll"], cwd=cfg["dir"],
                               capture_output=True, text=True)
        if build.returncode != 0:
            print(build.stdout + build.stderr, file=sys.stderr)
            print(f"check_axioms: {pkg}: could not build AuditAll (proofs/audit)", file=sys.stderr)
            return 1
    proc = subprocess.run(["lake", "env", "lean", axioms], cwd=cfg["dir"],
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r"\berror\b", out):
        print(out, file=sys.stderr)
        print(f"check_axioms: {pkg}: {axioms} did not elaborate cleanly", file=sys.stderr)
        return 1
    found = [(n, {a.strip() for a in axs.split(",") if a.strip()}) for n, axs in REPORT.findall(out)]
    found += [(n, set()) for n in re.findall(r"'(\S+?)' does not depend on any axioms", out)]
    seen, bad = key_reports(found, cfg.get("key", "user") == "full")
    reports = len(found)
    if cfg["mode"] == "all":
        m = re.findall(r"\baudited (\d+)\b", out)
        if len(m) != 1:
            print(out, file=sys.stderr)
            print("check_axioms: missing or repeated 'audited N' line", file=sys.stderr)
            return 1
        if int(m[0]) != reports:
            print(f"check_axioms: Lean audited {m[0]} theorems but {reports} reports were parsed",
                  file=sys.stderr)
            return 1
    if cfg["mode"] == "list":
        src = (cfg["dir"] / "Axioms.lean").read_text()
        expected = re.findall(r"^#print axioms\s+(\S+)", src, flags=re.M)
    else:
        expected = sorted(seen)
    known_sorry = cfg["known_sorry"]
    if len(expected) < cfg["min"]:
        bad.append(f"only {len(expected)} theorems audited (expected at least {cfg['min']})")
    for fam, reg in REGISTRIES.items():
        if pkg == fam or pkg == fam + "-heavy":
            bad += heavy_registry_problems(reg)
    if pkg == "security-heavy":
        bad += heavy_generated_problems(seen, HEAVY_THEOREMS, HEAVY_GENERATED)
    for name in sorted(cfg.get("required", set()) - set(seen)):
        bad.append(f"required theorem {name} was not reported by the audit")
    for name in sorted(known_sorry - set(seen)):
        bad.append(f"KNOWN_SORRY entry {name} was not reported (renamed or removed?)")
    for name in re.findall(r"'(\S+?)' is an axiom declared in the package", out):
        bad.append(f"axiom declared in the package: {name}")
    probs, ok, known_lines = axiom_problems(expected, seen, known_sorry)
    bad += probs
    known = len(known_lines)
    for line in known_lines:
        print(line)
    for b in bad:
        print(f"check_axioms: FAIL {b}", file=sys.stderr)
    print(f"check_axioms: {pkg}: {len(expected)} theorems audited, {ok} use only "
          f"{sorted(ALLOWED)}, {known} known-sorry (allowlisted), {len(bad)} failures")
    if pkg == "security":
        print("check_axioms: security: DoubleDealSecurityHeavy is not in this audit; "
              "security-heavy (CI job doubledeal-security-heavy) audits its "
              f"{len(HEAVY_THEOREMS)} HEAVY_THEOREMS plus the theorems Lean generates there")
    if pkg == "security-heavy" and not bad:
        print(f"check_axioms: security-heavy: {len(expected)} audited = {len(HEAVY_THEOREMS)} "
              f"HEAVY_THEOREMS + {len(HEAVY_GENERATED)} HEAVY_GENERATED "
              f"({', '.join(sorted(HEAVY_GENERATED))})")
    if pkg == "megadreifach":
        print("check_axioms: megadreifach: the heavy library MegaDreifachHeavy (the "
              f"{len(MD_HEAVY_THEOREMS)} KAT theorems and their step lemmas) is NOT in this "
              "audit; it is audited by `check_axioms.py megadreifach-heavy` (CI job "
              "megadreifach-heavy)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
