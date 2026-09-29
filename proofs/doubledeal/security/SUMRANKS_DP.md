# `sumRanksV10_survival_le`: the v10 SumRanks survival bound

**What it says.** This is about SumRanks v10 alone: one layer, no key, no rounds. Take any card relabelling τ
outside the 52-element symmetry group `v10Sym`. Then at most `52!/64` of the `52!` decks satisfy
`sumRanksV10 (τ·g) = τ·(sumRanksV10 g)`. It is not a security statement about the cipher.

**Also proved: one exact value.** For the one same-suit 3-cycle `threeCycle` = A♣→2♣→3♣ (cards `0 → 1 → 2`,
the permutation of `../analysis/v10-sumranks/sbox-search/`), exactly `(9/1105)·52!` decks survive
(`sumRanksV10_survival_threeCycle`, `ThreeCycle.lean`). So some non-symmetry survives on more than `52!/123`
decks (`sumRanksV10_survival_lower`), and the `1/64` constant is within a factor `1105/(9·64) ≈ 1.92` of tight.
This is the exact count for that one permutation, not a supremum.

Not formalised:
* the paper's sharper constant `0.012768` (PROOF.md §3 (A3), §5);
* the paper's Case B bound `1/425`;
* that `9/1105` is the maximum over all non-symmetries. PROOF.md §5b argues this; the argument is
  computer-assisted (it relies on the computer-checked Lemma R), not formalised in Lean and not independently
  reviewed. Only the value `9/1105` for the one 3-cycle above is proved.

**Where.**
* Lean sources: `DoubleDealSecurity/SumRanksDP/`. They are part of the default `DoubleDealSecurity`
  build and the `#audit_all` axiom audit. `check_axioms.py security` requires both main theorems and the two
  3-cycle theorems.
  * `Standalone.lean`: Mathlib only.
  * `Decomp.lean`: shared decomposition lemmas.
  * `Main.lean`: the main proof.
  * `ThreeCycle.lean`: the exact 3-cycle count.
* Paper proof: `sumranks-dp-paper/PROOF.md`. `PROOF.md §n` below and in the Lean comments refers to it.
* Axioms of all four theorems: `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry`, no
  `native_decide` and no new axiom.

```lean
theorem sumRanksV10_survival_le (τ : Relabel) (h : ¬ ∃ a x, τ = v10Sym a x) :
    64 * (survivors τ).card ≤ Fintype.card (Equiv.Perm (Fin 52))
-- survivors τ = univ.filter fun π =>
--   sumRanksV10 (relG τ (deckGrid π)) = relG τ (sumRanksV10 (deckGrid π))
-- deckGrid π = layColumnMajor (permDeck π)
```

`sumRanksV10_survival_le'` is the same bound, with the filter written out and `Nat.factorial 52` on the
right.

```lean
theorem sumRanksV10_survival_threeCycle :
    1105 * (survivors threeCycle).card = 9 * Fintype.card (Equiv.Perm (Fin 52))
-- threeCycle = Equiv.swap 0 2 * Equiv.swap 0 1   (0 ↦ 1 ↦ 2 ↦ 0, i.e. A♣ → 2♣ → 3♣)

theorem sumRanksV10_survival_lower :
    ∃ τ : Relabel, (¬ ∃ a x, τ = v10Sym a x) ∧
      Fintype.card (Equiv.Perm (Fin 52)) < 123 * (survivors τ).card
```

## Lemma map

The **S** file is `Standalone.lean` (namespace `SRDP`), **D** is `Decomp.lean`, **M** is `Main.lean` and **T**
is `ThreeCycle.lean` (namespace `DoubleDeal.Security.SumRanksDP`).

| # | PROOF.md | Lemma | File | Statement (informal) |
|---|---|---|---|---|
| 1 | §0 (0.1) | `sym_of_const`, `nonconst_of_not_sym` | M | constant δ and ε give a `v10Sym`; outside `v10Sym`, δ or ε is not constant |
| 2 | §0 | `sum_delta`, `sum_toZ_eps` | M | `Σ_c δ(c) = 0` in `ZMod 13`; `Σ_c ε(c) = 0` in GF(4) |
| 3 | §0 (0.2) | `rowTotal_cast`, `rowTurn_rel_iff` | M | the row turn is unchanged by τ iff `S = 0` |
| 4 | §0 (0.3) | `sum_seat_shift`, `wS_mul_rot1`, `rowS_rotate` | S, M | `S(Lᵏx) = S(x) − k·D(x)` |
| 5 | §0 | `colTurn_rel_iff` | M | the column turn is unchanged by τ iff `V(ε(prev)) = Σ(ε(col))` |
| 6 | §1 Lemma 1 | `survives_iff_amounts` | M | survival iff all 17 applied amounts agree |
| 7 | §1 Lemma 1 | `traj_of_survives` | M | survival gives the row and column conditions along the deck's own trajectory |
| 8 | §1 Cor. 1 | `rowEq_of_rowCondsTraj`, `thetaG_prefix` | M | row `r` needs `S(A_r) = θ_r·D(A_r)`; `θ_r` depends only on rows `< r` |
| 9 | §2 Lemma 2(a) | `lemma2a` | S | if `D ≠ 0`, each value of `S` is taken by exactly `13!/13` arrangements |
| 10 | §2 Lemma 2(b) | `lemma2b` | S | if value `v` occurs `z` times and the row is not constant, each value of `S` is taken at most `13!/(z+1)` times |
| 11 | §2 Lemma 2(c) | `lemma2c`, `sum_of_cancel` | S | a cancelling pair `{v¹¹, v+u, v−u}` never gives `S = 0` |
| 12 | §2 Lemma 3 | `nested_count`, `nested_count_eq`, `sum_mul_card_shuf` | D | nested fibre count (`≤` and exact); averaging over per-row / per-column reorderings |
| 13 | §2 Lemma 3 | `rowChain_eq`, `rowChain_le` | M | decks passing the four row conditions `= Σ_π Π_r ρ(row r)` |
| 14 | §2 | `rho_le_hA`, `rho_le_third`, `rho_eq_zero_of_cancel`, `rho_of_single` | M | pointwise bounds on `ρ` from Lemma 2 |
| 15 | §3 | `maxClass_le_50`, `exists_vStar`, `nStar_le_50` | S, M | the largest δ-class has at most 50 cards |
| 16 | §3 | `survivors_le_rhoSum` | M | survivors `≤ Σ_π Π_r ρ` |
| 17 | §3 (A1) | `caseA1` | M | `n* = 50`: `221 · Σ ≤ 52!` |
| 18 | §3 (A2) | `hyper_rows` (via `hyper_gen`) | S | multivariate hypergeometric count over rows |
| 19 | §3 (A2) | `caseA2` | M | `Σ ≤ 52! · E_A(n*)` |
| 20 | §3 (A2) | `EA_le` | S | `E_A(n) ≤ 1/100` for `13 ≤ n ≤ 49` (table A) |
| 21 | §3 (A3) | `distinct_row_count`, `card_transversals_le`, `amgm13` | S | at most `4¹³·52!/C(52,13)` decks have a row with 13 distinct values |
| 22 | §3 (A3) | `caseA3`, `A3_const` | M, S | `n* ≤ 12`: `Σ ≤ 52!·(1/81 + 4·4¹³/C(52,13))`, and that constant (`0.012768`) is `≤ 1/64` |
| 23 | §3 | `caseA_bound` | M | δ not constant ⇒ at most `52!/64` survivors |
| 24 | §4 | `colConds_H_card` | M | the post-row grid `H` is uniform (a bijection of decks) |
| 25 | §4 Lemma 4 | `lemma4_count_le` (via `lemma4_core`) | S | one column: probability over the 24 orders that `V(ε) = t` is `≤ fB(off, y')` |
| 26 | §4 Lemma 5 | `colChain_le` | M | decks passing the 13 column conditions `≤ Σ_π Π_j φ` |
| 27 | §4 | `exists_class_ge_13`, `mStar_bounds` | S, M | `2 ≤ m' ≤ 39` when ε is not constant |
| 28 | §4 Thm B | `hyper_cols` (via `hyper_gen`) | S | multivariate hypergeometric count over columns |
| 29 | §4 Thm B | `caseB_sum` | M | `Σ_π Π_j φ ≤ 52! · E_B(m')` |
| 30 | §4 Thm B | `EB_le` | S | `E_B(m) ≤ 1/64` for `2 ≤ m ≤ 39` (table B; the maximum is `E_B(2) = 1/68`) |
| 31 | §4 | `caseB_bound` | M | ε not constant ⇒ at most `52!/64` survivors |
| 32 | §5 | `sumRanksV10_survival_le`, `sumRanksV10_survival_le'` | M | the main theorem |
| 33 | §1 Lemma 1, Cor. 1 | `rowCond_iff`, `rowsDone_rel_of_traj`, `colsDone_threeCycle`, `survives_threeCycle_iff` | T | the 3-cycle keeps suits, so it survives iff the four row equations hold |
| 34 | §5b | `count_triples`, `count_S3` | T | `σ i₀ + σ i₁ + 11·σ i₂ ≡ 0` on exactly `13!/11` arrangements |
| 35 | §5b | `rho_threeCycle` | T | `ρ = 1, 1/13, 1/13, 1/11` for a row holding `0, 1, 2, 3` moved cards |
| 36 | §5b | `rhoSum_threeCycle`, `survivors_threeCycle_card` | T | survivors `= Σ_π Π_r ρ = 1080·49!` |
| 37 | §5b | `sumRanksV10_survival_threeCycle`, `sumRanksV10_survival_lower` | T | exactly `(9/1105)·52!` survivors; the `1/64` constant is within a factor 2 of tight |

## Differences from the paper

* **Case A** splits as `n* ≤ 12` ((A3)), `13 ≤ n* ≤ 49` ((A2), with the coarser table bound
  `E_A ≤ 1/100`) and `n* = 50` ((A1)).
* **Case B** uses only the column conditions, with the refinement `fB 2 0 = 1/4`. It proves `≤ 1/64`,
  not the paper's `1/425`, and it needs no hypothesis on δ.
* The row chain is proved with equality (`rowChain_eq`, used for the exact 3-cycle count); the bound uses
  its `≤` half `rowChain_le`. `colChain_le` is stated as `≤`: the paper proves equality, but only `≤` is needed.

## Kernel checks

The finite checks use `decide!`. This is Lean 4.14's kernel-reduction `decide`; unlike `native_decide`,
it adds no axiom. Approximate times:

| check | what it checks | time |
|---|---|---|
| `tableA_nat` | table A | ≈1.5 s |
| `lemma4_core` | Lemma 4, 140 cases | ≈1.3 s |
| `perms4_eq` | explicit list of the 24 permutations of `Fin 4` | ≈0.5 s |
| `LA2_spec` | convolution square used by table A | ≈0.3 s |
| `TB1_lt`, `tableB_nat` | table B | < 0.5 s |
| `card_good_triples` | 3-cycle: the `156` seat triples in `(Fin 13)³` with `S = 0` (`13³` cases) | ≈2.4 s |
| `sum_fN_fin` | 3-cycle: the row-vector sum `180` (`4⁴` cases) | ≈0.4 s |

The `1716` distinct seat triples (`card_distinct_triples`) are not a kernel check: they are
`PermCount.card_distinct_triples_eq` at `Fin 13` (under 0.1 s).

`Standalone.lean` compiles in about 40 s, `Main.lean` in about 30 s and `ThreeCycle.lean` in about
11 s (10.7 s measured, 12.1 s before `card_distinct_triples` was derived). All are light enough
for the default build.

## Manual check (not in CI)

`checks/sumranks_dp_tables.py` recomputes tables A and B independently, in exact rational arithmetic,
using the same definitions as Lean. It runs in about 1.5 s and exits 1 on failure. Expected output:
* max `E_A` over `13..49` is `0.008416`, at `n = 49`;
* `E_B(2) = 1/68` and `E_B(3) = 1/425`.

The paper's own numerical checks are in `sumranks-dp-paper/`: `verify_proof.py` writes
`verify_output.txt`.
