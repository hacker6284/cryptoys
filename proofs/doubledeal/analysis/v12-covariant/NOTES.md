# DoubleDeal v12: narrowing the covariant round conjecture (milestone 4)

The conjecture `roundBody_covariant_iff_id` (`security/DoubleDealSecurity/Rounds.lean`,
DRAFT-SORRY) is **still open**. Its statement, name and `sorry` are unchanged. This
milestone proves **separate** theorems that narrow it
(`security/DoubleDealSecurity/CovariantNarrow.lean`, heavy checks in
`security/DoubleDealSecurityHeavy/CovariantNarrow.lean`). No counterexample was found.
Labels: PROVED (Lean, audited), CONDITIONAL (a hypothesis in the statement),
EXACT (exhaustive Python), MEASURED (sampled, fixed seed).

Notation: `F = unkeyedWithMix` = GridCycle ∘ stem, where stem = scoop_cm ∘ ShiftRows ∘
SumRanks ∘ lay_cm. `Covariant σ F` means `∃ τ, ∀ deck m, F(σ·m) = τ·F(m)`. The conjecture
says `Covariant σ F ↔ σ = 1`.

## What was known before

* PROVED: σ ∈ v10Sym, σ ≠ 1 ⇒ not covariant (`roundBody_not_covariant_of_stem`).
* MEASURED (before, in `checks/check_covariant.py`, 4 sampled decks per σ): all 1326
  transpositions, the 51 v10Sym and 200 random σ are non-covariant.

## New results

**A. Algebra (PROVED, no computation).**
* `covPair_unique`: the output relabelling τ is unique.
* `covPair_one_iff`: τ = 1 ↔ σ = 1.
* The covariant σ form a subgroup (`covSubgroup`), and so do the commuting σ (`commSubgroup`).
* **Reduction to prime order** (`roundBody_covariant_iff_id_of_prime`): the conjecture
  follows from its special case for σ of prime order p ≤ 52, taken as the hypothesis.
  A nontrivial subgroup of S_52 contains an element of prime order p, and p divides 52!.
  The same reduction is proved for the commuting case (`roundBody_commutes_iff_id_of_prime`).

**B. Commuting case and survival (PROVED).**
* `commutes_sr_iff_gc`: if F commutes with σ on every deck, then at every deck SumRanks
  commutes with σ iff GridCycle commutes with σ at the stem output.
* `commutes_card_survivors_eq`: consequently the SumRanks and GridCycle survivor sets of
  σ have equal size.
* `commutes_gc_le_of_not_v10Sym`: for σ ∉ v10Sym, GridCycle would then have to commute
  with σ on ≤ 52!/64 decks. This is a consequence, not a contradiction.

**C. Transpositions, commuting case (PROVED; kernel check in the heavy library).**
`roundBody_not_commutes_swap a b (hab : a ≠ b) : ¬ CommutesOnDecks (swap a b) F`.
* Swapping walk cards 50 and 51 never changes the GridCycle walk
  (`BranchNumber.seatW_swap_tail`). So at a stem output with the pair at positions
  50, 51, GridCycle commutes, and commuting F would force the stem to commute there.
* Conjugation by v10Sym reduces the check to the 51 pairs (0, e). v10Sym commutes with
  the stem and acts simply transitively on the 52 cards.
* Each (0, e) is refuted at one deck: 51 kernel `decide!`s.
* Reproduction: `swap_tail_witness.py` → `swap_tail_witness.log`.

**D. Transpositions, covariant case: the conjecture for every transposition (PROVED; kernel check in the heavy library).**
`roundBody_not_covariant_swap a b (hab : a ≠ b) : ¬ Covariant (swap a b) F`.
* GridCycle puts walk card 0 at output seat 26 (`mixColumns_seat26`). So covariance
  implies the **seat-26 condition** `Cell0Cov σ τ`: `stem(σ·m)₀ = τ(stem(m)₀)` on every
  deck (`cell0Cov_of_covPair`).
* The seat-26 condition is invariant under v10Sym conjugation (`cell0Cov_conj`). It
  fails for every τ once two decks m1, m2 satisfy stem(m1)₀ = stem(m2)₀ but
  stem(σ·m1)₀ ≠ stem(σ·m2)₀ (`not_cell0Cov_of_witness`).
* For (0, e), m1 is the identity deck and m2 is the identity deck with seats (1, j)
  exchanged, j ∈ {2, 3, 5, 34}.
* Kernel-checked: 5 + 2·51 stem evaluations.
* Reproduction: `cell0_witness.py` → `cell0_witness.log` (EXACT: every entry is checked).

## Measured (MEASURED) — `cell0_sample.py`, log `cell0_sample.log`

The seat-26 argument found a witness pair for **every** sampled prime-order σ:
* 100 samples each of 16 cycle types, from 1 transposition up to 26 disjoint
  transpositions, 3-, 5-, 7-, 13-, 17- and 47-cycles;
* 1600 of 1600 in total, using random decks.

The 51 v10Sym are the control: there no witness can exist, and none was found.

This is evidence only. A witness for a sampled σ says nothing about the other σ of the
same cycle type.

## What remains open (precisely)

* **The conjecture for every σ that is not a transposition and not in v10Sym.** By the
  prime-order reduction, it is enough to handle σ of prime order p ≤ 52 other than
  single transpositions: products of ≥ 2 disjoint transpositions, and products of
  p-cycles for odd p.
* **Suggested route (not done):** a single-cell analogue of `sumRanksV10_commutes_iff`.
  The route itself is formalised in `roundBody_covariant_iff_id_of_cell0`, which
  derives the conjecture from the hypothesis
  `∀ σ τ, Cell0Cov σ τ → ∃ a x, σ = v10Sym a x` (a statement about SumRanks' output
  cell (0,0) alone, since ShiftRows fixes row 0 and scoop_cm reads (0,0) first).
  * The measurement above is consistent with that hypothesis.
  * Proving it needs the swap-pair argument of `sumRanksV10_commutes_iff`, restricted
    to one output cell. That cell depends on the whole row chain (row 0 turns by row 3,
    which turns by row 2, …) and on the last column step (column 0 turns by column 12's
    GF(4) value and its own suits).
  * This is the obstacle the Rounds.lean assessment describes. Effort is uncertain; it
    was not attempted tonight.
* **Why finite checks do not finish it:** there are 52! σ. v10Sym conjugation only
  divides the count by 52, and there is no further symmetry of F to exploit (GridCycle
  commutes only with 1).
