# v12 one mix round, roadmap item B1 (`dp1_le`): what is proved, and the `v10Sym` rows measured

Lean: `security/DoubleDealSecurity/OneRoundDP.lean`. Measurements: `../v12-differential/diff1.c`
(modes `r`, `k`, `c`), `run.sh`, `logs/`.
**The measurements are EMPIRICAL ONLY; no theorem uses them. Not a security claim.**

## What B1 asks, and how it relates to the stem bounds

B1: `max_{α ≠ 1, β} DP_1(α → β) ≤ ε₁` for ONE mix round (the stem, then GridCycle), independent
uniform key, `DP_1 = dp1Count α β / 52!` (`Differential.dp1Count = dpCount (mixColumns ∘ unkeyedNoMix)`).

The stem bounds of `StemUnion` (`dpFCount_le_of_ne`, `fullDiffCount_le_64`) are about the stem as
the LAST layer with an independent key before it (one Markov step). Inside a mix round there is
no key between the stem and GridCycle, so
`dp1Count α β = Σ_γ #{π : stem difference = γ and GridCycle sends (stem x, γ·stem x) to β}`
is a joint count, not a product of the two tables; the stem bounds give no `dp1Count` entry.
The only exact link: for `α ∈ v10Sym` the stem passes `α` unchanged
(`Differential.unkeyedNoMix_rel_v10Sym`), so the `v10Sym` rows are GridCycle's own rows.

## Proved (`OneRoundDP`)

* **B1 implies the covariant conjecture.** `covariant_iff_id_of_dp1_lt`: if
  `dp1Count α β < 52!` for every `α ≠ 1` and `β`, then `roundBody_covariant_iff_id` holds (a
  covariant pair counts every deck, `dp1Count_eq_of_covPair`); `covariant_iff_id_of_dp1Bound`
  for `DP1Bound p`, `p ≥ 2`. That conjecture is the one allowed `sorry` (in the default library; its statement is proved in the heavy library (finite checks by kernel `decide!`), `LabelStep.roundBody_covariant_iff_id_heavy`), and B1 for the rows
  outside `v10Sym` is at least as hard and is NOT proved: since the `v10Sym` rows are bounded
  (below), a bound below 1 on the rows outside `v10Sym` alone already implies the conjecture
  (`covariant_iff_id_of_dp1_lt_off_v10Sym`).
* **The 51 `v10Sym` rows**, for every output `β`:
  `dp1_le_v10Sym`: `52 · dp1Count (v10Sym a x) β ≤ 52!` for `(a, x) ∉ {(0, 0), (0, 3)}`;
  `dp1_le_v10Sym_zero_three`: `17 ·` for `v10Sym 0 3`; `dp1_le_v10Sym_all`: `17 ·` for all 51.
  Method: GridCycle's first two output seats (`mixRound_v10Sym_reads`; seat 26 is D4's
  `Differential.v10Sym_step_agree`) give `β (y 26) = α (y 26)` and
  `β (y p') = α (y p)` with `p = seat2Idx (y 26)`, `p' = seat2Idx (α (y 26))`; three distinct seats of
  a uniform deck (`card_seat_link_le`), at most 50 agreeing first cards (`card_agree_le_fifty`), and
  GridCycle survival for the diagonal (`dp1Count_v10Sym_self_le`). For `v10Sym 0 3` and first
  card K♣ or K♠ the two reads coincide (`sameSeat2`) and those first cards are counted in full,
  hence 1/17 instead of 1/52: a limit of the proof, not a measured value.

NOT proved: B1 for any row outside `v10Sym`; anything about several rounds or the real schedule.

## Measured (EMPIRICAL)

`sh run.sh 20000000 6` (about 20 minutes on 6 cores; `diff1 SPEC N SEED - r|c|k`): for each of
the 51 nontrivial `v10Sym a x`,
* row run (`r`): `N = 2·10^7` uniform decks x, output difference `β = diff(U x, U(α·x))`;
  also checks `stem(α·x) = α·stem(x)` on every sample;
* column run (`c`): `N = 2·10^7` uniform outputs y, input difference through `U^-1`;
* one restricted row run (`k`) for `v10Sym 0 3`, `N = 2·10^6` decks whose stem output starts
  with K♣ or K♠ (the first cards the proof counts in full).

Each difference is hashed to 64 bits; equal hashes count as equal. Rule: if no hash repeats in
N samples, then with 95% confidence (per run) every difference has probability `< 4.744/N`
(a difference of probability `p ≥ 4.744/N` is drawn at most once with probability
`≤ (1 + 4.744)·e^-4.744 = 0.05`). Positive control (`logs/control_swap01.log`): the swap `(0 1)` at `N = 2·10^6` shows repeats
(row: max multiplicity 133, all on `β = (0 1)`; column: 109); the stem check fails there, as
expected, since `(0 1)` is not in `v10Sym`.

Results (`logs/rows.log`, `logs/cols.log`, `logs/kcks_0_3.log`):
* all 103 runs: **no repeat** (every sampled difference distinct, max multiplicity 1);
* rows: no sample returned `β = α`, min support of `β` is 40, at most 19 cards where `β` agrees with `α`;
  0 stem-check failures;
* columns: no input difference in `v10Sym`, min support 41;
* `k` run: no repeat, min support 43.

So, per run at 95% confidence: every entry of each `v10Sym` row and column is below
`4.744/(2·10^7) ≈ 2.4·10^-7` (about 2^-22), far below the proved 1/52 and 1/17; on the K♣/K♠
first cards of `v10Sym 0 3`, every conditional entry is below `2.4·10^-6`. 103 runs at 95% each
are not a joint 95% statement. Nothing here is about rows outside `v10Sym`.

The logs were recorded with an earlier standalone copy of these modes (`dp1v10.c`, removed); the
`r`, `k`, `c` modes of `diff1.c` use the same code and seed streams and reproduce them exactly
(checked: `control_swap01.log` and `kcks_0_3.log` byte for byte, and the rows `v10Sym 1 0`,
`v10Sym 12 3` and the column `v10Sym 1 0` line for line).
