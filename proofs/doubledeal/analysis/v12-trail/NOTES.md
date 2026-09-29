# DoubleDeal v12: multi-round characteristic bound (roadmap milestone M2)

Roadmap: [`security/README.md`, section "Roadmap"](../../security/README.md#roadmap).

Labels: **PROVED** = Lean, audited; **CONDITIONAL** = proved with a hypothesis
stated in the theorem; **MEASURED** = random sampling with a fixed seed. Nothing
here is a security or bit-security claim, and a green build is not one either.

## Model and assumptions (all explicit)

1. **Independent uniform round keys (the Markov-cipher assumption).** The count is
   over all `(52!)^R` tuples `K : Fin R → Key`, so every tuple has the same weight.
   This is built into the statement by counting over the full tuple space. It is
   **not** a hypothesis about the real cipher. The real round keys come from one
   master deck through the PassKey chain (§3.7). They are not independent, and **no
   theorem here applies to them.** Whether the real schedule behaves like independent
   keys for this event is open (not proved, not measured here).
2. **Round model.** `rounds R y K`: for each i < R, Compose with `K i`, then lay
   column-major, SumRanks, ShiftRows, scoop column-major, GridCycle. Relative to
   `encryptN`, it takes `K = (pos0, posMix 0, …)` and drops the Compose that ends the
   last mix round and the final no-mix round. The dropped Compose commutes with every
   relabelling. The final no-mix round does **not**: it contains SumRanks. Extending
   the characteristic through it adds one more SumRanks condition, so the extended
   event is a sub-event and the same upper bound applies to it. That step, and the
   formal link to `encryptN`, are **not** proved here.
3. **Event = one characteristic, not a differential.** `Trail σ R y K` means that in
   *every* round SumRanks commutes with σ at the post-Compose state and GridCycle
   commutes with σ at the stem output. `trail_rounds_rel` proves that the event makes
   the output pair `(z, σ·z)`. The differential probability `DP(σ → σ)` also counts
   pairs whose difference changes and changes back, so it can be larger. This work
   gives **no bound on DP(σ → σ) and no bound on DP(σ → β) for β ≠ σ** (clustering is
   not handled).
4. **Starting pair.** The statements hold for **every** starting deck `y`, and the
   pair is `(y, σ·y)`. They are not averaged over messages.

## Proved (`security/DoubleDealSecurity/TrailBound.lean`, namespace `DoubleDeal.Security.TrailBound`)

`#T(σ,R,y)` below is `(univ.filter fun K : Fin R → Key => Trail σ R y K).card`.

* `trail_rounds_rel σ R y K : Trail σ R y K → rounds R (rel σ y) K = rel σ (rounds R y K)`.
* `card_keys_roundChar σ (hy : IsDeck y) : #{k | RoundChar σ (compose y k)} = roundCharCount σ`.
  This is Compose with a uniform key giving a uniform deck.
* `trail_card_le_of_round σ p (hround : p * roundCharCount σ ≤ 52!) R y (hy : IsDeck y) :
  p^R * #T(σ,R,y) ≤ (52!)^R`. This is the generic induction.
* `roundCharCount_le_sumRanks σ : roundCharCount σ ≤ #(SumRanksDP.survivors σ)` and
  `roundCharCount_le_gridCycle σ : roundCharCount σ ≤ #(gcSurvivors σ)`.
* `round_le_64_of_not_v10Sym σ (h : ¬∃ a x, σ = v10Sym a x) : 64 * roundCharCount σ ≤ 52!`.
* `round_le_26_v10Sym a x (hne : ¬(a = 0 ∧ x = 0)) : 26 * roundCharCount (v10Sym a x) ≤ 52!`.
  Here and below `hne` says `(a, x) ≠ (0, 0)`; it excludes `v10Sym 0 0 = 1`, for which
  every deck follows the characteristic and the bound is false.
* `round_le_of_v10Sym p (hp : p ≤ 64) hsym σ (h1 : σ ≠ 1) : p * roundCharCount σ ≤ 52!`,
  given `hsym`: the same bound for every nontrivial `v10Sym a x`. This is the one
  case split (SumRanks outside `v10Sym`) used by both `σ ≠ 1` statements below.
* **Unconditional:** `trail_card_le_26 σ (h1 : σ ≠ 1) R y hy : 26^R * #T ≤ (52!)^R`.
* **Unconditional:** `trail_card_le_64_of_not_v10Sym σ h R y hy : 64^R * #T ≤ (52!)^R`.
* **CONDITIONAL on `hKC : Check3 KC LKC`, `hKS : Check3 KS LKS`:**
  `trail_card_le_64_of_check … σ h1 R y hy : 64^R * #T ≤ (52!)^R` and
  `trail_card_le_4420_v10Sym_of_check … a x hne R y hy : 4420^R * #T(v10Sym a x) ≤ (52!)^R`.
* Heavy library (`DoubleDealSecurityHeavy/TrailBound.lean`), with the checks discharged by
  kernel `decide!`: `trail_card_le_64 σ (h1 : σ ≠ 1) R y hy` and
  `trail_card_le_4420_v10Sym a x hne R y hy` (`hne`: `(a, x) ≠ (0, 0)`), both without the
  check hypotheses.

In words: under independent uniform round keys, for every nontrivial relabelling σ
and every starting deck, the constant-σ characteristic through R rounds has
probability at most (1/64)^R. The default library proves (1/26)^R unconditionally,
and (1/64)^R given the finite check.

## Measured (`round_char.py`, log `round_char.log`, 10^6 decks, seed 20260929)

One-round characteristic probability over a uniform post-Compose deck:

| τ | stem commutes | RoundChar |
|---|---|---|
| A♣↔2♣ (same suit) | 4.466e-3 (SumRanks alone: 1/221 ≈ 4.52e-3, see below) | 5.8e-5 |
| 5♦↔8♦ | 4.593e-3 | 6.5e-5 |
| K♣↔K♦ | 0 | 0 (95% bound 3e-6) |
| v10Sym 0 3 | 1 | 0 (95% bound 3e-6) |

SumRanks alone: every same-suit swap commutes with v10 SumRanks on exactly 1/221 of
the decks. This is ENUMERATED exactly (not sampled) by `exact()` in
`../v10-sumranks/sbox-search/exact.py`, not proved in Lean; the Lean bound used
here is ≤ 1/64. `python3 exact.py --same-suit-swaps` runs `exact()` on all 312
same-suit swaps (A♣↔2♣, A♣↔K♣, 5♣↔8♣, … included) and gives exactly 1/221 for each,
and exactly 0 for each of the 78 same-rank swaps (`logs/exact_swaps.log`).

So the measured one-round values are far below the proved 1/64 per round. The gap
is GridCycle for small-support τ, which is not formalised (see
`../v12-diffusion/NOTES.md` §5 Findings, the "Gap (honest)" item). These values are not used by any theorem. They are not extrapolated
to R rounds here, because that would need the independence assumption this note
warns about.

Reproduce: `python3 round_char.py > round_char.log` (about 4 min on one core).

## Open

* The real PassKey schedule (dependent keys): only one round's bound is proved (M5, `../v12-keysched/NOTES.md`, `RealSchedule.lean`): ≤ 1/64 for every R. The proved bound gains nothing beyond round 1 (weaker than (1/64)^R, because from round 1 on the round key is not uniform given the state); a limit of the proof, not a measured weakness. For R ≥ 2 nothing rules out a probability above (1/64)^R.
* A numeric bound on the differential (sum over characteristics), including changing differences. M6 (`../v12-differential/NOTES.md`, `Differential.lean`) proves only its structure (Markov recursion, row sums; this characteristic is one path, a lower bound) and, for `(a, x) ≠ (0, 0)`, the bound for paths that stay inside `v10Sym` (exactly this characteristic). No numeric bound on the full differential.
* A whole-walk GridCycle bound for small-support τ.
* The final no-mix round, and the link of `rounds` to `encryptN`.
