# v12 full relabelling differential: measurements (roadmap milestone M6)

**EMPIRICAL ONLY.** Everything in this note is sampled. No theorem uses it, and no
number here is proved. **No numeric bound on the full differential is proved** anywhere
(`security/DoubleDealSecurity/Differential.lean`, security README "Roadmap", M6).
Not a bit-security claim. These measurements found no weakness.

## 0. What is proved (pointer)

The statements are in the header of `security/DoubleDealSecurity/Differential.lean`
(status: security README, "Roadmap", M6). Scope, for reading the numbers below:
independent uniform round keys; no numeric bound on the full differential; no product
decay; the `v10Sym` bounds hold only for `(a, x) ≠ (0, 0)` and cover only paths whose
difference stays inside `v10Sym`; the real PassKey schedule gets only `R = 1` and the
one-round `v10Sym`-cluster bound; the final no-mix round and `encryptN` are not
covered here (they are in M7, `FullCipher.lean`).

## 1. Method

C port of the v12 round (`../v12-keysched/dd12.h`, cross-checked against the Python
reference by `../v12-keysched/xcheck12.py`), plus an inverse unkeyed round in `ddiff.h`
(`inv_stem`, `inv_mix_v11`). `selftest.c` round-trips the inverse on 200 000 decks
(`logs/selftest.log`: OK).

* One round, forward (`diff1.c`): `x` uniform, pair `(x, α·x)`; record the difference
  after the stem (only SumRanks can change it), after GridCycle alone on `(x, α·x)`,
  and after the whole unkeyed round. Keys are a 64-bit hash of the difference with its
  support in the low 6 bits (hash collisions are possible in principle; they would add
  spurious matches).
* One round, backward (`diff1 … b`): `z` uniform,
  `γ = diff(U⁻¹ z, U⁻¹(β·z))`; then `P[γ] = T[γ][β]`, the one-round DP from `γ` to `β`.
* Two rounds, independent uniform keys (`mitm.c`): by the Markov recursion (proved,
  `diffCount_succ`), `DP₂(α → β) = ∑_γ T[α][γ] T[γ][β]`. With forward samples of `γ`
  from `α` and backward samples of `γ` into `β` (10^7 each), the estimate is
  `#{equal pairs} / (10^7 · 10^7)`, split into the `γ = α`, `γ = β` and other terms.
  Validated on a toy with a large DP (GridCycle, uniform key, GridCycle; `gcval.c`):
  A♣↔2♣ → A♣↔2♣ direct 1.68·10^-5 (336 of 2·10^7) against MITM 1.69·10^-5
  (`logs/gcval_*.log`).
* The real PassKey schedule: no new runs. `R = 1` is the same as independent keys
  (proved, `realDiffCount_one`). The MITM method needs independent round keys, so it
  is not valid for the real schedule at `R ≥ 2`. M5's characteristic measurement
  (`../v12-keysched/NOTES.md`) covers the dominant path only.

Cards are `13·suit + rank` with suits ♣ ♥ ♠ ♦ (A♣ = 0, 2♣ = 1, 5♦ = 43, 8♦ = 46,
K♣ = 12, K♦ = 51, A♣↔2♥ = (0, 14)). The 95% intervals in §2 (and the upper bounds
for zero counts) are exact Poisson intervals on the count; the §3 intervals are a
log-normal approximation for a product of two Poisson counts (see §3).
`sh run.sh [selftest|toy|one|back|scan|mitm|all]` rebuilds everything into `$BUILD`
(default `/tmp/v12-differential`); the sample files (`*.bin`, 80 MB each) stay there
and are not in the repository. Not run by CI.

## 2. One round, `T[α][β]` (10^7 decks each; `logs/f_*.log`, `logs/b_*.log`)

| input α | DP(α → α), forward | backward | best other β seen |
|---|---|---|---|
| A♣↔2♣ | 5.84e-5 [5.38, 6.33]e-5 (584) | 5.88e-5 (588) | 1.0e-6 (10; support 3) |
| 5♦↔8♦ | 5.39e-5 [4.94, 5.86]e-5 (539) | 5.69e-5 (569) | 1.1e-6 (11; support 3) |
| K♣↔K♦ | 0 (< 3.7e-7) | | no β seen twice |
| A♣↔2♥ | 0 (< 3.7e-7) | | no β seen twice |
| 3-cycle A♣→2♣→3♣ | 5.5e-6 [4.1, 7.2]e-6 (55) | 6.1e-6 (61) | 7e-7 (7; support 2) |
| double swap A♣↔2♣, 3♣↔4♣ | 6e-7 [2.2e-7, 1.3e-6] (6) | 2e-7 (2) | none seen twice |
| `v10Sym 0 3`, `v10Sym 1 0` | 0 (< 3.7e-7) | | no β seen twice |

Every sampled `α → α` hit also followed the characteristic (SumRanks and GridCycle
both commuted): 584/584, 539/539, 55/55, 6/6. The `v10Sym` rows agree with the proved
statement that one round never moves `v10Sym a x` to a *different* `v10Sym` (they are not a test
of it: `β = α` is the only `v10Sym` with a nonzero proved bound, and it was not seen).

All 312 same-suit swaps, 10^6 decks each (`logs/scan1.log`, `scan1.c`): mean DP(α → α)
5.66e-5, from 3.8e-5 (4♣↔6♣, 6♠↔10♠) to 8.0e-5 (2♦↔3♦). The variance of the counts is
60.7 against a mean of 56.6, consistent with Poisson noise around a common value. All
17 647 hits followed the characteristic.

Support of the output difference from A♣↔2♣ (fraction of the 10^7 decks):

| stage | 2 | 3 | 4–9 | 10–29 | 30–44 | 45–52 |
|---|---|---|---|---|---|---|
| SumRanks alone | 4.52e-3 | 0 | 0 | 5.0e-4 | 0.166 | 0.829 |
| GridCycle alone | 4.10e-3 | 3.79e-3 | 3.3e-2 | 0.304 | 0.423 | 0.232 |
| full round | 5.84e-5 | 4.9e-5 | 1.4e-3 | 6.7e-4 | 6.1e-4 | 0.997 |

GridCycle alone keeps a swap with probability 3.5–4.1e-3 (A♣↔2♣, 5♦↔8♦, K♣↔K♦,
A♣↔2♥); from A♣↔2♣ its most frequent support-3 outputs have ≈ 4.2e-5 each. K♣↔K♦: SumRanks
gives support 4–29 in ≈ 80% of decks, and the full round gives support ≥ 30 in ≈ 94%.
`v10Sym` inputs: SumRanks always commutes (proved); in the samples the output support
is ≥ 43 after GridCycle alone and ≥ 42 after the full round.

## 3. Two rounds, independent uniform keys (MITM, 10^7 × 10^7; `logs/mitm.log`)

| α → β | estimate | γ = α term | other paths |
|---|---|---|---|
| A♣↔2♣ → A♣↔2♣ | 3.44e-9 | 3.43e-9 [3.06, 3.85]e-9 | 3.2e-12 (≈ 0.1%; γ of support 3, 4) |
| 5♦↔8♦ → 5♦↔8♦ | 3.07e-9 | 3.07e-9 [2.73, 3.45]e-9 | 2.8e-12 |
| A♣↔2♣ → A♣↔3♣ | 4e-13 | 0 | 4e-13 |
| A♣↔2♣ → 2♣↔3♣ | 7.5e-13 | 0 | 7.5e-13 |
| A♣↔2♣ → A♥↔2♥ | 0 (no equal pairs) | | |
| A♣↔2♣ → double swap | 4e-14 | 0 | 4e-14 |
| A♣↔2♣ → 3-cycle A♣→2♣→3♣ | 2.06e-11 | 1.75e-11 | 3.05e-12 via γ = β; 7e-14 other |
| 3-cycle → 3-cycle | 3.4e-11 | 3.4e-11 | 8.9e-13 |
| 3-cycle → A♣↔2♣ | 4.1e-11 | 5.5e-12 | 3.5e-11 via γ = β |

The intervals are for the γ = α term only. That term is the product of the forward and
backward one-round counts (584 · 588 / 10^14 for A♣↔2♣, 539 · 569 / 10^14 for 5♦↔8♦);
the interval is the log-normal approximation `exp(ln est ± 1.96 √(1/n_F + 1/n_B))`, not
an exact interval. The smaller entries rest on a handful of matching keys and are
order-of-magnitude values. For the two same-suit swaps measured here (A♣↔2♣ and 5♦↔8♦;
no other swap was run for two rounds) the constant path carries ≈ 99.9% of the
estimated `DP₂(α → α)`. For the 3-cycle into a swap a path whose difference changes
wins (ordinary clustering). For comparison only: M2's proved bound on the
CHARACTERISTIC is `(1/64)² ≈ 2.4e-4`; nothing numeric is proved for the DIFFERENTIAL.

## 4. Open

* Any numeric bound on the full differential. Pushing a one-round column bound
  (`p · dp1Count γ β ≤ 52!` for every `γ ≠ 1`) through the Markov recursion gives the
  same bound for `R` rounds by convexity (the same bound for every `R`; it does not decay); for `β ≠ 1` and `p ≥ 2` its
  hypothesis would already imply the `τ = β` case of the covariant conjecture
  `roundBody_covariant_iff_id` (and, for every `β ≠ 1`, the whole conjecture), so it is
  neither proved nor claimed.
  This applies to a column bound for the MIX round (`dp1Count`). For the whole cipher
  (`encryptL`, which ends with the stem and no GridCycle), a column bound for the final
  round's stem is enough for outputs outside `v10Sym`. That is a statement about SumRanks
  alone. No proof of `roundBody_covariant_iff_id` goes through it (that statement is proved
  in the heavy library, `roundBody_covariant_iff_id`); it does imply that no β
  outside `v10Sym` is exactly stem-covariant into γ ≠ β, which now follows from
  `StemUnion.dpFCount_le_of_ne` (not stated as a separate theorem; `sumRanksV10_commutes_iff`
  rules out γ = β). See `FullCipher.fullDiffCount_le_of_col` (a PROVED reduction; the off-diagonal stem hypothesis is now
  PROVED, `StemUnion.dpFCount_le_of_ne`, and with the diagonal it is the column bound
  `StemUnion.dpFCount_col_le_64`, giving `StemUnion.fullDiffCount_le_64`: the same 1/64 for every n (the bound does not decay; nothing is proved about decay),
  independent keys, outputs outside `v10Sym`). Into `v10Sym` columns this route gives nothing (`not_col_v10Sym`).
* Paths through differences outside `v10Sym` (the only proved multi-round bound covers
  paths that stay inside `v10Sym`).
* The real schedule at `R ≥ 2` beyond the one-round bounds. (The final no-mix round
  and the link from `rounds` to `encryptN`: M7, `FullCipher.lean`; there the only numeric
  bound is `StemUnion.fullDiffCount_le_64`, the same 1/64 for every n (the bound does not decay; nothing is proved about decay), independent keys,
  outputs outside `v10Sym`.)
