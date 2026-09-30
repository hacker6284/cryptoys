# DoubleDeal v12: is there a linear-cryptanalysis analogue? (roadmap milestones M3 and M8a)

Roadmap: [`security/README.md`, section "Roadmap"](../../security/README.md#roadmap).

Status: **a note, not a theorem.** Nothing in this directory is proved. The M3 part
(the first three sections) is the original note. Its one number is a MEASUREMENT
(sampled, fixed seed) with a noise control. The M8a section below describes what is now
proved in Lean (`../../security/DoubleDealSecurity/Linear.lean`) and records an exact
4-card toy check of it. The toy check is computed, not proved, and it is on S_4, not
S_52. Nothing here is a security claim.

## Why AES-style linear cryptanalysis does not transfer directly

Linear cryptanalysis works on a state in a vector space `F_2^n`. A mask `a` gives
the character `x ↦ (-1)^{a·x}` of the additive group. Key addition `x ↦ x ⊕ k`
multiplies each character by the sign `(-1)^{a·k}`, so per-key correlations change
only in sign. A linear layer maps characters to characters, which gives masks,
trails and the linear branch number.

The DoubleDeal state is a deck: an element of the symmetric group `S_52`, with no
addition. Specifically:

* The key layer, Compose, is right multiplication `x ↦ x ∘ K` in a **nonabelian**
  group. There are no nontrivial homomorphisms `S_52 → {±1}` other than the sign
  character. Every layer is a bijection of `S_52`, so the sign of `F(x)` versus the
  sign of `x` is the only one-dimensional "mask" available, and it is too coarse to
  be useful.
* No layer is linear in any sense that masks could follow. ShiftRows and lay/scoop
  are fixed seat permutations, i.e. right multiplications. SumRanks and GridCycle are
  *data-dependent* seat permutations.
* The existing seat-weight notion is differential (pairs), not linear.
  `../../security/checks/branchnum/NOTES.md` already records that "there is no linear
  analogue because no layer has linear structure".

So "linear branch number" has no direct meaning here. We did not force a definition.

## What the right analogue probably is

1. **Fourier analysis on `S_52` (representation theory).** For a nonabelian group,
   characters are replaced by irreducible representations `ρ`. A key-alternating
   structure fits well: right multiplication by `K` acts on the `ρ`-Fourier
   coefficient as multiplication by the matrix `ρ(K)`. With independent uniform `K`,
   Schur orthogonality makes the first moment vanish for every nontrivial `ρ`. The
   natural analogue of the expected linear potential (ELP) is the second moment
   `E_K ||·||²`, and "linear trails" become products of per-layer operators on the
   `ρ`-isotypic components. This is the principled generalisation. It is heavy:
   `S_52` has very large irreps, so any computation has to pick small ones (the
   trivial, sign and standard `(51,1)` representations, then `(50,2)`, `(50,1,1)`, …).
2. **The smallest concrete case: single-card position correlation.** The standard
   representation `(51,1)` (plus the trivial one) is the permutation representation
   on seats. The simplest statistic in that representation (averaged over which
   card it is, so coarser than the full Fourier data) is the 52×52 matrix
   `M[i][j] = P_x[the card at input seat i is at output seat j of F(x)]`.
   `M - J/52` measures how much a card's seat predicts its next seat. This is the
   analogue of a one-bit-in / one-bit-out linear approximation. The pairs analogue,
   `(50,2)` and friends, would track two cards at once.

## Measurement (MEASURED): `position_correlation.py`, log `position_correlation.log`

One unkeyed v12 round `U = GridCycle ∘ stem`, 2·10^6 uniform decks, seed 20260929.
The largest singular value of `M - J/52` is **0.0014**. The control, the same
statistic for uniformly random seat permutations with the same sample size, is
**0.0014**. The largest single-entry deviation is 0.0003 against 0.0003 in the
control. So **no single-card position bias was detected at this sample size**
through one unkeyed round. Resolution is about 1e-3 in singular value. This does
not show there is none, and it says nothing about two-card or higher statistics.
Note that with a uniform Compose key any first-moment position bias is erased
anyway (item 1). For a fixed key the question is the per-key correlation, which
this unkeyed statistic does not measure.

## M8a: squared correlations as differential counts (PROVED in Lean; identities only)

Lean: `DoubleDealSecurity/Linear.lean`; the exact statements are in its module header.
For integer functions `f`, `g` on decks and a deck map `E`, the unnormalised correlation is
`corrOf E f g = ∑_x f(x) g(E x)` over all 52! decks. The autocorrelation is
`autoCorr f α = ∑_x f(x) f(α·x)`. The Lean statements are:

* L1 `sumSqCorrU_eq`: one keyed layer `x ↦ U(x ∘ k₁) ∘ k₂`, summed over all key pairs:
  `∑_{k₁,k₂} corr² = ∑_{α,β} autoCorr f α · dpCount U α β · autoCorr g β`.
* L2 `sumSqCorr_eq`: `encryptL n`, summed over all (52!)^(n+2) key tuples, for any deck y:
  `52! · ∑_L corr² = ∑_{α,β} autoCorr f α · fullDiffCount α β n y · autoCorr g β`.
* L3 `sumSqCorr_eq_final`: the same with `fullDiffCount` split through the proof's
  finalRound step: `∑_L corr² = ∑_{α,β} autoCorr f α · diffCount α β n y ·
  ∑_γ dpFCount β γ · autoCorr g γ`.
* L4 `sumSqCorr_split`: `52! · ∑_L corr² = (52!)^(n+2) · autoCorr f 1 · autoCorr g 1 +
  ∑_{α,β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`.

What these are, and what they are not:

* **Generic.** They hold for every key-alternating cipher on the 52! decks whose Compose
  keys are independent uniform permutations, the whitening and final keys included, and
  whose unkeyed layers map decks to decks. No DoubleDeal layer is used. The cipher enters
  only through the differential counts.
* **No numeric bound.** They are identities. They move the linear question to the
  differential counts of M6/M7, and no numeric bound is proved for those.
* **Not the real PassKey schedule.** The proof averages over the final key (giving the
  autocorrelation of `g`) and uses that the counts do not depend on the deck, which
  needs every key uniform and independent of the others. Under the real schedule all
  keys are functions of one master key. The toy check below gives a dependent toy
  schedule for which the equation of the same shape fails.

This is the representation-theoretic picture of the M3 section, restricted to what
needs no representation theory. The second moment (sum of squares) is used because the
first moment is not key-invariant: right multiplication by a key does not just flip a
sign, as it does for XOR keys.

### Exact 4-card toy check (COMPUTED): `toy_link.py`, log `toy_link.log`

This is a pure-Python exact computation on S_4 (24 decks), seed 7, taking about 6 s.
CI reruns it (`security/checks/selftest.py`) and byte-compares the output with the log.
The toy cipher has the shape of `encryptL n`: `n` rounds of (Compose, `U`), then (Compose,
`V`, Compose). `U` and `V` are random bijections of the 24 decks, and `n` is 0 or 1. The
check uses Lean's conventions (Compose is `x ∘ k`; relabellings act on card values). For
random integer `f`, `g` it checks exact equality in L1 (for `U` and for `V`), L2, L3 and
L4. It also checks `fullDiffCount_eq_of_isDeck` (on three more decks),
`fullDiffCount_one_left` and `fullDiffCount_to_one`. All of these hold.

Two further outputs are not Lean statements:

* A dependent toy schedule `L = (k, F k, F(F k))` for `n = 1`, one master key `k`. Here
  `∑_k corr²` differs from `(1/4!) ∑ autoCorr · count · autoCorr` for all three random
  `(f, g)` tried; the right-hand side is not even an integer. This documents the header's
  "does not apply to the real schedule". It is a toy, not the PassKey schedule.
* First-order masks `f = 4·[x(s) = c] − 1` (M8b scope; not formalised). The normalised
  potential equals `(N/(N−1)²)(q − 1/N)`, `N = 4`, for the four seat/card choices tried. Here `q` is
  the fraction of (difference fixing `c`, key tuple) pairs whose output difference fixes
  `c'`.

## Suggested next steps (not done)

* M8b: first-order (single-card) masks, whose potential reduces to card-alignment counts
  (the toy's last block). As with M8a, no numeric bound is expected from the identity alone.
* Measure the `(50,2)` analogue (the joint seats of two cards) for one round. This
  is where a SumRanks/GridCycle interaction could show up if it exists.
* A trail-style product bound over rounds for the squared correlations is NOT in
  M8a. It would need numeric bounds on the differential counts, which are open (M6, M7).
