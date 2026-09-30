# DoubleDeal v12: is there a linear-cryptanalysis analogue? (roadmap milestones M3, M8a, M8b)

Roadmap: [`security/README.md`, section "Roadmap"](../../security/README.md#roadmap).

Status: **a note, not a theorem.** Nothing in this directory is proved. The M3 part
(the first three sections) is the original note. Its one number is a MEASUREMENT
(sampled, fixed seed) with a noise control. The M8a section below describes what is now
proved in Lean (`../../security/DoubleDealSecurity/Linear.lean`) and records an exact
4-card toy check of it. The M8b section describes what is proved in
`../../security/DoubleDealSecurity/LinearMasks.lean`, its toy check, and the M8b
measurements (`measure/`), which are MEASURED or SCRIPT-COMPUTED, not proved. The toy
checks are computed, not proved, and they are on S_4, not S_52. Nothing here is a
security claim.

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
`corr E f g = ∑_x f(x) g(E x)` over all 52! decks. The autocorrelation is
`autoCorr f α = ∑_x f(x) f(α·x)`. Through `encryptL n _ L` the correlation is
`fullCorr n f g L`. Both sums of squares below are key-summed and unnormalised. The Lean
statements are:

* L1 `sumSqCorrLayer_eq`: one keyed layer `x ↦ U(x ∘ k₁) ∘ k₂`, summed over all key pairs:
  `∑_{k₁,k₂} corr² = ∑_{α,β} autoCorr f α · dpCount U α β · autoCorr g β`.
* L2 `fullSumSqCorr_eq`: `encryptL n`, summed over all (52!)^(n+2) key tuples, for any
  deck y: `52! · ∑_L fullCorr² = ∑_{α,β} autoCorr f α · fullDiffCount α β n y ·
  autoCorr g β`.
* L3 `fullSumSqCorr_eq_final`: the same with `fullDiffCount` split through the proof's
  finalRound step: `∑_L fullCorr² = ∑_{α,β} autoCorr f α · diffCount α β n y ·
  ∑_γ dpFCount β γ · autoCorr g γ`.
* L4 `fullSumSqCorr_split`: `52! · ∑_L fullCorr² = (52!)^(n+2) · autoCorr f 1 ·
  autoCorr g 1 + ∑_{α,β ≠ 1} autoCorr f α · fullDiffCount α β n y · autoCorr g β`.

Remark (not a theorem): the key-averaged normalised squared correlation would be
`E_L[ĉ²] = fullSumSqCorr n f g / ((52!)^(n+2) · autoCorr f 1 · autoCorr g 1)`. Under it,
L4 reads as `1/52!` plus the `α, β ≠ 1` remainder over
`(52!)^(n+3) · autoCorr f 1 · autoCorr g 1`.

What these are, and what they are not:

* **Generality.** L1 and the final-key step are proved for arbitrary layers. L2–L4 are
  proved for DoubleDeal's encryptL; their proofs use only independent uniform keys, layers
  sending decks to decks and, for L4, injective layers. In Lean: L1 (`sumSqCorrLayer_eq`)
  and the final-key step (`sum_sq_corr_finalKey`) take the layer as an argument. The
  layer facts that L2–L4 use are the generic `Differential.dpCount_one_left` (decks to
  decks) and `Differential.dpCount_to_one` (explicit `Function.Injective U`), applied to
  DoubleDeal's layers. For non-injective layers the same-shape L4 can fail.
* **No numeric bound.** They are identities. They move the linear question to the
  differential counts of M6/M7, and no numeric bound is proved for those.
* **Independent uniform keys only.** The statements are stated only for independent
  uniform keys; nothing is proved for the real PassKey schedule, and a dependent toy
  schedule shows the same-shape equation can fail (toy check below). The proof averages
  over the final key (giving the autocorrelation of `g`) and uses that the counts do not
  depend on the deck, which needs every key uniform and independent of the others.

This is the representation-theoretic picture of the M3 section, restricted to what
needs no representation theory. The second moment (sum of squares) is used because the
first moment is not key-invariant: right multiplication by a key does not just flip a
sign, as it does for XOR keys.

### Exact 4-card toy check (COMPUTED): `toy_link.py`, log `toy_link.log`

This is a pure-Python exact computation on S_4 (24 decks), seed 7, taking about 6 s.
CI reruns it (`security/checks/selftest.py`) and byte-compares the output with the log.
It checks the toy, not the Lean: it recomputes the same-shape identities on a 4-card
toy cipher, and it is not a check of the Lean statements or proofs.
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
  "a dependent toy schedule shows the same-shape equation can fail". It is a toy, not
  the PassKey schedule.
* First-order masks `f = 4·[x(s) = c] − 1` (not formalised in M8a; M8b's L6 below is
  the unnormalised form). The normalised
  potential equals `(N/(N−1)²)(q − 1/N)`, `N = 4`, for the four seat/card choices tried.
  Here `q` is the fraction of (difference fixing `c`, key tuple) pairs whose output
  difference fixes `c'`.

## M8b: single-card masks and the sign mask (PROVED in Lean; identities only)

Lean: `DoubleDealSecurity/LinearMasks.lean`; the exact statements are in its module
header. Same model as M8a: independent uniform keys only, key-summed and unnormalised,
nothing proved for the real PassKey schedule, and no numeric bound. The single-card mask is
`cardMask s c x = 52·[x s = c] − 1` (card `c` at seat `s`, centred), and
`alignCount c c' n y = ∑_{α c = c} ∑_{β c' = c'} fullDiffCount α β n y`.

* L5 `autoCorr_cardMask`: `autoCorr (cardMask s c) α = 52! · (52·[α c = c] − 1)`.
* L6 `fullSumSqCorr_cardMask`: `fullSumSqCorr n (cardMask s c) (cardMask t c') =
  52! · (52² · alignCount c c' n y − (52!)^(n+3))`, for any deck `y`; and
  `fullSumSqCorr_cardMask_seat`: the seats `s`, `t` do not matter.
* L7 `alignCount_eq`: `alignCount c c' n y` is the number of pairs (relabelling `α`, key
  tuple `L`) for which card `c` keeps its seat between `y` and `α·y` and card `c'` keeps
  its seat between the two ciphertexts: a truncated differential on one card's seat.
* L9 `autoCorr_cardMask_v10Sym` (a helper, not a headline): for `(a, x) ≠ (0, 0)`,
  `autoCorr (cardMask s c) (v10Sym a x) = −52!`. This is an immediate corollary of L5 and
  `v10Sym_fixfree` (the nontrivial `v10Sym` fix no card). Its only content is negative,
  a non-transfer: the SumRanks symmetries `v10Sym`, which pass the proof's finalRound step
  on every deck, enter L6 only through the constant term, like every relabelling that
  moves `c`. It says nothing about the cipher's layers.
* L10 `corr_keyedLayer_sign`: through ONE keyed layer `x ↦ U(x ∘ k₁) ∘ k₂` (`U` any deck
  map sending decks to decks), `corr (keyedLayer U k₁ k₂) sgnDeck sgnDeck =
  sign k₁ · sign k₂ · corr U sgnDeck sgnDeck`: the keys only flip the sign. One layer only;
  nothing about several rounds, and nothing about the value of `corr U sgnDeck sgnDeck`.

Remark (not a theorem): normalised as in the M8a remark,
`E_L[ĉ²] = (52/51²)(q − 1/52)` with `q = alignCount / (51! · (52!)^(n+2))`, the fraction
of (difference fixing `c`, key tuple) pairs whose output difference fixes `c'`. This is the
formula the M8a toy's last block checked for `N = 4`.

Not in M8b: positivity of the bracket in L6 (the proposal's L8), M8c, and the H1–H4
statements. No bound on `alignCount` is proved.

### Exact 4-card toy check (COMPUTED): `toy_masks.py`, log `toy_masks.log`

A pure-Python exact computation on S_4, seed 8, about 6 s. CI reruns it
(`security/checks/selftest.py`) and byte-compares the output with the log. It checks the
toy, not the Lean. On the toy cipher of `toy_link.py` it checks L5 for every seat, card and
relabelling; the L9 shape (`−4!` at the 9 fixed-point-free relabellings); row and column
sums of `fullDiffCount`; L7 and L6 (three card pairs, three seat pairs each, `n = 0, 1`);
and L10 for `U` and `V` and every key pair. All of these hold.

### M8b measurements (MEASURED or SCRIPT-COMPUTED; NOT proofs): `measure/`

`measure/run.sh` builds and runs everything (about 8 min, one core; not run by CI); logs
are in `measure/logs/`. The C programs use `../v12-differential/ddiff.h` and the v12
model `../v12-keysched/dd12.h`. No theorem uses any of these numbers.

* First order, MEASURED (`first_order.c`, `logs/first_order.log`; 5·10^7 uniform decks,
  seed 1). For the stem, one unkeyed round (GridCycle after the stem) and a control (a
  fresh uniform deck), the table `P(card c at output seat t | c at input seat s)`. The
  largest entry deviation from `1/52` is 6.3·10^-4 (stem), 6.5·10^-4 (unkeyed round) and
  6.4·10^-4 (control). The largest `q_c − 1/52` (with `q_c` the mean over `s` of
  `∑_t P(t|s)²`) is 5.8·10^-8, 1.0·10^-7 and 5.6·10^-8, and the corresponding
  `(52/51²)(q − 1/52)` is at most 1.2·10^-9, 2.0·10^-9 and 1.1·10^-9. So **no first-order
  bias was detected**: the stem and the round are at the noise level of the control, at
  about 10^-7 resolution in `q`. This does not show there is none.
* Sign, MEASURED (`sign_layers.c`, `logs/sign_layers.log`; 10^8 uniform decks, seed 2).
  `E[sgn(x) sgn(U x)]`: stem −0.00010, GridCycle alone −0.00001, unkeyed round +0.00019,
  control +0.00008, each ±0.00010 (one standard deviation). All are within 2 standard
  deviations of 0 (the largest is the unkeyed round, 1.9); resolution about 10^-4.
* The stem's exact sign correlation, SCRIPT-COMPUTED and UNPROVED (`stem_sign_dp.py`,
  `logs/stem_sign_dp.log`; exact rational arithmetic, about 2.5 min):
  `E[sgn(x) sgn(stem x)] = 2009561917/267966441044041684179375 ≈ 7.5·10^-15`. This value
  is not in Lean. It rests on the script's model of the stem's column turns: the sign of
  `stem(x)` times the sign of `x` is `(−1)^(sum of the 13 column turns)`, and the turns
  depend only on the suit pattern (the grid after the row step). That model is checked
  only by sampling, as follows; the checks are not proofs.
  - `stem_sign_check.c` (`logs/stem_sign_check.log`; 4·10^6 decks, seed (7,7,7)) samples
    the identity, with 0 failures, and the joint distribution of the first two column
    turns. `stem_turn_dp_check.py` (`logs/stem_turn_dp_check.log`) computes that
    distribution exactly from the model: it is uniform (0.0625 each). The 16 sampled
    values are within 3.5·10^-4 of it (at most 2.9 sampling standard deviations of
    1.2·10^-4).
  - Deck by deck: `stem_turn_dump.c` prints, for 2·10^5 decks (seed (7,7,8)), the suit
    grid after the row step and the 13 turns the C stem applies;
    `stem_turn_model_check.py` (`logs/stem_turn_model_check.log`) recomputes every turn
    with the model's own functions. 0 of the 2·10^5 decks have any mismatch. (With the
    model's column rotation reversed or removed, almost every deck mismatches, so the
    check does see the model.) The C stem is `../v12-keysched/dd12.h`, cross-checked
    against the Python port and the vectors there.
  The rest of the DP (the reduction to a uniform suit pattern and the transfer-matrix
  count) is not checked beyond its own assertion that it counts all suit patterns.
  By L10 (one keyed layer), this value would be the key-free size of the sign correlation
  through one keyed stem layer; nothing is claimed for several layers.

## Suggested next steps (not done)

* Any bound on `alignCount` (M8b reduces the single-card question to it), and the
  positivity of the L6 bracket (the proposal's L8, not in M8b).
* Measure the `(50,2)` analogue (the joint seats of two cards) for one round. This
  is where a SumRanks/GridCycle interaction could show up if it exists.
* A trail-style product bound over rounds for the squared correlations is NOT in
  M8a. It would need numeric bounds on the differential counts, which are open (M6, M7).
