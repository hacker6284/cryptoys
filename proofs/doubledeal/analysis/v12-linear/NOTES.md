# DoubleDeal v12: is there a linear-cryptanalysis analogue? (milestone 3, note only)

Status: **a note, not a theorem.** Nothing in this directory is proved. The one
number here is a MEASUREMENT (sampled, fixed seed) with a noise control. It is not
a security claim.

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

## Suggested next steps (not done)

* Measure the `(50,2)` analogue (the joint seats of two cards) for one round. This
  is where a SumRanks/GridCycle interaction could show up if it exists.
* Define a key-averaged second moment (the ELP analogue) for the standard
  representation, and see whether a trail-style product bound over rounds can be
  proved in the independent-key model, like milestone 2.
