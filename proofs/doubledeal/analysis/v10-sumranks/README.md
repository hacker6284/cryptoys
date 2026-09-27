# DoubleDeal v10 SumRanks: empirical notes (not a proof)

**Kind:** analysis. Nothing in this folder is a theorem, a spec or a security claim. The normative v10 SumRanks is SPEC §3.3 in [`primitives/cipher/doubledeal/SPEC.md`](../../../../primitives/cipher/doubledeal/SPEC.md) and `doubledeal.sudo`; the Lean model is [`../../lean/DoubleDeal/SumRanksV10.lean`](../../lean/DoubleDeal/SumRanksV10.lean).

v10 SumRanks is the candidate called **W5c** here. It was chosen from the W family in [`EXPERIMENTS.md`](EXPERIMENTS.md) (section "index-weighted SumRanks (W family) and the GF(4) suit sum (W5)"), after the v9 candidates in [`../../../deprecated/doubledeal-v9/candidates/CANDIDATES.md`](../../../deprecated/doubledeal-v9/candidates/CANDIDATES.md).

**Row weights.** The experiment log's prose writes the row weights as `(k+1)` for position k; the code (`candidates.py` `wrow`, `cand.c`) and the spec use `(13 − k) mod 13` (leftmost card weight 0, rightmost weight 1), which is what the two-running-totals hand method computes. All numbers here come from the code, so they are for the spec's weights.

## W5c swap survival (measured, empirical)

"Survival" of a transposition σ through a map F is the fraction of random decks m with F(σm) = σF(m).

| Measurement | W5c | v9 (for comparison) | Source |
| --- | --- | --- | --- |
| SumRanks alone, worst pair (all 1326 pairs × 200k decks; top 5 re-measured at 4e6) | ≈ 0.0045 ≈ 1/221 (exactly 1/221 for a same-suit swap, `sbox-search/`) | 0.236 ≈ 1/4.2 | `sronly2.py`, `sronly2_all.log` |
| SumRanks alone, worst non-symmetry relabelling of any shape (see below) | same-suit 3-cycle, exactly 9/1105 ≈ 1/123 | – | `sbox-search/` |
| SumRanks alone, pairs above 1/64 | 0 | 390 | same |
| SumRanks alone, surviving pair classes | same-suit pairs only (same-rank pairs: 0 hits in 200k decks per pair) | equal rank mod 13 / rank+suit mod 4 | `blindclass.py`, `blindclass.log` |
| Full round (SumRanks, ShiftRows, GridCycle), worst pair, 100k decks/pair | 1.4e-3 (Q♣↔K♣) | 4.3e-2 (K♣↔Q♥) | `allpairs.py`, `allpairs_W.log` |
| Heuristic 6-round product formula P_S^6 (P_round/P_S)^5, worst pair / summed over pairs | 2.1e-17 / 4.8e-16 | 3.6e-8 / 7.0e-8 (measured F6 for v9: ≈3.5e-8) | `EXPERIMENTS.md` table |
| Hand cost (convention in `EXPERIMENTS.md`) | 208 per SumRanks pass, 1768 per encryption | 104, 1144 | `EXPERIMENTS.md` |

The product formula is a heuristic independence assumption, not a measured six-round rate, and not a bound. The v10 full cipher was not measured at six rounds (the expected hit counts are far too small for Monte Carlo).

Structural facts that *are* proved in Lean: SumRanks v10 commutes with every relabelling in `v10Sym` (rank + a mod 13, suit label ⊕ x), `sumRanksV10_commutes_v10Sym` in [`../../security/DoubleDealSecurity/SumRanksV10.lean`](../../security/DoubleDealSecurity/SumRanksV10.lean). The converse is proved too: a relabelling commutes with v10 SumRanks on every deck iff it is in `v10Sym` (`sumRanksV10_commutes_iff`, [`../../security/DoubleDealSecurity/SumRanksV10Iff.lean`](../../security/DoubleDealSecurity/SumRanksV10Iff.lean)). That is about exact commutation on all decks; it says nothing about the per-deck survival rates measured here. For each non-identity `v10Sym` element there are permutation round keys and a deck on which the 6-round model does not commute with it (`encrypt6_not_commutes_v10Sym`), and under one fixed master key (the identity deck with the real PassKey schedule) no non-identity `v10Sym` element commutes with the emitted `encrypt` (`generated_encrypt_realKey_not_v10Sym_equivariant`, heavy target). These exclude exact symmetries only; they say nothing about near-symmetries such as the measured same-suit survival.

## Beyond swaps: the S-box difference search (`sbox-search/`, empirical)

The swap table above tests only transpositions. [`sbox-search/`](sbox-search/) widens this to other relabellings
and to position differences, again for SumRanks alone over uniformly random decks. It covers 3-cycles, double swaps,
same-rank and same-suit moves, GF(4) suit maps and rank maps on subsets, row/column rotations and block moves. The
low-weight families are exhaustive, and hill-climbs were run on top. Result:

- **The worst non-symmetry value difference measured is a same-suit 3-cycle (e.g. A♣→2♣→3♣), at exactly
  9/1105 ≈ 1/123.** That is exact by enumeration and agrees with 162,525 hits in 20M decks. This supersedes the
  swap-only "worst ≈ 1/221" as the SumRanks-alone worst case.
- The same-suit swap is 1/221. Nothing except the 51 exact `v10Sym` symmetries exceeds 1/64.
- Proved in Lean (`sumRanksV10_survival_le`, `../../security/SUMRANKS_DP.md`): no non-symmetry
  relabelling survives SumRanks alone on more than 1/64 of the decks. The exact 9/1105 is measured only.
- Mechanism: SumRanks reads 17 totals. Row totals see only ranks and column totals see only suits, so a
  same-suit cycle is invisible to every column. Each row holding a moved card must keep its weighted rank sum
  mod 13. Three cards in one row balance that sum in 1 of 11 placements; a swap in one row never balances.

This is a measurement with an exact enumeration under a stated uniformity argument. It is not a proof and not a
security claim; see that folder's README for scope and caveats.

## Files

| File | What |
| --- | --- |
| `EXPERIMENTS.md` | The experiment log (verbatim copy, with a banner) |
| `candidates.py`, `cand.c`, `cport.py` | Python and C models of v9 plus every candidate variant; W5c is `VARIANTS['W5c']` (bit 131072 in `cand.c`). Reuses `../../../deprecated/doubledeal-v9/attack/dd_v9.py` |
| `check_cand.py` | v9 variant matches the frozen v9 vectors; the W5c variant matches all 6 current v10 encrypt vectors (Python and C); C == Python; decrypt(encrypt) = id for every variant |
| `sronly2.py`, `sronly2_all.log` | SumRanks-only survival per pair (writes `sronly2_<V>.npy`, not committed) |
| `blindclass.py`, `blindclass.log` | Per-class breakdown of the SumRanks-only survival |
| `allpairs.py`, `allpairs_W.log` | Full-round per-pair survival |
| `sbox-search/` | SumRanks-alone difference search beyond swaps (own README, scripts, logs) |

The maintained v10 conformance check is `../../security/checks/ddport.py` / `selftest.py`; `check_cand.py` only confirms that W5c here is the same cipher. `EXPERIMENTS.md` also mentions files that stayed in scratch (the F6 extrapolation `extrap.py` / `extrap*.log`, `measure*`, `exp1*`); those numbers cannot be reproduced from this folder. `python3 check_cand.py` needs numpy and gcc; it builds `build/libcand.so` (gitignored).
