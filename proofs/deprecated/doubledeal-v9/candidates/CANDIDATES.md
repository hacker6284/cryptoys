# Candidate fixes for the v9 swap distinguisher (analysis only)

**Status: analysis, not a proposal.** Nothing here changes `SPEC.md` or any `.sudo`, and there is no v10. Choosing a successor, or none, is Zachary's decision. All numbers are measured, and none is a security claim.

The variants are implemented in `candidates.py` (Python) and `cand.c` (fast C mirror). `check_cand.py` checks four things: the `v9` variant matches the frozen v9 vectors, C matches Python, and decrypt∘encrypt = id on 360 cases across the 6 variants, so every variant below is still a permutation of decks. The measurements come from `measure.py 1 11`, with the log in `measure.log` and data in `measure.json` (2353 s on the shared box).

## Variants

| Name | Change (a single layer) |
| --- | --- |
| **A3** | SumRanks column weight is (rank − suit) mod 4 instead of (rank + suit) mod 4. |
| **R2** | SumRanks is rows, then columns, then **rows again** (the same row-total gesture a second time). |
| **G** | GridCycle "step again". A card whose target seat is taken repeats its own step from the blocked seat until it finds a free one. If the steps cycle back to its own seat (K♣ does this at once), it uses the v9 marker-row scan. |
| **GR2** | G and R2 together. |
| **B4** | GridCycle "slide along". A blocked card scans the **target** row from the blocked column, then the rows below. There is no marker. |

## Results

Method, identical for every variant:
- Every one of the 1326 transpositions: per-layer survival (P_S, P_G) over 20,000 decks.
- For the worst pair and for K♣↔Q♥: exact \(E_K(\sigma M) = \sigma E_K(M)\) at F2 (1e6 pairs), F3 (4e6) and F4 (1.6e7), with real PassKey keys.
- "F6 extrap." is a log-linear fit through the non-zero F2–F4 rates, evaluated at r = 6. "F6 formula" is \(P_S^6 (P_{round}/P_S)^5\).
- The v8 distinguisher is K♣↔K♦ (per round, F2 exact).
- v9Sym is the T1 group of 51 relabellings: GridCycle commutation, round commutation, and v9Sym(0,1) at F2.

| Variant | Worst transposition (per round) | F2 / F3 / F4 measured (worst) | F6 extrap. | F6 formula | K♣↔Q♥ per round; F2–F4 | v8 K♣↔K♦ per round; F2 | v9Sym |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **v9** | K♣↔Q♥, 1/23 | 1.02e-2 / 4.14e-4 / 1.82e-5 | 3.2e-8 | 3.3e-8 (F6 measured 3.5e-8) | as left | 1.7e-2; 1.02e-3 | 0/1,020,000 round; F2 0/1e6 |
| **A3** | K♣↔Q♦, 1/33 | 7.25e-3 / 2.16e-4 / 7.69e-6 | 7.9e-9 | 6.4e-9 | 0 (w4 now differs); F2–F4 0 hits | 1.7e-2; 1.03e-3 | 0; 0 (SumRanks no longer commutes on all decks for every v9Sym, so the group changes) |
| **R2** | K♣↔K♦ (same rank), 1/64 | 9.08e-4 / 1.38e-5 / 1.25e-7 (2 hits) | 1.9e-11 | 5.4e-11 | 1/97; 6.4e-4 / 7.8e-6 / 1.3e-7 | 1.6e-2; 9.4e-4 | 0; 0 |
| **G** | 4♣↔8♣ (same suit, Δrank 4), 1/28 | 8.35e-3 / 2.96e-4 / 9.25e-6 | 1.0e-8 | 1.3e-8 | 1/1124; 2.1e-4 / 5e-7 / 0 | 9.1e-3; 5.1e-4 | 0; 0 |
| **GR2** | K♣↔K♠ (same rank), 1/59 | 1.03e-3 / 1.55e-5 / 3.13e-7 (5 hits) | 9.1e-11 | 7.9e-11 | 1/6250; 1.1e-5 / 0 / 0 | 6.6e-3; 3.8e-4 | 0; 0 |
| **B4** | A♣↔K♣, **1/4** | 5.37e-2 / 1.21e-2 / 2.79e-3 | **1.4e-4** | 1.4e-4 | 1/462; 5.0e-4 / 1.3e-6 / 0 | 4.5e-3; 2.5e-4 | 0; 0 |

Reading the table:
- **B4 should be rejected.** It is far worse than v9: the slide makes A♣ and K♣ pick the same seat about 97% of the time.
- **A3 and G** only move the problem. A3 cuts the worst rate by about 4× and G by about 3×. By pigeonhole, every mod-4 weight has 13 cards per class, and within-row sums stay symmetric, so an equal-weight swap still passes SumRanks on about 12/51 of decks. G kills K♣'s self-blocking, but it creates same-seat coincidences for same-suit pairs.
- **R2 and GR2** remove the "same row only" path through SumRanks: the second row pass sees the swapped pair in different rows. The best pair falls to about 1/60 per round, and F6 to about 1e-10 (roughly 400× below v9). The worst pairs become same-rank pairs, the v8 family, which v9 had weakened and which is now back to the top of the list. That is still astronomically above 1/52!, so **none of the minimal patches removes the distinguisher.**
- **Root cause.** Every layer that moves cards decides from symmetric sums or local occupancy, so some relabellings of two cards survive each round with constant probability. A real fix probably needs more than a one-layer patch: more rounds (each round multiplies by the per-round rate, for example 1/60 for GR2), or a structurally different, card-order-dependent S-step. That is a design decision for Zachary.

## Which T1 proofs would break

- **A3.** Changes the column weight and therefore the symmetry group. Affected: `v9SymFn`, `v9_shift_iff`, the weight lemmas, `encrypt6_not_commutes_v9Sym`/`RealKey` (the v9Sym powers), SwapMechanism's `KC_QH_weights`, and the Link 2 `sum_ranks_refines` weight arguments. Generated/, the vectors, the demo and the CBC-HMAC KATs would all need regenerating.
- **R2.** Changes the `sumRanks` definition. The "if" direction of the SumRanks characterisation still holds. The "only if" (`row_pair`/`col_pair`), core `invSumRanks_sumRanks`, Link 2 `sum_ranks_refines`/SumLink, Generated/, vectors, `trace_sum` in the demo and the KATs need redoing.
- **G.** Changes the GridCycle chooser. T1 `Walk` is generic in `FreeChooser` and `seat2` is unchanged, so `mixColumns_commutes_iff_id` probably ports with a new `FreeChooser` proof. Link 2 Mix (`overflow_seat_refines`, `mixStep`, `scan_row`), `invMixColumns` and the `decide!` facts (`mixColumns_KC_KD_fails`, …) break.
- **GR2.** Everything under R2 and G.
- **B4.** Not worth porting.

## Reproduce

```sh
cd proofs/deprecated/doubledeal-v9/candidates
python3 check_cand.py          # v9 == frozen vectors; C == Python; decrypt∘encrypt = id
python3 weights.py             # P_G for all pairs under the weight variants (pg_all_pairs.json)
python3 measure.py 1 11 > measure.log   # ~40 min, 8 processes
```
