# Candidate fixes for the v9 swap distinguisher (analysis only)

**Status: analysis, not a proposal.** Nothing here changes `SPEC.md` or any `.sudo`. (Later note: v10 was chosen from a follow-up family, W5c; see [`../../../doubledeal/analysis/v10-sumranks/`](../../../doubledeal/analysis/v10-sumranks/). None of the variants below is v10.) All numbers are measured, and none is a security claim. Numbers are from `measure.log` except the F6 extrap. column (extrapolated by `extrap.py`; output in `extrap.log`) and v9's measured F6 (`../attack/NOTES.md:22`).

The variants are in `candidates.py` (Python) and `cand.c` (fast C mirror). `check_cand.py` checks four things:
1. the Python `v9` variant matches the 6 frozen encrypt vectors;
2. the C `v9` variant matches the same 6 vectors;
3. C == Python on 360 random cases (60 per variant);
4. decrypt(encrypt) = id on those same 360 cases.

So every variant below is still a permutation of decks. The measurements come from `measure.py 1 11` (log `measure.log`, data `measure.json`; 2353 s on the shared box).

## Variants

| Name | Change (one layer) |
| --- | --- |
| **A3** | The SumRanks column weight is (rank − suit) mod 4 instead of (rank + suit) mod 4. |
| **R2** | SumRanks does rows, then columns, then **rows again** (the same row-total gesture a second time). |
| **G** | GridCycle "step again": a card whose target seat is taken repeats its own step from the blocked seat until it finds a free one. If the steps come back to its own seat (K♣ does this at once), it falls back to the v9 marker-row scan. |
| **GR2** | G and R2 together. |
| **B4** | GridCycle "slide along": a blocked card scans the **target** row from the blocked column, then the rows below. There is no marker. |

## Results

**Method.** Every variant uses the same decks, keys and messages, because the seeds do not depend on the variant.
- **Scan:** per-layer survival (P_S, P_G) for all 1326 transpositions, at n = 20,000 decks per pair.
- **Exact rates:** for the worst pair found by the scan, re-measured with fresh seeds at n = 400,000, and for K♣↔Q♥, the exact rate of \(E_K(\sigma M) = \sigma E_K(M)\) at F2 (1e6 pairs), F3 (4e6) and F4 (1.6e7) with real PassKey keys.
- **"F6 extrap."** is the least-squares fit of log(rate) on r over the non-zero F2–F4 points, evaluated at r = 6 (`extrap.py`, `extrap.log`).
- **"F6 formula"** is \(P_S^6 (P_{round}/P_S)^5\).
- **Zero-hit cells** give the 95% upper bound (3/n).
- **v8** is the same-rank distinguisher K♣↔K♦.
- **v9Sym** is the T1 group of 51 relabellings: full-round commutation, and v9Sym(0,1) at F2.

| Variant | Worst transposition found by the scan (per round) | F2 / F3 / F4 measured (worst) | F6 extrap. | F6 formula | K♣↔Q♥ per round; F2 / F3 / F4 | v8 K♣↔K♦ per round; F2 | v9Sym |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **v9** | K♣↔Q♥, 1/23 | 1.02e-2 / 4.14e-4 / 1.82e-5 | 3.2e-8 | 3.3e-8 (F6 measured 3.5e-8, 14/4e8, attack/NOTES.md) | as left | 1.7e-2; 1.02e-3 | round 0/1,020,000; F2 0/1e6 (<3e-6) |
| **A3** | K♣↔Q♦, 1/33 | 7.25e-3 / 2.16e-4 / 7.69e-6 | 7.9e-9 | 6.4e-9 | 0 (w4 now differs); 0 hits (<3.0e-6 / <7.5e-7 / <1.9e-7, 95%) | 1.7e-2; 1.03e-3 | round 0/1,020,000; F2 0/1e6 (<3e-6). SumRanks no longer commutes on all decks for every v9Sym, so the group changes. |
| **R2** | K♣↔K♦ (same rank), 1/64 | 9.08e-4 / 1.38e-5 / 1.25e-7 (2 hits) | 1.9e-11 | 5.4e-11 | 1/97; 6.4e-4 / 7.8e-6 / 1.3e-7 (2 hits) | 1.6e-2; 9.4e-4 | round 0/1,020,000; F2 0/1e6 (<3e-6) |
| **G** | 4♣↔8♣ (same suit, Δrank 4), 1/28 | 8.35e-3 / 2.96e-4 / 9.25e-6 | 1.0e-8 | 1.3e-8 | 1/1124; 2.1e-4 / 5e-7 (2 hits) / <1.9e-7 | 9.1e-3; 5.1e-4 | round 0/1,020,000; F2 0/1e6 (<3e-6) |
| **GR2** | K♣↔K♠ (same rank), 1/59 | 1.03e-3 / 1.55e-5 / 3.13e-7 (5 hits) | 9.0e-11 | 7.9e-11 | 1/6250; 1.1e-5 (11 hits) / <7.5e-7 / <1.9e-7 | 6.6e-3; 3.8e-4 | round 0/1,020,000; F2 0/1e6 (<3e-6) |
| **B4** | A♣↔K♣, **1/4** | 5.37e-2 / 1.21e-2 / 2.79e-3 | **1.4e-4** | 1.4e-4 | 1/462; 5.0e-4 / 1.3e-6 (5 hits) / <1.9e-7 | 4.5e-3; 2.5e-4 | round 0/1,020,000; F2 0/1e6 (<3e-6) |

### Reading the table

- **B4**'s worst pair is far worse than v9's: A♣↔K♣ survives 1/4 per round and F6 extrapolates to 1.4e-4 (v9 3.2e-8). On K♣↔Q♥ and K♣↔K♦ it is lower than v9 (1/462 and 4.5e-3 per round). The slide makes A♣ and K♣ pick the same seat about 97% of the time.
- **A3 and G** move the problem rather than remove it. On the F6-extrapolated metric only, A3 is about 4× below v9 and G about 3×. Per round the gain is smaller: A3 goes from 1/23 to 1/33 (1.4×), and G's worst pair is 1/28 (1.2×). By counting, each mod-4 weight class holds 13 cards and within-row sums stay symmetric, so an equal-weight swap still passes SumRanks on about 12/51 of decks. G removes K♣'s self-blocking but creates same-seat coincidences for same-suit pairs.
- **R2 and GR2** remove the "same row only" path through SumRanks, because the second row pass sees the swapped pair in different rows. The worst pair drops to about 1/60 per round. F6 extrapolates to about 2e-11 (R2) and 9e-11 (GR2), which is 350–1700× below v9. That rests on 2 and 5 F4 hits, so read it as order of magnitude only. The worst pairs become same-rank pairs (the v8 family) again. Either way this is astronomically above 1/52!, so **none of the minimal patches removes the distinguisher.**
- **Root cause and options.** Every layer that moves cards makes its decisions from symmetric sums or local occupancy, so some two-card relabellings survive each round with constant probability. The options for a fix include more rounds (each round multiplies the rate by the per-round survival, for example about 1/60 for GR2) and a structurally different, card-order-dependent S-step. The choice is Zachary's.

## Which T1 proofs would break

- **A3.** Changes the column weight and therefore the symmetry group. Affected: `v9SymFn`, `v9_shift_iff`, the weight lemmas, `encrypt6_not_commutes_v9Sym` / `RealKey` (the v9Sym powers), SwapMechanism's `KC_QH_weights`, and the weight arguments in Link 2 `sum_ranks_refines`. Generated/, vectors, demo and CBC-HMAC KATs would need regenerating.
- **R2.** Changes the `sumRanks` definition. The "if" direction (`sumRanks_rel_of_sums`) still has an analogue. The "only if" (`row_pair`/`col_pair`, `commute_rotations`), core `invSumRanks_sumRanks`, Link 2 `sum_ranks_refines` / SumLink, Generated/, vectors, the demo's `trace_sum` and the KATs need redoing.
- **G.** Changes the GridCycle chooser. T1 `Walk` is generic in `FreeChooser` and `seat2` is unchanged, so `mixColumns_commutes_iff_id` probably ports with a new `FreeChooser` proof. Link 2 Mix (`overflow_seat_refines`, `mixStep`, `scan_row`), `invMixColumns` and the `decide!` facts (`mixColumns_KC_KD_fails`, …) break.
- **GR2.** The union of R2 and G.
- **B4.** Port cost not assessed.

## Reproduce

```sh
cd proofs/deprecated/doubledeal-v9/candidates
python3 check_cand.py                    # the four checks above
python3 measure.py 1 11 > measure.log    # ~40 min, 8 processes; writes measure.json
python3 extrap.py > extrap.log           # F6 extrapolation from measure.json
```
