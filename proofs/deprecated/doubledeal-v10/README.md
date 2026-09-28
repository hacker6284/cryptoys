# DoubleDeal v10: GridCycle parity shortfall (DEPRECATED algorithm)

**Kind:** per-layer weakness write-up, filed next to the frozen artifact (see the [`proofs/README.md`](../../README.md) taxonomy). It is **not** a working attack on the full cipher. This folder freezes DoubleDeal v10 at [`primitives/cipher/doubledeal/v10/`](../../../primitives/cipher/doubledeal/v10/), following the v8/v9 precedent. **The successor is v11**: GridCycle rule 1 + tweak B (ghost finger, blocker-directed scan). It is now the live `SPEC.md` / `doubledeal.sudo`. The analysis that found the shortfall and selected the fix is [`proofs/doubledeal/analysis/v10-gridcycle/`](../../doubledeal/analysis/v10-gridcycle/) (README, PHASE2–PHASE6). Nothing here is a security claim, and there are no bit-security claims in either direction.

## Why deprecate

v10 fixed the v9 SumRanks problem (position-aware SumRanks, W5c). GridCycle, the MixColumns stand-in, was left unchanged from v9, and it does not reach the parity we ask of a layer: for a single transposition of card faces σ = x↔y, the probability that σ commutes with one GridCycle application on a uniform deck should be small for **every** pair. We use 1/64 as the per-layer bar. v10 GridCycle misses it badly:

| Measurement (uniform decks, 200,000 decks per pair) | v10 GridCycle |
| --- | --- |
| worst pair | **K♣↔K♦: 0.262** (95% CI [0.260, 0.264]) |
| next pairs | K♣↔K♥ 0.251, K♣↔K♠ 0.250, K♣↔Q♥ 0.183 |
| pairs above 1/64 | **1311 of 1326** |
| mean over all pairs | 0.043 (same-rank pairs: 0.127) |

**What this is not.** It is not a distinguisher or a key-recovery attack on the full v10 cipher. SumRanks in v10 is position-aware and lets only about 1/221 of swaps through. The worst pair over a full round is Q♣↔K♣ at 1.40e-3 (analysis README §5). The product-formula estimate for the worst swap-only trail over 5 full rounds and the final round is (1.4e-3)⁵ × (1/221) ≈ **2e-17**, which matches the v10 SPEC heuristic and is not an attack at any practical data volume. The analysis itself concluded that nothing there *forces* a deprecation. v10 is being deprecated by the maintainer's decision, because one of its layers fails its design bar and so the margin the construction relies on is thinner than intended. It is not being deprecated because of a demonstrated break.

## What is proved, and what is only measured

| Claim | Status |
| --- | --- |
| There is a deck \(d\) with \(\mathrm{GC}(\sigma d) = \sigma\,\mathrm{GC}(d)\) and \(\sigma\,\mathrm{GC}(d) \ne \mathrm{GC}(d)\) for σ = K♣↔K♦ (card ids 12↔51) on the **emitted frozen v10 `mix_columns`** | **Kernel theorem** `DoubleDealV10.Witness.v10_KC_KD_swap_commutes_with_gridcycle` (`lean/DoubleDealV10/Witness.lean`). Both `mix_columns` evaluations are `decide!` (kernel reduction). **No `native_decide`.** `lean/Axioms.lean` together with `check_axioms.py v10-deprecated` shows only `propext` / `Classical.choice` / `Quot.sound`. Clean build about 30 s, so it runs in normal CI. It is **one deck**: an illustration, not a probability bound. |
| On a deck, GridCycle commutes with σ iff the seat walk is unchanged | Already a theorem for the model (`mixColumns_rel_iff_walk`, `proofs/doubledeal/security/DoubleDealSecurity/GridCycle.lean`). |
| The survival rates above, the 1311/1326 count, and the full-round figure | **Measured** ([`proofs/doubledeal/analysis/v10-gridcycle/`](../../doubledeal/analysis/v10-gridcycle/): `survival_value.log`, `mechanism.log`, `round.log`). Not theorems. |
| The ≈2e-17 six-round trail figure | **Estimate** (product formula, v10 SPEC). Not a theorem and not a bound. |

## Mechanism (K♣↔K♦)

Card \(c\): suit \(= \lfloor c/13\rfloor\) in GridCycle order ♣0 ♥1 ♠2 ♦3, rank \(= c \bmod 13 + 1\). A card steps the finger by (Δrow = suit, Δcol = rank) mod (4, 13).

- K♣ = (suit 0, rank 13) steps by (0, 0): the next target after K♣ is the seat K♣ itself is standing on, which is always taken, so **the card after K♣ is always blocked** and overflows. The v10 overflow scans the marker row \(t\) from the blocked column, and **the blocking card plays no part in where the next card lands**. Its landing seat depends only on \((t, \text{column}, \text{occupancy})\).
- K♦ = (suit 3, rank 13) steps by (3, 0): the next target after K♦ is the seat one row up (mod 4) in K♦'s column. If that seat is taken, the card after K♦ overflows from the same column with the same marker, which is exactly where the card after K♣ would have gone.
- So whenever the seat above is occupied at the two walk positions that hold K♣/K♦, swapping them leaves the walk unchanged, and the walk being unchanged is exactly the commutation condition. `proofs/doubledeal/analysis/v10-gridcycle/mechanism.log`: survival 0.2616; this sufficient condition holds 0.2583 of the time and is never true without survival. The residual 0.003 comes from K♣'s overflow landing exactly on K♦'s free target.
- K♣↔K♥ and K♣↔K♠ are the same effect with a different row offset. More generally, a card-blind overflow makes many pairs collide, which is why 1311/1326 pairs are above the bar.

The v11 fix (analysis PHASE2 rule 1 + PHASE6 tweak B) has three parts. (1) Ghost finger: each step starts from the previous target, not from where the card landed. (2) A blocked placement is scanned by the blocker: row = marker + blocker's suit, start column = target column + blocker's rank, first empty seat to the right, dropping a row if the row is full; the marker advances one suit. (3) Tweak B: after a blocked placement the finger moves to target + the blocker's step, and the next step starts there. Unblocked placements are as in v10. Measured worst pair: 0.0049 (≈1/205), with 0 pairs above 1/64.

## Reconciling with T1

T1 (`proofs/doubledeal/security/`) proves `mixColumns_commutes_iff_id`: GridCycle commutes with σ on **every** deck only when σ = id. That stays true: K♣↔K♦ fails on about 74% of decks. The weakness is about commutation on a large *fraction* of decks. "No non-identity relabelling commutes universally" does not imply "no transposition commutes often". The witness above is a concrete member of that fraction.

## Limits

- Per-layer evidence only. No distinguisher on the full cipher is claimed or known. The worst 6-round trail is estimated at about 2e-17.
- The rates are Monte-Carlo measurements with the CIs shown. The mechanism explanation is a checked sufficient condition, not a proof of the rate.
- The theorem is about the emitted Lean of the frozen sudo (Link 1, sudo text = emitted Lean, stays open as everywhere in the repo).

## Files

| Path | What |
| --- | --- |
| `witness_v10.json` | σ, deck, GC(deck), σ·deck, GC(σ·deck), the walk positions of the swapped cards. Written by `attack/make_witness.py` (seed 10) using the repo Python port (`ddport.mix_columns(d, 10)`); `--check` in CI. |
| `lean/` | Lake package `DoubleDealV10`. `WitnessData.lean` is generated by `witness_to_lean.py` (CI runs `--check`); `Witness.lean` holds the headline; `Axioms.lean` is the audit. It path-requires `lean/Generated/` (emitted by `proofs/emit_lean.sh doubledeal-v10`; do not edit). |
| `vectors/` | Frozen v10 vectors. `proofs/doubledeal/vectors/regen.sh v10 --check` rebuilds them from `v10/doubledeal_v10.sudo` through the sudoc JS target. |
| `attack/measure/` | `xcheck.py` (the analysis C model `proofs/doubledeal/analysis/v10-gridcycle/gc.h` == `ddport` v10 on 2000 decks; in CI) and `run.sh`, which reproduces the cited logs in the analysis folder (not in CI; about 10–20 CPU-minutes). The C sources and logs are not duplicated here. |

## Reproduce

Note: `attack/make_witness.py` and `attack/measure/xcheck.py` import the live repo port `proofs/doubledeal/security/checks/ddport.py` and call it as `mix_columns(d, 10)`, i.e. its frozen v10 code path; they do not carry their own copy of the port.


```sh
proofs/doubledeal/vectors/regen.sh v10 --check
python3 proofs/deprecated/doubledeal-v10/attack/make_witness.py --check
python3 proofs/deprecated/doubledeal-v10/lean/witness_to_lean.py --check
(cd proofs/deprecated/doubledeal-v10/lean && lake build)
python3 proofs/doubledeal/check_axioms.py v10-deprecated
python3 proofs/deprecated/doubledeal-v10/attack/measure/xcheck.py
proofs/deprecated/doubledeal-v10/attack/measure/run.sh   # slow, optional
```
