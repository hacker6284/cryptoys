# DoubleDeal v9: vulnerability proof (DEPRECATED algorithm, draft)

**Kind:** vulnerability proof (see the [`proofs/README.md`](../../README.md) taxonomy). **Status: draft, awaiting Zachary's decision.** This folder freezes DoubleDeal v9 at [`primitives/cipher/doubledeal/v9/`](../../../primitives/cipher/doubledeal/v9/) following the v8 precedent. **No successor has been chosen.** Until one is chosen, the live [`SPEC.md`](../../../primitives/cipher/doubledeal/SPEC.md) and `doubledeal.sudo` still describe v9 byte for byte, and so do `proofs/doubledeal/`, the demo and the CBC-HMAC composition. Candidate fixes are measured in [`candidates/CANDIDATES.md`](candidates/CANDIDATES.md) as analysis only. Nothing here is a security claim, and nothing here changes the spec.

## What is proved, and what is only measured

| Claim | Status |
| --- | --- |
| There is a key \(K\) and a message \(M\) with \(E_K(\sigma M) = \sigma E_K(M)\) and \(\sigma E_K(M) \ne E_K(M)\) on the full emitted v9 `encrypt` (whitening, 5 full rounds, final round, PassKey schedule), for \(\sigma\) = K♣↔Q♥ (card ids 12↔24) | **Kernel theorem** `DoubleDealV9.Witness.v9_KC_QH_swap_commutes_on_witness` in `lean/DoubleDealV9/Witness.lean`. The stages are checked with `decide!` (kernel reduction): six PassKey steps, then whitening, 5 rounds and the final round for \(M\) and for \(\sigma M\). They are chained by the generic lemmas in `Glue.lean`. **No `native_decide`.** `lean/Axioms.lean` together with `check_axioms.py v9-deprecated` shows it depends only on `propext` and `Quot.sound`. Build on the shared box: 659 s wall, peak ≈ 10.8 GB total Lean RSS. One PassKey `decide!` is ≈ 46 s and 5.2 GB. A single `decide!` over the whole `expand_keys` was OOM-killed at 12.8 GB, and that is why the proof is split into stages. |
| Equal-w4 swaps commute with v9 SumRanks on every deck where the two cards share a row (and so, for K♣↔Q♥ in particular) | **Kernel theorem** (Mathlib package): `DoubleDeal.Security.sumRanksV9_swap_commutes_of_same_row` and `sumRanksV9_KC_QH_of_same_row` in [`proofs/doubledeal/security/DoubleDealSecurity/SwapMechanism.lean`](../../doubledeal/security/DoubleDealSecurity/SwapMechanism.lean). This is one direction of the SumRanks condition below. |
| Per-layer survival probabilities, the ≈1/23 per-round rate, F6 ≈ 3.5e-8, and the vulnerable class | **Measured** (`attack/mechanism.py`, `attack/mechanism.log`, `attack/results/`). Not a theorem. The ≈12/51 SumRanks share is exact counting for a uniform deck. The GridCycle share has a model that is approximate only. |
| Key recovery | **Not claimed.** This is a distinguisher. |

As everywhere in the repo, Link 1 (sudo text = emitted Lean) stays open. The JS target of the frozen sudo and the Python port `attack/dd_v9.py` agree on all 14 recorded F6 witnesses (`attack/verify_witness.mjs`, `attack/check_witnesses.py`).

## Mechanism, layer by layer

Notation: card \(c \in 0..51\), rank \(= c \bmod 13 + 1\) (A=1 … K=13), suit \(= \lfloor c/13\rfloor\) (♣♥♠♦). A relabelling \(\sigma\) renames card faces. "Commutes" means \(L(\sigma x) = \sigma L(x)\) for a layer \(L\). The ciphertext relation holds exactly when every layer applied along the way commutes on the state it actually receives.

**Correction to a common description:** v9 SumRanks rotates **rows** by Σrank mod 13 (rank only) and **columns** by Σ(rank+suit) mod 4. Only the column weight involves the suit. Write \(w_4(c) = (\text{rank}+\text{suit}) \bmod 4\).

| Layer | When it commutes with \(\sigma = x \leftrightarrow y\) | Probability per use, K♣↔Q♥ |
| --- | --- | --- |
| Compose (AddRoundKey stand-in), lay/scoop, ShiftRows | Always. These are positional: they move seats and never read faces. | 1 |
| PassKey | Never touches the message. | n/a |
| SumRanks (SubBytes stand-in) | Exactly when (\(x, y\) are in the same row **or** have equal rank) **and** (they are in the same column after the row step **or** have equal \(w_4\)). The row sums are symmetric in the row's cards, so swapping two cards inside one row changes no row sum. K♣ has \(w_4 = 13 \bmod 4 = 1\) and Q♥ has \(w_4 = 13 \bmod 4 = 1\), and their ranks differ. | 12/51 = 0.2353 exactly (uniform deck: the other card is in the same row). Measured 0.2363. |
| GridCycle (MixColumns stand-in) | Exactly when the seat chosen for the card after \(x\) equals the seat chosen for the card after \(y\). | ≈ 0.184 measured (see below) |

**Why GridCycle survives so often for K♣↔Q♥.** K♣ = (suit 0, rank 13). Its step (Δrow 0, Δcol 13 ≡ 0) targets its own seat, so K♣ **always overflows** and scans the marker row \(t\) from its column \(c\). Q♥ targets \((r+1, c-1)\). If that seat is blocked, Q♥ scans row \(t\) from \(c-1\). The two choices coincide when \((r+1, c-1)\) is occupied and the scan from \(c\) and from \(c-1\) lands on the same cell. That holds when \((t, c-1)\) is already occupied, which is the same cell when \(t = r+1\) (≈ 0.47 of the time, because after an overflow the marker is row+1). A per-position model \(f(i) = \varphi(q + (1-q)\varphi)\), \(\varphi = i/51\), \(q \approx 0.47\), gives \(P_G \approx 0.169\), against 0.184 measured. Other pairs lack the self-blocking card, so their GridCycle survival is lower (mean 0.038 over the equal-w4 class).

**Per-round rate.** \(P_S \cdot P_G \approx 0.2363 \times 0.1834 = 0.0433 \approx 1/23\). The rounds are close to independent because Compose with a fresh round key re-randomises seats. Product formula: \(F_r \approx P_S^{\,r} P_G^{\,r-1}\) (the final round has SumRanks but no GridCycle) and \(E_r \approx (P_S P_G)^r\).

| target | measured | predicted | meas/pred |
| --- | --- | --- | --- |
| F2 | 1.04e-2 (1043/1e5) | 1.03e-2 | 1.02 |
| F3 | 4.37e-4 (873/2e6) | 4.45e-4 | 0.98 |
| F4 | 1.81e-5 (290/2e7) | 1.93e-5 | 0.94 |
| F5 | 7.44e-7 (119/2e8) | 8.39e-7 | 0.89 |
| **F6 (real v9)** | **3.5e-8 (14/4e8)** | **3.64e-8** | 0.96 |
| E2, E3 | 1.73e-3, 7.77e-5 | 1.88e-3, 8.18e-5 | 0.92, 0.95 |

An ideal cipher gives ≈ 1/52!. Distinguisher: query \(E_K(M)\) and \(E_K(\sigma M)\) for about \(10^8\) random \(M\) and answer "v9" on any hit.

## The vulnerable class

- **Different rank and different \(w_4\)** (936 of the 1326 transpositions): SumRanks never commutes, so the rate is exactly 0 per round.
- **Equal \(w_4\), different rank** (312 pairs): \(P_S \approx 12/51\) for all of them. \(P_G\) ranges from 0.014 to 0.184. Predicted F6 has median 4e-12 and max 3.7e-8 (K♣↔Q♥). The top pairs have Δ(suit, rank) = (+1, −1): K♣Q♥ (1/23 per round), Q♣J♥ (1/36), J♣T♥ (1/38), and so on. Next come A♥K♥ and A♣K♣ (A and K are adjacent mod 13 and equal mod 4) and the (+3, +1) family (J♣Q♦, …). The full table is in `attack/results/mechanism_pairs.json`.
- **Same rank** (78 pairs, the v8 family): \(P_S \approx 3/51\) (same column after the row step, or same row and equal \(w_4\)). \(P_G\) mean 0.127. Predicted F6 max 4.9e-11. v9 did weaken the v8 attack. It did not remove the class.

## Reconciling with T1 (WeightShift, "v9Sym has no transpositions")

The T1 results in `proofs/doubledeal/security/` are statements about **all** decks. They say which relabellings commute with SumRanks on every deck (the WeightShift group v9Sym, 51 elements, no transpositions), and that GridCycle commutes with σ on every deck only when σ = id (`mixColumns_commutes_iff_id`). Consequences such as `encrypt6_not_commutes_v9Sym` are also universal statements. Both remain true. The attack needs commutation only on the decks the cipher actually visits, with non-negligible probability: K♣↔Q♥ commutes with SumRanks on 12/51 of decks and fails on the rest, so it is correctly excluded from v9Sym. "No transposition commutes universally" does not imply "no transposition commutes often". The new lemma `sumRanksV9_swap_commutes_of_same_row` makes the 12/51 set explicit. v9Sym itself gives nothing: SumRanks commutes on all decks, GridCycle and the full round 0/1,020,000, and v9Sym(0,1) F2 0/1e6 (`candidates/measure.log`).

## Limits

- This is a distinguisher, not key recovery.
- The rates are measured. The Lean theorem is one concrete input pair, which is what a vulnerability-proof witness is. It is not a probability bound. The GridCycle model is a heuristic (it predicts 0.169 against 0.184 measured).
- The theorem is about the emitted Lean of the frozen sudo, not a sudo↔Lean theorem.

## Files

| Path | What |
| --- | --- |
| `witness_v9.json` | σ, key, message, cipher, σM, σC, plus hints (round keys, per-stage states) that the Lean proof uses as intermediate values. It comes from F6 witness #0 (`attack/make_witness.py`). |
| `lean/` | Lake package `DoubleDealV9`. `WitnessData.lean` is generated by `witness_to_lean.py` (CI runs `--check`). The package also contains `Glue.lean`, `Keys.lean`, `RunM.lean`, `RunSigma.lean` and `Witness.lean` (headline), plus `Axioms.lean`. It path-requires `lean/Generated/` (emitted by `proofs/emit_lean.sh doubledeal-v9`; do not edit). |
| `vectors/` | Frozen v9 vectors. `regen_v9.sh --check` rebuilds them from `v9/doubledeal_v9.sudo` through the sudoc JS target. |
| `attack/dd_v9.py`, `check_vectors.py` | Python port and its check (sudo sha plus vectors) |
| `attack/dd9.c`, `dd9.py`, `check_port.py` | Fast C port (numpy/ctypes), checked against `dd_v9.py` and the vectors |
| `attack/mechanism.py`, `layers.c`, `mechanism.log` | The per-layer measurements and the class scan above |
| `attack/lowdiff.py`, `relations.py`, `scan.py`, `stats.py`, `summarize.py`, `NOTES.md`, `results/` | The original reduced-round analysis that found the break (1326 transpositions at E2/F2/F3, the 12↔24 scaling to F6) |
| `attack/verify_witness.mjs`, `check_witnesses.py` | All 14 F6 witnesses on the JS target and on the Python port |
| `candidates/` | Candidate-fix analysis: `candidates/CANDIDATES.md` (table), `candidates/measure.log` (raw run) |

## Reproduce

```sh
proofs/deprecated/doubledeal-v9/vectors/regen_v9.sh --check
python3 proofs/deprecated/doubledeal-v9/attack/check_vectors.py
python3 proofs/deprecated/doubledeal-v9/attack/check_port.py
python3 proofs/deprecated/doubledeal-v9/attack/check_witnesses.py
(cd proofs/deprecated/doubledeal-v9/attack && python3 mechanism.py 400000 7)   # ~1 min
(cd proofs/deprecated/doubledeal-v9/lean && python3 witness_to_lean.py --check && lake build)  # ~11 min, ~11 GB
python3 proofs/doubledeal/check_axioms.py v9-deprecated
```
