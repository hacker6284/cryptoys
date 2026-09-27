# DoubleDeal v8 — vulnerability proof (DEPRECATED algorithm)

**Kind:** vulnerability proof (see [`proofs/README.md`](../../README.md) taxonomy). DoubleDeal v8 is deprecated and frozen at [`primitives/cipher/doubledeal/v8/`](../../../primitives/cipher/doubledeal/v8/). v9 (deprecated, draft; no successor yet) is still the live spec ([`primitives/cipher/doubledeal/SPEC.md`](../../../primitives/cipher/doubledeal/SPEC.md)). Nothing here is a claim about v9, and nothing here is a security claim.

**What is proved, and what is only measured:**

| Claim | Status |
| --- | --- |
| There is a key \(K\) and message \(M\) with \(E_K(\tau M) = \tau\,E_K(M)\) and \(\tau E_K(M) \ne E_K(M)\), on the full 6-round **emitted** v8 `encrypt`, for \(\tau\) = K♣↔K♦ | **Checkable witness, compiled evaluation**: `lake exe doubledeal_v8_witness` (TAP 2/2) runs emitted `Doubledeal_v8.encrypt` on `witness_v8.json`. The Lean data is generated from the JSON (`lean/witness_to_lean.py`, CI runs `--check`); kernel `decide` facts tie the JSON's \(\tau M\), \(\tau C\) to \(\tau\) applied cardwise and show \(\tau C \ne C\). Also checked on the sudo JS target (`attack/check_witness.mjs`) and the Python port. **Not a kernel theorem:** kernel `decide` on the full 6-round emitted `encrypt` exceeded ~14 GB RAM (killed, exit 137) on the build box, so it is not shipped. No `native_decide` is used anywhere. |
| Per-pair rate \(\approx 1.1\text{–}1.6\times10^{-3}\) for K♣↔K♦; decay \(\approx 0.27\times\) per round | **Evidence** (Python scripts below). Not a theorem. |
| Key recovery | **Not claimed.** This is a distinguisher. |

The Lean check is about `Doubledeal_v8.encrypt` in `lean/Generated/` (emitted from `doubledeal_v8.sudo` by `proofs/emit_lean.sh doubledeal-v8`). Link 1 (sudo text = emitted Lean) stays open, as everywhere in this repo; the JS target of the same sudo agrees on the witness (`attack/check_witness.mjs`).

## Mechanism (plain language)

A deck is a map from seats to cards. Every v8 layer only **moves cards between seats**:

1. **Compose** (AddRoundKey stand-in) moves seats by the key: \(\mathrm{Compose}(M,K) = M\circ K^{-1}\). Renaming card faces with any relabelling \(\tau\) commutes with it: \(\mathrm{Compose}(\tau M, K) = \tau\,\mathrm{Compose}(M,K)\).
2. **SumRanks** (SubBytes stand-in) chooses its row and column rotations from **rank** sums only. **ShiftRows** and lay/scoop are fixed. So if \(\tau\) keeps ranks (e.g. swaps K♣ and K♦), the whole SumRanks+ShiftRows stem commutes with \(\tau\) **with probability 1**.
3. **PassKey** never touches the message.
4. **GridCycle** (MixColumns stand-in) reads suits, so it is the only obstacle. But when both swapped cards' next step lands on an already-full seat, the v8 overflow rule (scan the marker row from column 0) picks the same seat whatever the suit. So GridCycle commutes with a same-rank swap about 7–18% of the time for a random suit pair, broadly rising with rank (`attack/per_layer.py`), and about 27% for K♣↔K♦ (one full round, `attack/relabel_attack.py`).

Five GridCycles sit between whitening and the final round. For \(\tau\) = K♣↔K♦, \(\Pr[E_K(\tau M) = \tau E_K(M)]\) is roughly \(0.27^5\) to \(0.28^5\) — about \(10^{-3}\) — for a random key and message. For an ideal cipher it is about \(1/52!\).

## Measured (evidence only)

`attack/relabel_attack.py` (64,000 pairs per row, 16 random keys; `attack/relabel_attack.log`):

| τ | full rounds | hits / 64,000 | rate |
| --- | --- | --- | --- |
| K♣↔K♦ | 1 | 17,105 | 2.7e-1 |
| K♣↔K♦ | 2 | 4,640 | 7.3e-2 |
| K♣↔K♦ | 3 | 1,237 | 1.9e-2 |
| K♣↔K♦ | 5 (real v8) | 100 | 1.6e-3 |
| control K♣↔Q♦ (different ranks) | 1, 2, 3, 5 | 0 | 0 |

An earlier independent run (analysis workspace) got 70 / 64,000 = 1.1e-3 at 5 full rounds; the two agree within noise for a rare event. With a random same-rank pair (not fixed K♣↔K♦) the rate is lower, about 1e-4: 32,768 chosen plaintexts per key distinguished 20/24 random keys (1.1e-4 per pair); control 0/24; a CTR chosen-nonce variant (nonces \(N\) and \(\tau N\), keystream read off known plaintext) 23/24 (1.6e-4 per pair) (`attack/success_rate.py`, deterministic seeds, `attack/success_rate.log`). An earlier run with process-salted seeds gave 19/24 and 21/24.

Distinguisher: ask for \(E_K(M)\) and \(E_K(\tau M)\) for about 3,000 random \(M\) with \(\tau\) = K♣↔K♦; answer "v8" on any hit. Success ≈ 95%; false-positive rate ≈ \(3000/52!\).

Other relations tried (`attack/gen_attack.py`, `attack/per_layer.py`, logs alongside): same-suit swaps, whole-suit swaps, rank shifts, id+4, id+13 give no exact hits; counting seats where \(E_K(\tau M)\) and \(\tau E_K(M)\) agree gives no signal (mean ≈ 1.0, like random). The relation is all-or-nothing.

## Limits (honest)

- Distinguisher, not key recovery. No attack on the key is known here.
- The rate is measured, not proved. The witness shows the relation holds on one concrete input, which is what a vulnerability-proof witness is; it is not a probability bound.
- The witness is checked by compiled evaluation (Lean exe, JS, Python), not by the Lean kernel. Future work: a kernel check, e.g. per-round `decide` chained through a v8 Link 2 `encrypt_as_loop`, or kernel evaluation on the algebraic `encryptDeck` plus a v8 `encrypt_refines`.
- Statements are about the emitted Lean and the Python/JS ports of the frozen sudo, not a sudo↔Lean theorem.

## Files

| Path | What |
| --- | --- |
| `witness_v8.json` | \(\tau\), key, message, cipher, \(\tau M\), \(\tau C\) |
| `lean/` | Lake package: `DoubleDealV8/WitnessData.lean` (generated from `witness_v8.json` by `witness_to_lean.py`; do not edit), `DoubleDealV8/Witness.lean` (`enc` = emitted v8 `encrypt`, kernel facts `messageTauJson_eq`, `cipherTauJson_eq`, `cipherTau_ne`), `WitnessMain.lean` (compiled TAP check). Path-requires `lean/Generated/` (emitted, do not edit). |
| `vectors/doubledeal_v8_vectors.json` | Frozen v8 known-answer vectors (29). `vectors/regen_v8.sh --check` rebuilds them from `v8/doubledeal_v8.sudo` via the sudoc JS target and requires a byte-identical file |
| `attack/dd_v8.py` | Python port of `v8/doubledeal_v8.sudo` (29/29 on the frozen vectors via `check_vectors.py`, which also checks their `sudo_sha256`) |
| `attack/find_witness.py` | Search that produced the witness (739 trials) |
| `attack/check_witness.mjs` | JS target of `doubledeal_v8.sudo` on the witness |
| `attack/relabel_attack.py`, `success_rate.py`, `gen_attack.py`, `per_layer.py` | Evidence scripts (deterministic seeds) and their `.log` outputs |

## Reproduce

```sh
# Emitted v8 Lean + TAP
proofs/emit_lean.sh --check doubledeal-v8
cd proofs/deprecated/doubledeal-v8/lean/Generated && lake build && ./.lake/build/bin/doubledeal_v8_test
# Witness (compiled check)
cd .. && python3 witness_to_lean.py --check && lake build && lake exe doubledeal_v8_witness
sudoc build --target js -o /tmp/dd-v8-js primitives/cipher/doubledeal/v8/doubledeal_v8.sudo && node attack/check_witness.mjs /tmp/dd-v8-js
# Evidence
vectors/regen_v8.sh --check
python3 attack/check_vectors.py && python3 attack/relabel_attack.py 64000 16 1,2,3,5
python3 attack/success_rate.py && python3 attack/gen_attack.py && python3 attack/per_layer.py
```
