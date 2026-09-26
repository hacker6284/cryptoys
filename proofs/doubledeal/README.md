# DoubleDeal proofs

Normative definition: [`primitives/cipher/doubledeal/SPEC.md`](../../primitives/cipher/doubledeal/SPEC.md). Stones live in SPEC §6. This directory is the correctness ledger for those stones, not a second specification.

DoubleDeal is a toy block cipher. It has no cryptographic security claim. **This ledger tracks v9** (current). v8 is deprecated; its vulnerability proof is in [`../deprecated/doubledeal-v8/`](../deprecated/doubledeal-v8/).

> **Stage-1 status (v9 bump).** Generated Lean, TAP (10/10), and vectors are regenerated for v9. The algebraic stones and Link 2 still describe v8 SumRanks (rank-only columns) and v8 GridCycle overflow (scan from column 0); the affected theorems are listed in the v9 porting table below and stay OPEN until stage 2. The Lean package below proves **correctness / algebraic** facts (bijections, round-trip, content-preservation). It does **not** prove bit-security, MDS diffusion, or a strong key schedule.

## Layers (be honest)

Sudo is normative. Emitted Lean under `lean/Generated/` is the algorithm.
`lean/DoubleDeal/` is proof-only. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
This does **not** claim sudo↔Lean semantic-equivalence theorems. The
emit terminates gate is on. DoubleDeal production paths are bounded
`for` (PassKey drain, overflow scans `0 to 3`). Two test-only
kind-scan `while`s are stripped under the gate; JS still runs all
twelve sudo tests.

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the proof-only model** | Bijections, `encrypt6_rt` under Compose-key bijections, PassKey `F_inv ∘ F = id`, and the same round-trip with the algebraic PassKey schedule (`encryptDeckFn_rt`). | Lean kernel. `lake build` of the proof package. No `sorry`. No `native_decide`. **Not** the cipher. |
| **(b) Generated TAP** | `proofs/emit_lean.sh` → `lake` → `doubledeal_test` (10/10), including sudo's encrypt/decrypt and `passkey_inv` tests. Two kind-scan tests are stripped under `--require terminates`. | Compiled emitted Lean. **Not** a sudo=Lean theorem. |
| **(c) Skeleton vs JS JSON** | `lake exe doubledeal` vs `vectors/doubledeal_vectors.json` (from sudoc JS). | Evidence the *skeleton* matches those decks. OPEN that it equals `Generated.encrypt`. |
| **(d) Equivalence** | sudo text = generated Lean, or skeleton = generated. | OPEN (Link 1). |
| **(e) Link 2 refinement** | Algebraic stones ≃ Generated on the well-formed domain. | embed/decode, `drop_front` / `push_front` / `left_rotate` / `right_rotate`, `Generated.passkey` ≃ `passToKeyCutFallback` and `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list, S3/S4 on `Except Trap`, and `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages. Not emitter soundness. Not bit-security. See [`../LINK2.md`](../LINK2.md). |

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| S1 | Lay/scoop, SumRanks, ShiftRows, GridCycle, Compose are invertible as stated | Proved (GridCycle: `invMix ∘ Mix = id`) |
| S2 | Full / final round and Nr=6 encrypt/decrypt round-trip | Proved under abstract Compose-key bijections; concrete PassKey schedule inherits `encrypt6_rt` |
| S3 | PassKey is deterministic and content-preserving | Proved (`List.Perm`), including emitted `passkey` / `passkey_inv` on `FitsLen` |
| S4 | PassKey is injective (constructive inverse) | Proved on the list model and on emitted `passkey` / `passkey_inv` (`FitsLen` / `WellFormed`). Cycle structure is not. |
| S5 | Factoradic `unrankPerm` returns a permutation of its items | Proved; injectivity only for `3!` in Lean |
| S6 | CTR `counter_deck` length and nonce-prefix stability | Proved |
| S11 | Compose known-plaintext uniqueness; CTR nonce prefix | Proved at the Compose algebra layer |
| S12 | Full round peels as Compose ∘ unkeyed stem | Proved (definitional) |

## What is open or evidence-only

| Stone | Claim | Status |
| --- | --- | --- |
| S4 (orbits) | PassKey cycle structure / orbit lengths | Evidence only |
| S5 (full) | `unrankPerm` injective for `13!` / `52!` | Partial; `3!` is kernel `decide` |
| S7 | Hand sheet refines §3 math | Open |
| S8–S10 | Differentials, slide, randomness stats | Evidence only; never "security results" |
| S13 | §5.3 bytes ↔ deck | Evidence in `encoding.test.mjs` / `demos/doubledeal/cards.js` |
| — | sudo text equals generated Lean | OPEN (Link 1). Link 2 closes `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages and PassKey S3/S4 on `Except Trap`. Not emitter soundness. Not bit-security. |
| — | `mixColumns ∘ invMixColumns = id` on arbitrary packets | Open (needs image / seat characterization) |

## Lean packages

Two Lake packages, same toolchain **4.14.0**, no Mathlib.

**Generated (algorithm).** Do not edit. From the repo root:

```sh
proofs/emit_lean.sh doubledeal
cd proofs/doubledeal/lean/Generated && lake build && ./.lake/build/bin/doubledeal_test
```

Pin and regenerating: [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).

**Proof-only.** From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/doubledeal/lean
lake build
```

`lake exe doubledeal` prints a one-line summary **and** runs the skeleton-vs-JSON checks. The library target is `DoubleDeal`. Namespaces are `DoubleDeal`. Link 2 lives in `lean/DoubleDeal/Link2/` and path-requires `Generated/` (do not edit Generated).

Shipped theorems contain no `sorry` and no `native_decide`. The proofs CI job (`proofs.yml`) also emits Lean from `doubledeal.sudo` against the pin, builds `Generated/`, and runs TAP. Path filters: `proofs/**`, `primitives/cipher/doubledeal/**`, `primitives/hash/megadreifach/**`, `primitives/hash/scramble/**`, `tools/emit_lean.py`, and the workflow file.

### Regenerating vectors

Do not hand-edit `vectors/doubledeal_vectors.json` or `lean/DoubleDeal/Vectors.lean`. From the repo root, with network enough to clone [sudocode](https://github.com/hacker6284/sudocode) (same compiler as `.github/workflows/pages.yml`):

```sh
proofs/doubledeal/vectors/regen.sh
```

That checks out a **pinned** sudocode commit (`SUDOCODE_COMMIT` in `regen.sh`), builds `doubledeal.sudo` to JS, evaluates the published sudo tests plus extra KATs, writes the JSON (including `sudo_sha256` of the current `doubledeal.sudo` and that sudocode SHA), then emits `Vectors.lean`. CI fails if `sudo_sha256` no longer matches the file. If the JSON is already current:

```sh
python3 proofs/doubledeal/vectors/json_to_lean.py          # write Vectors.lean
python3 proofs/doubledeal/vectors/json_to_lean.py --check  # CI: stale Lean fails
```

Optional env: `SUDOC=/path/to/sudoc` or `SUDOCODE_DIR=/path/to/sudocode`.

## v9 porting table (stage 1 → stage 2)

v9 changes two layers (SPEC §3.3 A2, §3.5 B3; see SPEC §7a). The Generated tree, TAP, and vectors are v9. The hand-written algebraic model (`SumRanks.lean`, `GridCycle.lean`, `Round.lean`, `Concrete.lean`) and the Link 2 glue still describe **v8**. Rows marked **BROKEN** fail `lake build`. Rows marked **STALE** still compile, but they prove v8 facts and must be re-stated for v9. Measured on branch `doubledeal-v9` with Lean 4.14.0.

| File | Theorem / def | Status | Why | Stage-2 work |
| --- | --- | --- | --- | --- |
| `Link2/Compose.lean` | `compose_as_loop` (assert line) | fixed (mechanical) | sudo line shift, `sudoAssert false 219` → `221` | done |
| `Link2/SumLink.lean` | `sum_ranks_as_loop` (l. 324) | **BROKEN** (`rfl`) | the `colRankStep` mirror lacks `+ suit_of` | add the suit term to the mirror |
| `Link2/SumLink.lean` | `colRankStep`, `colRankStep_hit`, `colRank_pref`, `rank_loop`, `colsSummed`, `colsSummed_all`, `sumColStep_hit`, `col_loop`, `sum_ranks_refines` | STALE (only compile because they sit on top of the v8 mirror) | column weight is `cardRank` | re-thread with the column weight `rank + suit` |
| `Link2/Mix.lean` | `scanColStep`, `scanCol_hit`, `scan_loop`, `scanRowN_spec`, `scanFound_encode`, `attempt_refines` | STALE | the inner scan is now `col = (start + k) mod 13` | rotated-scan versions |
| `Link2/Mix.lean` | `overflowStep` / `overflow_as_loop` (l. 396–446) | **BROKEN** | `overflow_seat` takes a third argument, `start` | new mirror plus loop lemma |
| `Link2/Mix.lean` | `overflowStep_hit`, `overflow_fuel_some`, `overflow_seat_refines` (l. 448–537) | **BROKEN** | follow from the above | redo against the B3 `overflowSeat` |
| `Link2/Mix.lean` | `mixStep` def, `placeN_step` (l. 843–943) | **BROKEN** (type mismatch) | the `overflow_seat occ t tc` call | new mirror |
| `Link2/Mix.lean` | `mixStep_hit` (l. 1243), `mix_columns_as_loop` (l. 1391), `mix_columns_refines` | **BROKEN** | downstream | re-glue |
| `Link2/Encrypt.lean`, `DoubleDeal/Link2.lean` | `full_round_refines`, `final_round_refines`, `encrypt_refines`, `mix_bound` | blocked (these build once SumLink and Mix are stubbed) | imports | re-glue, small |
| `SumRanks.lean` / `Round.lean` | `sumRanks`, `invSumRanks_sumRanks`, `sumRanks_invSumRanks`; `Round` uses `sumRanks cardRank` | STALE | one weight for rows and columns | split into a row weight (`cardRank`) and a column weight (`cardRank + cardSuit`); the generic RT proofs should carry over |
| `GridCycle.lean` | `scanRow`, `overflowSeat`, `chooseSeat`, `invMixColumns_mixColumns`, `inv_place_agree` | STALE | the overflow scan starts at column 0 | scan from the blocked target's column; redo the inverse walk agreement |
| `Concrete.lean`, `VectorCheck.lean` (`lake exe doubledeal`) | encrypt/decrypt KATs | STALE: **15/35** vector checks pass against the v9 JSON | the skeleton is v8 | green once the two model changes land |

Link 1 (sudo = Generated) stays OPEN, as before. v8's own proofs are not kept alive under `deprecated/`; only its Generated TAP and the witness check are.

## Reading order

SPEC §6 suggested order: **S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7**, S13 as an encoding property test, and S8–S10 as living evidence. PassKey injectivity and content-preservation are proved on the list model and, on `FitsLen` / `WellFormed`, for emitted `Doubledeal.passkey` / `passkey_inv` (`Link2/PassKeyTransfer.lean`). `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages. NEXT is MegaDreifach Link 2 (see [`../LINK2.md`](../LINK2.md)). sudo already tests `passkey_inv` on several decks in Generated TAP. Not bit-security.

### Why PassKey is invertible

At step \(i\) the controller \(C\) is placed on top of the key pile, so the inverse can read it. Every branch (suit-rotate the hand; proper-cut the hand, the key, or neither) depends only on \(C\) and the two pile lengths — hand \(= 51-i\) after the pop, key \(= i\) — never on hidden card identities. So each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. `invPassKeyStep` undoes one step; `passToKeyCutFallbackInv` walks the composition backwards.
