<!-- Owns: the DoubleDeal proof ledger (what is proved, what is open, how to build and check it) and the per-version record of what changed in the proofs. Maintenance rules: ../../DOCS.md. -->
# DoubleDeal proofs

Normative definition: [`primitives/cipher/doubledeal/SPEC.md`](../../primitives/cipher/doubledeal/SPEC.md). Stones live in SPEC §6. This directory is the correctness ledger for those stones, not a second specification.

DoubleDeal is a toy block cipher. It has no cryptographic security claim. **This ledger tracks v12.** Version history: [SPEC §7a](../../primitives/cipher/doubledeal/SPEC.md#7a-version-history). Frozen versions and their write-ups: [`../deprecated/`](../deprecated/README.md). What changed in these proofs per version: [v12](#v12-changes), [v11](#v11-changes), [v10](#v10-changes), [v9](#v9-changes-historical).

> **Status: v12.** Generated Lean, TAP, vectors, the algebraic model and Link 2 all describe v12 (see "v12 changes" below; GridCycle is still v11's, see "v11 changes"; SumRanks is still v10's, see "v10 changes"). `lake build` is green with no `sorry` and no `native_decide`, `lake exe doubledeal` passes every known-answer vector, and `check_axioms.py` (run in CI) confirms the top theorems in [`lean/Axioms.lean`](lean/Axioms.lean) use only propext, Classical.choice and Quot.sound. The Lean package proves **correctness / algebraic** facts (bijections, round-trip, content-preservation). It does **not** prove bit-security, MDS diffusion, or a strong key schedule.

## Layers (be honest)

Sudo is normative. Emitted Lean under `lean/Generated/` is the algorithm.
`lean/DoubleDeal/` is proof-only. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
This does **not** claim sudo↔Lean semantic-equivalence theorems. The
emit terminates gate is on. DoubleDeal production paths are bounded
`for` (PassKey drain, overflow scans `0 to 3`). Two test-only
kind-scan `while`s are stripped under the gate; JS runs every sudo
test.

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the proof-only model** | Bijections, `encrypt6_rt` under Compose-key bijections, PassKey `F_inv ∘ F = id`, and the same round-trip with the algebraic PassKey schedule (`encryptDeckFn_rt`). | Lean kernel. `lake build` of the proof package. No `sorry`. No `native_decide`. **Not** the cipher. |
| **(b) Generated TAP** | `proofs/emit_lean.sh` → `lake` → `doubledeal_test` (every emitted sudo `test` passes), including sudo's encrypt/decrypt and `passkey_inv` tests. Two kind-scan tests are stripped under `--require terminates`. | Compiled emitted Lean. **Not** a sudo=Lean theorem. |
| **(c) Skeleton vs JS JSON** | `lake exe doubledeal` vs `vectors/doubledeal_vectors.json` (from sudoc JS). | Evidence the *skeleton* matches those decks. OPEN that it equals `Generated.encrypt`. |
| **(d) Equivalence** | sudo text = generated Lean, or skeleton = generated. | OPEN (Link 1). |
| **(e) Link 2 refinement** | Algebraic stones ≃ Generated on the well-formed domain. | embed/decode, `drop_front` / `push_front` / `left_rotate` / `right_rotate`, `Generated.passkey` ≃ `passToKeyCutFallback` and `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list, S3/S4 on `Except Trap`, and `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages. Not emitter soundness. Not bit-security. See [`../LINK2.md`](../LINK2.md). |

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| S1 | Lay/scoop, SumRanks, ShiftRows, GridCycle, Compose are invertible as stated | Proved (GridCycle: `invMix ∘ Mix = id` and `Mix ∘ invMix = id`, every packet `Fin 52 → Nat`) |
| S2 | Full / final round and Nr=6 encrypt/decrypt round-trip | Proved under abstract Compose-key bijections, both directions (`encrypt6_rt`, `encrypt6_decrypt6`); concrete PassKey schedule inherits both (`encryptDeckFn_rt`, `encryptDeckFn_decryptDeckFn`) |
| S3 | PassKey is deterministic and content-preserving | Proved (`List.Perm`), including emitted `passkey` / `passkey_inv` on `FitsLen` |
| S4 | PassKey is injective (constructive inverse) | Proved on the list model (PR #3) and on emitted `passkey` / `passkey_inv` (`FitsLen` length and cards / `WellFormed`). Cycle structure is not. |
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
| S13 | §5.3 bytes ↔ deck | Evidence in [`encoding.test.mjs`](../../primitives/cipher/doubledeal/encoding.test.mjs) / [`demos/doubledeal/cards.js`](../../demos/doubledeal/cards.js) |
| — | sudo text equals generated Lean | OPEN (Link 1). Link 2 closes `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages and PassKey S3/S4 on `Except Trap`. Not emitter soundness. Not bit-security. |

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

Shipped theorems contain no `sorry` and no `native_decide`. The proofs CI workflow ([`proofs.yml`](../../.github/workflows/proofs.yml)) also emits Lean from `doubledeal.sudo` against the pin, builds `Generated/`, and runs TAP.

### Regenerating vectors

Do not hand-edit `vectors/doubledeal_vectors.json` or `lean/DoubleDeal/Vectors.lean`. From the repo root, with network enough to clone [sudocode](https://github.com/hacker6284/sudocode):

```sh
proofs/doubledeal/vectors/regen.sh            # current; also v8 | v9 | v10 | v11
proofs/doubledeal/vectors/regen.sh --check    # CI (generated-fresh): byte-identical or fail
```

That checks out the **pinned** sudocode commit ([`proofs/SUDOCODE_PIN`](../SUDOCODE_PIN), the same pin as the Lean emitter), builds `doubledeal.sudo` to JS, evaluates the published sudo tests plus extra KATs, writes the JSON (including `sudo_sha256` of the current `doubledeal.sudo` and that sudocode SHA), then emits `Vectors.lean`. CI fails if `sudo_sha256` no longer matches the file. If the JSON is already current:

```sh
python3 proofs/doubledeal/vectors/json_to_lean.py          # write Vectors.lean
python3 proofs/doubledeal/vectors/json_to_lean.py --check  # CI: stale Lean fails
```

Optional env: `SUDOC=/path/to/sudoc` or `SUDOCODE_DIR=/path/to/sudocode`.

## v12 changes

v12 changes the key schedule only: the PassKey step \(F\) (SPEC §3.7, §4.6, §7a; analysis [`analysis/passkey-related-key/`](analysis/passkey-related-key/) §9, the key-pile fallback). What changed in the proofs:

- **Model (`lean/DoubleDeal/PassKey.lean`).** `dealUnder xs m = xs.drop m ++ (xs.take m).reverse` and `undealUnder` (the sudo `deal_under` / `undeal_under`), `dealCount c = suit c + 2`, and `maybeDeal` / `maybeDealInv` (hand / key pile / skip, the same `dif` shape as `maybeCut`) replace the suit rotation. `passKeyStep` is `maybeDeal`, then `maybeCut`, then the controller on the key pile; `invPassKeyStep` is `maybeCutInv`, then `maybeDealInv`. **`passKey_leftInverse`, `passKey_rightInverse`, `passKey_injective`, `passToKeyCutFallback_perm` and the per-step inverse lemmas are unchanged in statement** and re-proved. New: `undealUnder_perm`, `maybeDealInv_perm`, `maybeCutInv_perm`, `invPassKeyStep_perm`.
- **Link 2 (`Link2/Deal.lean`, `Link2/PassKey.lean`, `Link2/PassKeyInv.lean`).** `deal_under_refines` / `undeal_under_refines` / `deal_step_refines` / `undeal_step_refines` cover the new emitted helpers; both twin-loop refinements are redone on top of them. **Statement change:** `passkey_refines` and `passkey_inv_refines` now also assume `∀ c ∈ deck, FitsLen c`. The emitted `suit_of(c) + 2` is an i64 addition, so a card above `i64Max − 2` makes the emitted code trap; v11 only compared and rotated, so it was total on every `Nat` card. The same hypothesis is threaded through `passkey_singleton`, `passkey_refines_nil_and_singleton` and the S3/S4 transfers (`passkey_perm`, `passkey_inv_perm`, `passkey_leftInverse`, `passkey_rightInverse`, `passkey_injective`, `passkey_inv_injective`); `WellFormed` gains a matching `cards` field, so the `_wf` forms keep their statements and `wellFormed_embed` takes the card bound. **`encrypt_refines` is unchanged in statement**: `Link2/Expand.lean` gets the card bound from `Perm52` (cards < 52).
- **Security package.** `DoubleDealSecurityHeavy/RealKey.lean` has new expected ciphertexts (the key schedule changed; five identity-key encryptions from `checks/realkeys/v10sym_subgroup.py` on the v12 port); its headline `generated_encrypt_realKey_not_v10Sym_equivariant` is unchanged. The `Link.lean` K♣↔K♦ `decide!` witness still holds under v12 with the same message and key. Nothing else in the package reads PassKey's internals.
- **Port and checks.** `security/checks/ddport.py` has `passkey(deck, v)` / `passkey_inv(deck, v)` / `expand_keys_v(k0, v)` (the `f(x, v)` convention; v < 12 falls back to the frozen v8 suit rotation); v12 `encrypt` matches all 19 applicable live vectors (including the `passkey` and `expand_keys` ones), and `selftest.py` checks the v12 PassKey inverse on 300 random decks. `check_relabel.py` adds v12 at the encrypt level ([4]) and a v12 PassKey value-dependence line ([5]); the earlier lines of its log are byte-identical. `check_covariant.py` checks the unkeyed round body, which v12 does not change, so it still runs v8–v11.
- **Not claimed.** Nothing here is a security claim. The v12 numbers (worst swap through one pass ≈ 1/506, no exact per-step collision, six passes 0/200k for the worst pair) are sampled measurements and a closed-form count in the analysis folder, not Lean proofs.

## v11 changes

v11 changes one layer: GridCycle (SPEC §3.5, §4.4, §7a; analysis rule 1 + tweak B, [`analysis/v10-gridcycle/`](analysis/v10-gridcycle/) PHASE2 and PHASE6). What changed in the proofs:

- **Model (`lean/DoubleDeal/GridCycle.lean`).** `WalkState` now carries the finger (in `prev`, next to the last card) and the table so far (`board`, so a blocked placement can read its blocker). `overflowSeat occ row start` drops rows and no longer returns a marker; the new `blockedChoice` does the v11 blocked step; `chooseSeat?` / `chooseSeat!` return a `SeatChoice` (seat, next marker, next finger). `chooseSeat?_isSome`, `chooseSeat!_free`, `placeN_count`, `inv_place_agree` and **`invMixColumns_mixColumns` are unchanged in statement** and re-proved. In the inverse, `board` is the part of the laid table already visited, which is exactly what a decryptor reads the blocker from.
- **Link 2 (`Link2/Mix.lean`).** **`mix_columns_refines` is unchanged in statement** (`CardBound` hand) and re-proved against the new emitted loop: its state is (finger row, finger column, marker, grid, previous card); new lemmas cover the blocked branch (`chooseSeat!_blocked`, `blocked_after`, `placeN_board`, …) and the emitted `overflow_seat`. `encrypt_refines`, `full_round_refines`, `final_round_refines` and every downstream theorem are unchanged in statement and still build.
- **Security package (T1 and friends).** `Walk.Chooser` now returns a `SeatChoice`. The frozen v8 chooser (`GridCycle.V8`) is re-expressed on the new interface with its old semantics (scan from column 0, next marker = row after the one used, finger = landed seat); `V8Vectors` still pins it to the frozen v8 vectors. All GridCycle statements are **unchanged** and re-checked for v11, including the kernel `decide!` witnesses `seat2_inj` (second seat injective except K♣/K♠, still true under v11), `mixColumns_KC_KD_fails`, `mixColumns_KC_KS_fails`, `V8.seat2_eq`, and hence `mixColumns_commutes_iff_id` (GridCycle commutes only with the identity) and the v8 analogue. `BranchNumber`, `PermKeys`, `Rounds`, `Link` and `RealKey` are unchanged in statement. The heavy `DoubleDealSecurityHeavy/RealKey.lean` has new expected ciphertexts (five identity-key encryptions, from `checks/realkeys/v10sym_subgroup.py` on the v11 port); its headline `generated_encrypt_realKey_not_v10Sym_equivariant` is unchanged.
- **Right inverse (added after v11 landed).** `mixColumns_invMixColumns : mixColumns (invMixColumns packet) = packet` for every `packet : Fin 52 → Nat` (no deck hypothesis): the encrypt walk on `invMixColumns packet` goes through exactly the decrypt walk's states, and after 52 steps every seat is occupied, so it rebuilds the laid grid. Lifted to the skeleton (`encrypt6_decrypt6`, assuming only the left-inverse key facts `invPos (pos j) = j` for the whitening, mix and final keys) and to the PassKey schedule (`encryptDeckFn_decryptDeckFn`, `Perm52 key`). Not lifted to the emitted `Generated.encrypt` / `Generated.decrypt`: there is no Link 2 refinement for `decrypt`. The security package's local copy of `unkeyedNoMix_invUnkeyedNoMix` moved to core. `encryptN_rt` / `encrypt6_rt` lost their unused `h0L` argument (conclusions unchanged; `encryptDeckFn_rt` unchanged).
- **Still a conjecture.** `Rounds.roundBody_covariant_iff_id` keeps its allowlisted `sorry` (now read for v11; `check_covariant.py` finds no covariant σ for v11 either: 0/1326 transpositions, 0/51 nontrivial v10Sym, 0/200 random). Nothing was restated or weakened.
- **Port and checks.** `security/checks/ddport.py` has the v11 walk (matches the sudo and the analysis variant 62); `selftest.py`, `check_relabel.py`, `check_covariant.py` cover v11 (logs regenerated). Under v11, K♣↔K♦ commutes with GridCycle on 57/20000 random decks (v10: about 5200/20000).
- **Not claimed.** Nothing here is a security claim. The GridCycle parity measurements (worst single swap ≈ 0.0049, 0/1326 above 1/64) are sampled measurements in the analysis branch, not proofs or bounds.

## v10 changes

v10 changes one layer: SumRanks (SPEC §3.3, §7a; candidate W5c). The model is [`lean/DoubleDeal/SumRanksV10.lean`](lean/DoubleDeal/SumRanksV10.lean):

- **Round trip.** `invSumRanksV10_sumRanksV10` and `sumRanksV10_invSumRanksV10` (both directions, all grids). They rest on a generic chain lemma (`sumRanksChain` / `invSumRanksChain`): each step turns one line by an amount read from a line that is already final, and for columns also from a quantity the turn does not change (`OwnInvariant`: the XOR of a column's own suit labels is rotation invariant, `colTurnV10_ownInvariant`). Both theorems are in `Axioms.lean` and checked by `check_axioms.py`.
- **Round.** `unkeyedNoMix` / `invUnkeyedNoMix` now use `sumRanksV10`; `encrypt6_rt`, `encryptDeckFn_rt` and every downstream round-trip theorem are unchanged in statement. The old two-weight `sumRanks` (v8/v9) stays in `SumRanks.lean` for the frozen models; `cardColumnWeight` is kept and documented as the deprecated v9 weight.
- **Link 2.** `Link2/SumLink.lean` was rewritten: every emitted v10 helper (`row_total`, `row_turn`, `sum_rows`, `suit_label`, `gf_add`, `gf_times_w`, `column_value`, `column_suits`, `column_turn`, `turn_column`, `sum_columns`) has a refinement lemma, and `sum_ranks_refines` now says `sum_ranks (embedGrid g) = .ok (embedGrid (sumRanksV10 g))` for every grid (the v9 version needed `CardBound` cells). `encrypt_refines` is unchanged in statement.
- **Compiled evaluation.** The chained model, read naively as nested closures, is exponential when compiled (each step re-reads earlier steps). `SumRanksV10.lean` therefore carries a list implementation with `@[csimp]` lemmas (`sumRanksV10_eq_LL`, `invSumRanksV10_eq_LL`) proved equal to the model; `lake exe doubledeal` uses it. Kernel proofs never see the list version.
- **Relabelling symmetry (security package).** `sumRanksV10_commutes_iff`: a relabelling σ commutes with v10 SumRanks on every deck iff σ is one of the 52 `v10Sym a x` (rank + a mod 13, GF(4) suit label ⊕ x), the v10 analogue of v9's `sumRanks_commutes_iff`. This is about exact symmetry only.
- **Not claimed.** Nothing here is a security claim. The empirical W5c measurements (swap survival, hand cost) are in [`analysis/v10-sumranks/`](analysis/v10-sumranks/) and are measurements, not proofs.

## v9 changes (historical)

v9 changes two layers (SPEC §3.3 A2, §3.5 B3; see SPEC §7a). **A2:** SumRanks takes separate weights, rank for rows and `cardColumnWeight` = rank + suit for columns (`sumRanks cardRank cardColumnWeight`; the round-trip theorems hold for any pair of weights). In Link 2, `sum_ranks_refines` follows the emitted `column_weight`; because suit grows with the card id it needs `CardBound` cells, the same bound `encrypt_refines` already puts on messages. **B3:** the GridCycle overflow scan starts at the blocked target's column (`rotCol`, `scanRow occ row start`, `overflowSeat occ t start`). `invMixColumns_mixColumns` needed no change, because the forward and inverse walks share `chooseSeat!`. In Link 2, `scan_row_refines` covers the emitted `scan_row` helper, and `overflow_seat_refines` / `mix_columns_refines` sit on top of it. The emitted asserts in `index_of` and `overflow_seat` are matched as `∃ ln` (witness by `rfl`), so sudo edits that move a line no longer reach into Link 2.

Link 1 (sudo = Generated) stays OPEN, as before. v8's own proofs are not kept alive under `deprecated/`; only its Generated TAP and the witness check are.

## Reading order

SPEC §6 suggested order: **S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7**, S13 as an encoding property test, and S8–S10 as living evidence. PassKey injectivity and content-preservation are proved on the list model and, on `FitsLen` (length and cards) / `WellFormed`, for emitted `Doubledeal.passkey` / `passkey_inv` (`Link2/PassKeyTransfer.lean`). `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages (see [`../LINK2.md`](../LINK2.md)). sudo already tests `passkey_inv` on several decks in Generated TAP. Not bit-security.

### Why PassKey is invertible

See SPEC [§3.7](../../primitives/cipher/doubledeal/SPEC.md#37-passkey-f) ("Why"). In Lean, `invPassKeyStep` undoes one step; `passToKeyCutFallbackInv` walks the composition backwards.
