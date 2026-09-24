# TwoDeck proofs

Normative definition: [`primitives/cipher/twodeck/SPEC.md`](../../primitives/cipher/twodeck/SPEC.md). Stones live in SPEC §6. This directory is the correctness ledger for those stones, not a second specification.

TwoDeck is a toy block cipher. It has no cryptographic security claim. The Lean package below proves **correctness / algebraic** facts (bijections, round-trip, content-preservation). It does **not** prove bit-security, MDS diffusion, or a strong key schedule.

## Three layers (be honest)

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the Lean model** | Bijections, `encrypt6_rt` under Compose-key bijections, PassKey `F_inv ∘ F = id`, and the same round-trip with the **real PassKey schedule** (`encryptDeckFn_rt`). List wrappers used by KATs agree: `encryptDeck_eq_encryptDeckFn`, `decryptDeck_eq_decryptDeckFn`. | Lean kernel. `lake build`. No `sorry`. No `native_decide`. |
| **(b) Vector agreement** | Every deck in `vectors/twodeck_vectors.json` is checked by `lake exe twodeck` against the Lean functions. JSON is generated from a sudoc JS build of `twodeck.sudo`, not hand-copied. | Compiled Lean evaluation (the `twodeck` executable), plus the committed JSON. **Not** kernel `decide`. **Not** a proof that sudo = Lean. |
| **(c) Future: emitter proof** | A sudocode total-fragment Lean emitter should eventually show the sudo text *is* this model. | Does not exist yet. Do not read (b) as a substitute. |

## What is proved

Sorry-free Lean 4.14 theorems. Details and file tags are in [`STONES.md`](STONES.md).

| Stone | Claim | Status |
| --- | --- | --- |
| S1 | Lay/scoop, SumRanks, ShiftRows, GridCycle, Compose are invertible as stated | Proved (GridCycle: `invMix ∘ Mix = id`) |
| S2 | Full / final round and Nr=6 encrypt/decrypt round-trip | Proved under abstract Compose-key bijections; concrete PassKey schedule inherits `encrypt6_rt` |
| S3 | PassKey is deterministic and content-preserving | Proved (`List.Perm`) |
| S4 | PassKey is injective (constructive inverse) | Proved (`Function.LeftInverse` / right inverse). Cycle structure is not. |
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
| S13 | §5.3 bytes ↔ deck | Evidence in `encoding.test.mjs` / `demos/twodeck/cards.js` |
| — | sudo text equals the Lean model | Open; vector agreement is layer (b) only. Future emitter is layer (c). |
| — | `mixColumns ∘ invMixColumns = id` on arbitrary packets | Open (needs image / seat characterization) |

## Lean package

Toolchain **4.14.0**, no Mathlib. From a checkout with [elan](https://github.com/leanprover/elan):

```sh
cd proofs/twodeck/lean
lake build
```

`lake exe twodeck` prints a one-line summary **and** runs the known-answer vector checks. The library target is `TwoDeck`. Namespaces are `TwoDeck`, not a workspace lineage name.

Shipped theorems contain no `sorry` and no `native_decide`. The proofs CI job (`proofs.yml`) runs a sorry / `native_decide` gate, `check_source.py` (JSON `sudo_sha256` vs the current `twodeck.sudo`), `lake build`, and `lake exe twodeck`. It does not gate the Pages demo build. Path filters: `proofs/**`, `primitives/cipher/twodeck/**`, and the workflow file.

### Regenerating vectors

Do not hand-edit `vectors/twodeck_vectors.json` or `lean/TwoDeck/Vectors.lean`. From the repo root, with network enough to clone [sudocode](https://github.com/hacker6284/sudocode) (same compiler as `.github/workflows/pages.yml`):

```sh
proofs/twodeck/vectors/regen.sh
```

That checks out a **pinned** sudocode commit (`SUDOCODE_COMMIT` in `regen.sh`), builds `twodeck.sudo` to JS, evaluates the published sudo tests plus extra KATs, writes the JSON (including `sudo_sha256` of the current `twodeck.sudo` and that sudocode SHA), then emits `Vectors.lean`. CI fails if `sudo_sha256` no longer matches the file. If the JSON is already current:

```sh
python3 proofs/twodeck/vectors/json_to_lean.py          # write Vectors.lean
python3 proofs/twodeck/vectors/json_to_lean.py --check  # CI: stale Lean fails
```

Optional env: `SUDOC=/path/to/sudoc` or `SUDOCODE_DIR=/path/to/sudocode`.

## Reading order

SPEC §6 suggested order: **S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7**, S13 as an encoding property test, and S8–S10 as living evidence. PassKey injectivity is proved here. Merge this PR with [PR #3](https://github.com/hacker6284/cryptoys/pull/3) (or land #3 immediately after) so SPEC §3.7 / S4 name `passKey_leftInverse` / `passKey_rightInverse` in `proofs/twodeck/lean/TwoDeck/PassKey.lean` and stop saying injectivity is open.

### Why PassKey is invertible

At step \(i\) the controller \(C\) is placed on top of the key pile, so the inverse can read it. Every branch (suit-rotate the hand; proper-cut the hand, the key, or neither) depends only on \(C\) and the two pile lengths — hand \(= 51-i\) after the pop, key \(= i\) — never on hidden card identities. So each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. `invPassKeyStep` undoes one step; `passToKeyCutFallbackInv` walks the composition backwards.
