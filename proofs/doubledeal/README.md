# DoubleDeal proofs

Normative definition: [`primitives/cipher/doubledeal/SPEC.md`](../../primitives/cipher/doubledeal/SPEC.md). Stones live in SPEC §6. This directory is the correctness ledger for those stones, not a second specification.

DoubleDeal is a toy block cipher. It has no cryptographic security claim. The Lean package below proves **correctness / algebraic** facts (bijections, round-trip, content-preservation). It does **not** prove bit-security, MDS diffusion, or a strong key schedule.

## Layers (be honest)

Sudo is normative. Emitted Lean under `lean/Generated/` is the algorithm.
`lean/DoubleDeal/` is proof-only. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
This does **not** claim sudo↔Lean semantic-equivalence theorems. The
emit terminates gate is still off (repo-wide, until MegaDreifach).
DoubleDeal sudo itself is terminates-ready: PassKey and trace overflow
scans are bounded `for`.

| Layer | What it is | Trust base |
| --- | --- | --- |
| **(a) Theorems about the proof-only model** | Bijections, `encrypt6_rt` under Compose-key bijections, PassKey `F_inv ∘ F = id`, and the same round-trip with the algebraic PassKey schedule (`encryptDeckFn_rt`). | Lean kernel. `lake build` of the proof package. No `sorry`. No `native_decide`. **Not** the cipher. |
| **(b) Generated TAP** | `proofs/emit_lean.sh` → `lake` → `doubledeal_test` (12/12), including sudo's encrypt/decrypt and `passkey_inv` tests. | Compiled emitted Lean. **Not** a sudo=Lean theorem. |
| **(c) Skeleton vs JS JSON** | `lake exe doubledeal` vs `vectors/doubledeal_vectors.json` (from sudoc JS). | Evidence the *skeleton* matches those decks. OPEN that it equals `Generated.encrypt`. |
| **(d) Equivalence** | sudo text = generated Lean, or skeleton = generated. | OPEN. |

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
| S13 | §5.3 bytes ↔ deck | Evidence in `encoding.test.mjs` / `demos/doubledeal/cards.js` |
| — | sudo text equals generated Lean; skeleton equals `Generated.encrypt` / `Generated.passkey` | OPEN. Generated TAP is layer (b), not a theorem. |
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

`lake exe doubledeal` prints a one-line summary **and** runs the skeleton-vs-JSON checks. The library target is `DoubleDeal`. Namespaces are `DoubleDeal`.

Shipped theorems contain no `sorry` and no `native_decide`. The proofs CI job (`proofs.yml`) also emits Lean from `doubledeal.sudo` against the pin, builds `Generated/`, and runs TAP. Path filters: `proofs/**`, `primitives/cipher/doubledeal/**`, `tools/emit_lean.py`, and the workflow file.

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

## Reading order

SPEC §6 suggested order: **S1 → S2 → S12 → S3 → S4 → S5 → S6 → S11 → S7**, S13 as an encoding property test, and S8–S10 as living evidence. PassKey injectivity is proved on the **proof-only** list model. OPEN: that model equals `Generated.passkey`. sudo already tests `passkey_inv` on several decks in Generated TAP.

### Why PassKey is invertible

At step \(i\) the controller \(C\) is placed on top of the key pile, so the inverse can read it. Every branch (suit-rotate the hand; proper-cut the hand, the key, or neither) depends only on \(C\) and the two pile lengths — hand \(= 51-i\) after the pop, key \(= i\) — never on hidden card identities. So each step is a bijection on \((\mathrm{hand},\mathrm{key})\) states of those sizes, and \(F\) is their composition. `invPassKeyStep` undoes one step; `passToKeyCutFallbackInv` walks the composition backwards.
