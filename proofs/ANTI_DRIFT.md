# Anti-drift: sudo is normative, Lean algorithms are generated

Sudo (`.sudo` under `primitives/`) is the algorithm. Lean algorithm
definitions are **generated** from those files by the sudocode Lean
backend. They are not a second handwritten model.

This document is the anti-drift contract. It does **not** claim
sudo↔Lean semantic-equivalence theorems. A green `lake build` is not
a security claim.

## Architecture

```text
primitives/**/*.sudo          # normative algorithm
        │
        │  proofs/emit_lean.sh
        │  (sudoc emit-ir -I stdlib  →  protocol-4 envelope
        │   →  backends/lean/emit.py  →  lake)
        ▼
proofs/*/lean/Generated/      # executable Lean (DO NOT EDIT)
        │
        │  proof-only modules (stones, lemmas sudo does not express)
        ▼
proofs/*/lean/<Name>/*.lean   # algebraic ledger, not a second encrypt/Hash
```

| Tree | What lives here | What must not live here |
| --- | --- | --- |
| `lean/Generated/` | Emitted `encrypt` / `passkey` / `v_Hash` / TAP tests. Standalone Lake package. | Hand edits. Proof lemmas. |
| `lean/DoubleDeal/` or `lean/MegaDreifach/` | Stones and lemmas sudo does not express (bijections, PassKey inverse theorems, pad injectivity, …). | A second `encrypt` / `Hash` treated as the algorithm. |

`Generated/` is **not** imported by the proof package. Types do not
match: emitted functions are fuel-total `Except SudoRt.Trap` over
`Array Int`; stones are Fin / `List Nat` algebra. Bridging them is
OPEN (see below). Separation is deliberate so nobody edits a second
encrypt by hand and thinks they changed the cipher.

## How to regenerate

From the repo root:

```sh
proofs/emit_lean.sh              # write both Generated/ trees
proofs/emit_lean.sh --check      # CI: fail if committed Lean is stale
proofs/emit_lean.sh doubledeal   # one algorithm
```

Optional: `SUDOC=/path/to/sudoc` and `SUDOCODE_DIR=/path/to/sudocode`
(the checkout **must** contain `backends/lean/emit.py` at the pin
below). The script clones that pin into `/tmp/sudocode` when needed.

Then:

```sh
cd proofs/doubledeal/lean/Generated && lake build && ./.lake/build/bin/doubledeal_test
cd proofs/megadreifach/lean/Generated && lake build && ./.lake/build/bin/megadreifach_test
```

Expected TAP: DoubleDeal **10/10** (two test-only kind-scan `while`s
stripped under the terminates gate; JS still runs all twelve),
MegaDreifach **11/11**.

## Pin (sudocode main)

| Field | Value |
| --- | --- |
| Repo | [hacker6284/sudocode](https://github.com/hacker6284/sudocode) |
| Branch | `main` |
| Commit | `4286093e791e85e2be0b72b524319ba64bda002b` (file: [`SUDOCODE_LEAN_PIN`](SUDOCODE_LEAN_PIN)) — squash merge of [PR #5](https://github.com/hacker6284/sudocode/pull/5) |
| Spike | [PR #6](https://github.com/hacker6284/sudocode/pull/6) (CONDITIONAL GO) |

This pin is **durable on sudocode main**. `backends/lean/` ships there
as of #5. Lean is still **not** in `ALL_BACKENDS` (unfinished lockstep
peer; out of scope here). The merge includes the `_fs` Flow-binder
shadow fix (a sudo `for s` must not capture the loop payload).

## Terminates gate is on

`proofs/emit_lean.sh` passes `sudoc emit-ir --require terminates` for
DoubleDeal and MegaDreifach. All three public `.sudo` files (DoubleDeal,
MegaDreifach, Scramble) accept that flag on their exports.

Production loops are bounded `for` (PassKey drain over initial
`deck.length`; overflow scans `0 to 3`; MD bigint trim/peel/carry,
φ / even-perm search, Hash MD walk; Scramble pad / apply / evaluate
remainders and `digest_bytes` over the 12-byte buffer). DoubleDeal
test-only `while`s that scan traces by `kind` are stripped under the
gate (JS/Python still run those tests). Generated TAP is the remaining
tests.

Scramble has no Generated Lean in this drop. Its sudo is
terminates-clean; adding a Generated tree is a follow-up.

The registered Lean backend profile is **full peer** (empty
`predicates`): fuel-total `while` / `for` via `SudoRt.natIter`.
Fuel exhaustion is `StackOverflow`, not a hang. That is not a
total-fragment / terminating-subset emitter.

## What this is not

- Not a sudo↔Lean semantic-equivalence theorem.
- Not a claim that `Generated.encrypt` equals the algebraic
  `encrypt6` / `encryptDeck` in `DoubleDeal/`.
- Not a claim that `Generated.v_Hash` equals the algebraic
  `hashBlocks` fold in `MegaDreifach/`.
- Not bit-security, MDS, collision-resistance, or AEAD.
- Not adding Lean to sudocode `ALL_BACKENDS` (peer registration is
  a sudocode follow-up; this repo only consumes the emitter).

## OPEN

| Item | Status |
| --- | --- |
| sudo text = generated Lean (deep embedding / equivalence) | OPEN. TAP agreement is evidence, not a theorem. |
| Algebraic `passToKeyCutFallback` = `Generated.passkey` | OPEN. S3/S4 stay on the list-level proof model. sudo already *tests* `passkey_inv ∘ passkey = id` (generated TAP). |
| Algebraic `encryptDeck` / `encrypt6` = `Generated.encrypt` | OPEN. S2 stays on the Fin-packet skeleton. Generated TAP checks sudo's encrypt/decrypt tests. |
| `--require terminates` on these publics | ON at emit for DoubleDeal and MegaDreifach. All three publics ready (bounded `for`). Scramble has no Generated Lean. |
| PassKey / stone proofs *about* `Except Trap` emitted defs | OPEN. Fuel-total monadic programs are not the Fin algebra the stones use. |
| Scramble generated Lean | Out of this drop. |
| MegaDreifach M13 (proof-package digest = KAT hex) | Still OPEN in the algebraic package (no handwritten `Hash`). Research hexes were refreshed to current sudo; Python and emitted Lean agree. |

## Proofs that remain handwritten

Sudo does not emit theorems. These stay as **proof infrastructure**:

- DoubleDeal S1 layer bijections, S2 abstract / PassKey-schedule
  round-trip on the Fin skeleton, S3/S4 PassKey inverse, S5/S6
  factoradic / CTR prefix, S11 Compose KP, S12 peel.
- MegaDreifach M1–M8/M10–M12 packing, group law, pad, DM algebra.

They are tagged in each file: **proof-only, not the algorithm**.
Edit `.sudo` and regenerate `Generated/` to change `encrypt` or `Hash`.
