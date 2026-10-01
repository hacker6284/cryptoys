<!-- Owns: the proof taxonomy (what may be claimed where), the evidence layers, and the status of each current primitive. Maintenance rules: ../DOCS.md. -->
# Proofs

This tree is the library's proof ledger. Specifications under `primitives/` stay normative. Proofs here are obligations: they say what has been machine-checked, what is only evidence, and what is not claimed.

Nothing in this repository is for real use. A green Lean build is not a security claim.

Sudo is normative. Lean *algorithm* definitions are generated from `*.sudo`
into `proofs/*/lean/Generated/`. See [`ANTI_DRIFT.md`](ANTI_DRIFT.md). This does **not** claim sudo↔Lean semantic-equivalence theorems. The terminates gate is on at emit for DoubleDeal, MegaDreifach, Scramble, DoubleDeal-CBC-HMAC, and BS. All five publics are terminates-ready and have Generated Lean.

Five layers of evidence. (1) and (4) are theorems; (2) and (3) are evidence; (5) is OPEN:

1. **Theorems about the proof-only Lean model** — bijections, round-trip, PassKey injectivity. Zero `sorry`. The Lean kernel checks these theorems; there is no `native_decide` in the shipped DoubleDeal Lean. These modules are **not** the algorithm.
2. **Generated TAP** — `sudoc emit-ir --require terminates` → protocol-4 Lean backend → `lake` → TAP, from the same `.sudo` that JS/Python compile. DoubleDeal: every sudo `test` passes except the two test-only kind-scan `while`s, which the gate strips (JS runs them all); expected counts for the others: [MegaDreifach](megadreifach/README.md#three-layers-be-honest), [Scramble](scramble/README.md#generated-lean), [DoubleDeal-CBC-HMAC](doubledeal-cbc-hmac/README.md#generated-lean), [BS](key_exchange/bs/lean/README.md#generated-lean). Evidence the emitter ran, **not** a sudo=Lean theorem.
3. **Vector agreement (algebraic skeleton vs JS JSON)** — known-answer decks evaluated in the proof package against JSON from the sudoc JS target. Evidence the *skeleton* matches those inputs, **not** a proof it equals `Generated.encrypt`.
4. **Link 2 refinement** — algebraic skeleton equals the generated program on the well-formed domain. DoubleDeal: `drop_front` / `push_front` / `left_rotate` / `right_rotate`; `Generated.passkey` ≃ `passToKeyCutFallback` and `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list; PassKey S3/S4 (multiset, inverse, injectivity) on `Except Trap`; `Generated.encrypt` ≃ `encryptDeck` on `CardBound` messages. MegaDreifach: see [`megadreifach/README.md`](megadreifach/README.md). Not emitter soundness (that stays layer-2 TAP / Link 1). Not bit-security. See [`LINK2.md`](LINK2.md).
5. **Future: Link 1 equivalence** — a theorem that the sudo text *is* the generated Lean. OPEN. Fuel-total `natIter` is not a total-fragment emitter.

## Taxonomy

Four kinds. The first three apply to **current** algorithms. The fourth applies only after an algorithm is **deprecated** or marked broken.

| Kind | What it is | When it belongs here |
| --- | --- | --- |
| **Correctness** | Bijections, encrypt/decrypt round-trip, content-preservation, encoding injectivity. Algebraic facts about the published definition. | Current algorithms, as soon as the claim is honest and the proof is sorry-free. |
| **Reduction** | "Breaking this is as hard as that assumption." | Current algorithms, only when earned. Not in this first drop. |
| **Attack-bounds** | Concrete work estimates (birthday, MITM, distinguishing advantage). | Current algorithms, only when earned as a theorem. Heuristic ceilings already in a SPEC stay SPEC honesty, not proofs. |
| **Vulnerability proofs** | A named attack that *works*, with a checkable witness. | Deprecated algorithms, or a current algorithm whose SPEC is marked broken (filed under `<alg>/security/`). Otherwise, current algorithms do not collect vuln write-ups as a substitute for deprecation. |

Current algorithms get correctness now, and stronger security proofs (reductions, attack-bounds) later if they earn them. They do not get collision-resistance or AES-class numbers from a correctness package.

### What does not belong

- Promoting property tests, avalanche tables, or slide probes to theorems.
- Bit-security slogans ("≈ 2^128") attached to a Lean green light.
- Collision-resistance claims for Scramble.
- Treating a SPEC birthday ceiling as a proved bound.

## Layout

```text
proofs/
  README.md                 # this taxonomy
  doubledeal/               # DoubleDeal correctness stones (+ security/, analysis/, vectors/)
  megadreifach/             # MegaDreifach correctness stones (+ security/: v1 grip-rule weakness report)
  scramble/                 # Generated Lean + teaching / lineage; Link 2 to a hand-written model (+ security/: attacks showing v2 is broken)
  doubledeal-cbc-hmac/      # Generated Lean for HMAC / KDF / pad + Link 2 to a hand-written model
  scm/                      # placeholder; SCM/SMAC stay later (CBC-HMAC is the AEAD)
  key_exchange/bs/          # BS evidence: Python evidence harness, exchanges, key checks, sudo vectors (+ lean/: Generated Lean and Link 2 to a hand-written arithmetic model; scope in lean/README.md)
  audit/                    # core-only #audit_all package shared by the axiom audits
  deprecated/               # vulnerability proofs for deprecated, frozen algorithms
    doubledeal-v8/          # DoubleDeal v8 relabelling distinguisher + witness
    doubledeal-v9/          # DoubleDeal v9 K♣↔Q♥ swap distinguisher + kernel-checked witness (draft)
    doubledeal-v10/         # DoubleDeal v10 GridCycle per-layer parity shortfall + single-deck kernel witness
    doubledeal-v11/         # DoubleDeal v11, superseded (PassKey related-key property; not an attack): frozen vectors + emitted TAP
```

## Status

| Primitive | Current version | This tree |
| --- | --- | --- |
| DoubleDeal | `primitives/cipher/doubledeal/` | **Generated** Lean under `doubledeal/lean/Generated/` (from `doubledeal.sudo`; TAP all-pass under the terminates gate). Proof-only stones under `doubledeal/lean/DoubleDeal/`. Proved versus open: [`doubledeal/README.md`](doubledeal/README.md). Security theorems, the open conjecture and the AES-style roadmap: [`doubledeal/security/README.md`](doubledeal/security/README.md). |
| MegaDreifach | `primitives/hash/megadreifach/` (v2; deprecated v1 frozen in `v1/`) | **Generated** Lean under `megadreifach/lean/Generated/` (from the v2 sudo; [TAP](megadreifach/README.md#three-layers-be-honest)). Proof-only stones under `megadreifach/lean/MegaDreifach/`, about v2. Proved versus open: [`megadreifach/README.md`](megadreifach/README.md). The v1 weakness proofs, frozen: [`deprecated/megadreifach-v1/`](deprecated/megadreifach-v1/README.md). |
| Scramble | `scramble_v2` (**broken**) | **Generated** Lean under `scramble/lean/Generated/` (from `scramble.sudo`; [TAP](scramble/README.md#generated-lean) under the terminates gate). Teaching hash. **Broken**: practical collisions, second preimages and preimages (measured; write-up, scripts and logs in [`scramble/security/`](scramble/security/REPORT.md)). [Link 2](scramble/README.md#link-2-leanscramblev2) proved (correctness of the emitted code against a hand-written model; scope in that README). Not a collision-resistance claim. |
| DoubleDeal-CBC-HMAC | `primitives/aead/doubledeal-cbc-hmac/` | **Generated** Lean under `doubledeal-cbc-hmac/lean/Generated/` (from `doubledeal_cbc_hmac.sudo` + imported MegaDreifach; [TAP](doubledeal-cbc-hmac/README.md#generated-lean)). HMAC / KDF / pad / MAC-input evidence, plus [Link 2](doubledeal-cbc-hmac/README.md#link-2) of every exported function to a hand-written model on byte inputs. No AEAD security theorem. Not SCM. |
| BS | `primitives/key_exchange/bs/` | `bs.sudo` with sudoc-generated vectors cross-checked against the Python evidence harness, which is not a reference ([`key_exchange/bs/vectors/`](key_exchange/bs/vectors/README.md)). **Generated** Lean under `key_exchange/bs/lean/Generated/` ([TAP](key_exchange/bs/lean/README.md#generated-lean) under the terminates gate), and a partial [Link 2](key_exchange/bs/lean/README.md) (the arithmetic, the walk, the received-value check, the key build and reader, and the exchange, against a hand-written arithmetic model, documented in `key_exchange/bs/lean/README.md`). Evidence: Python reference, full exchanges and key checks in [`key_exchange/bs/`](key_exchange/bs/README.md). No security theorem. |
| DoubleDeal-SCM / SMAC | not in `primitives/` | Stub [`scm/README.md`](scm/README.md). Stays later. |
| DoubleDeal v8–v11 (frozen) | `primitives/cipher/doubledeal/v8/` … `v11/` | Vulnerability proofs (v8, v9), a per-layer write-up (v10) and a superseded-not-attacked write-up (v11) under `deprecated/`; see [`deprecated/README.md`](deprecated/README.md). |
