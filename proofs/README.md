# Proofs

This tree is the library's proof ledger. Specifications under `primitives/` stay normative. Proofs here are obligations: they say what has been machine-checked, what is only evidence, and what is not claimed.

Nothing in this repository is for real use. A green Lean build is not a security claim.

Sudo is normative. Lean *algorithm* definitions are generated from `*.sudo`
into `proofs/*/lean/Generated/`. See [`ANTI_DRIFT.md`](ANTI_DRIFT.md). This
does **not** claim sudo↔Lean semantic-equivalence theorems. The terminates
gate is on at emit for DoubleDeal, MegaDreifach, Scramble, and
DoubleDeal-CBC-HMAC. All four publics are terminates-ready and have
Generated Lean.

Five layers of evidence. (1) and (4) are theorems; (2) and (3) are evidence; (5) is OPEN:

1. **Theorems about the proof-only Lean model** — bijections, round-trip, PassKey injectivity. Zero `sorry`. The Lean kernel checks these theorems; there is no `native_decide` in the shipped DoubleDeal Lean. These modules are **not** the algorithm.
2. **Generated TAP** — `sudoc emit-ir --require terminates` → protocol-4 Lean backend → `lake` → TAP, from the same `.sudo` that JS/Python compile. DoubleDeal 10/10 (two test-only kind-scan `while`s stripped under the gate; JS still runs all twelve), MegaDreifach 11/11, Scramble 15/15, DoubleDeal-CBC-HMAC 11/11. Evidence the emitter ran, **not** a sudo=Lean theorem.
3. **Vector agreement (algebraic skeleton vs JS JSON)** — known-answer decks evaluated in the proof package against JSON from the sudoc JS target. Evidence the *skeleton* matches those inputs, **not** a proof it equals `Generated.encrypt`.
4. **Link 2 refinement** — algebraic skeleton equals the generated program on the well-formed domain. DoubleDeal: `drop_front` / `push_front` / `left_rotate` / `right_rotate`; `Generated.passkey` ≃ `passToKeyCutFallback` and `Generated.passkey_inv` ≃ `passToKeyCutFallbackInv` on every well-formed list. NEXT is encrypt refinement. Not emitter soundness (that stays layer-2 TAP / Link 1). Not bit-security. See [`LINK2.md`](LINK2.md).
5. **Future: Link 1 equivalence** — a theorem that the sudo text *is* the generated Lean. OPEN. Fuel-total `natIter` is not a total-fragment emitter.

## Taxonomy

Four kinds. The first three apply to **current** algorithms. The fourth applies only after an algorithm is **deprecated**.

| Kind | What it is | When it belongs here |
| --- | --- | --- |
| **Correctness** | Bijections, encrypt/decrypt round-trip, content-preservation, encoding injectivity. Algebraic facts about the published definition. | Current algorithms, as soon as the claim is honest and the proof is sorry-free. |
| **Reduction** | "Breaking this is as hard as that assumption." | Current algorithms, only when earned. Not in this first drop. |
| **Attack-bounds** | Concrete work estimates (birthday, MITM, distinguishing advantage). | Current algorithms, only when earned as a theorem. Heuristic ceilings already in a SPEC stay SPEC honesty, not proofs. |
| **Vulnerability proofs** | A named attack that *works*, with a checkable witness. | **Deprecated** algorithms only. Deprecate first; then file the proof next to that frozen artifact. Current algorithms do not collect vuln write-ups as a substitute for deprecation. |

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
  doubledeal/               # DoubleDeal correctness stones
  megadreifach/             # MegaDreifach correctness stones
  scramble/                 # Generated Lean + teaching / lineage; no algebraic stones
  doubledeal-cbc-hmac/      # Generated Lean for HMAC / KDF / pad (no algebraic stones)
  scm/                      # placeholder; SCM/SMAC stay later (CBC-HMAC is the AEAD)
```

Deprecated algorithms, when they appear, get their own directory under `proofs/` (or a `deprecated/` child) for vulnerability proofs. There are none yet.

## Status

| Primitive | Current version | This tree |
| --- | --- | --- |
| DoubleDeal | `primitives/cipher/doubledeal/` | **Generated** Lean under `doubledeal/lean/Generated/` (from `doubledeal.sudo`; TAP 10/10 under the terminates gate). Proof-only stones under `doubledeal/lean/DoubleDeal/`. PassKey injectivity is **proved** on the list model (PR #3). Link 2: `Generated.passkey` / `passkey_inv` ≃ that model on every well-formed list. NEXT is encrypt refinement. |
| MegaDreifach | `primitives/hash/megadreifach/` (SPEC + `megadreifach.sudo` + KATs) | **Generated** Lean under `megadreifach/lean/Generated/` (TAP 11/11). Proof-only stones under `megadreifach/lean/MegaDreifach/`. M1–M7 packing/algebra **proved** (M3 even-perm glue still open). M8 is a net-distinctness reduction. M9 / M13 full KAT digests in the proof package **OPEN**. Research Hash hexes refreshed to current sudo. A green Lean build is not a security claim. |
| Scramble | `scramble_v2` | **Generated** Lean under `scramble/lean/Generated/` (from `scramble.sudo`; TAP 15/15 under the terminates gate). Teaching hash; single-cube birthday ceiling. No algebraic stones. Not a collision-resistance claim. |
| DoubleDeal-CBC-HMAC | `primitives/aead/doubledeal-cbc-hmac/` | **Generated** Lean under `doubledeal-cbc-hmac/lean/Generated/` (from `doubledeal_cbc_hmac.sudo` + imported MegaDreifach; TAP 11/11). HMAC / KDF / pad / MAC-input evidence. No Link 2. No AEAD security theorem. Not SCM. |
| DoubleDeal-SCM / SMAC | not in `primitives/` | Stub `scm/README.md`. Stays later. |

See `doubledeal/README.md` for DoubleDeal proved-versus-open, and `doubledeal/STONES.md` for the SPEC §6 checklist. See `megadreifach/README.md` and `megadreifach/STONES.md` for MegaDreifach.
