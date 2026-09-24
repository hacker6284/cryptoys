# Proofs

This tree is the library's proof ledger. Specifications under `primitives/` stay normative. Proofs here are obligations: they say what has been machine-checked, what is only evidence, and what is not claimed.

Nothing in this repository is for real use. A green Lean build is not a security claim.

Three layers of evidence, and only the first is a theorem:

1. **Theorems about the Lean model** — bijections, round-trip, PassKey injectivity. Zero `sorry`. The Lean kernel checks these theorems; there is no `native_decide` in the shipped TwoDeck Lean.
2. **Vector agreement** — the same known-answer decks are evaluated in Lean and in `twodeck.sudo` (via the sudoc JS target). This is evidence that the hand-written model matches the conformance implementation on those inputs, **not** a proof that the sudo text equals the Lean model.
3. **Future: emitter proof** — a sudocode total-fragment Lean emitter will be the place to prove that the sudo code *is* the Lean model. That emitter does not exist yet.

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
  twodeck/                  # TwoDeck correctness stones
  megadreifach/             # MegaDreifach correctness stones
  scramble/                 # teaching / lineage placeholder; no Lean
  scm/                      # placeholder until TwoDeck-SCM exists
```

Deprecated algorithms, when they appear, get their own directory under `proofs/` (or a `deprecated/` child) for vulnerability proofs. There are none yet.

## Status

| Primitive | Current version | This tree |
| --- | --- | --- |
| TwoDeck | `primitives/cipher/twodeck/` | Correctness Lean under `twodeck/lean/`. PassKey injectivity is **proved**. Known-answer vectors under `twodeck/vectors/` agree with `twodeck.sudo`. Merge with PR #3 (or #3 immediately after) so SPEC §3.7 / S4 stop saying injectivity is open. |
| MegaDreifach | `primitives/hash/megadreifach/` (front end; `E_m` follow-up) | Correctness Lean under `megadreifach/lean/`. M1–M7 packing/algebra **proved** (M3 even-perm glue still open). M8 is a net-distinctness reduction. M9 / full KAT digests **OPEN**. See `megadreifach/README.md`. A green Lean build is not a security claim. |
| Scramble | `scramble_v2` | Placeholder only. Teaching hash; single-cube birthday ceiling. No Lean. Not bumped. |
| TwoDeck-SCM / SMAC | not in `primitives/` | Stub `scm/README.md`. |

See `twodeck/README.md` for TwoDeck proved-versus-open, and `twodeck/STONES.md` for the SPEC §6 checklist. See `megadreifach/README.md` and `megadreifach/STONES.md` for MegaDreifach.
