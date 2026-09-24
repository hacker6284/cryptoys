# Scramble proofs

Scramble stays a **teaching / lineage** hash. `scramble_v2` is current (`primitives/hash/scramble/`). This directory does not claim collision resistance, preimage resistance, or any other hash-security property.

Sudo is normative. Emitted Lean under `lean/Generated/` is the
algorithm. See [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md). This does
**not** claim sudo↔Lean semantic-equivalence theorems. The emit
terminates gate is on. Production loops are bounded `for`.

## Birthday ceiling

The digest is a seated cube pose: about 65.2 bits, the order of the cube group. A single cube has a birthday collision ceiling around \(2^{32.6}\). The v2 SPEC also records a meet-in-the-middle second-preimage cost around \(2^{33}\). Those figures are honesty about the group size, not theorems in this tree, and not a reason to treat Scramble as a hash with a security level.

## Generated Lean

Do not edit `lean/Generated/` by hand. From the repo root:

```sh
proofs/emit_lean.sh scramble
cd proofs/scramble/lean/Generated && lake build && ./.lake/build/bin/scramble_test
```

Expected TAP: **15/15**. Pin and regenerating: [`../ANTI_DRIFT.md`](../ANTI_DRIFT.md).
There is no algebraic proof package next door (no Link-2 refinement).

## Long-term hash story

A future **multi-cube sponge** is the long-term hash direction. Until that lands as a published primitive, do not read this directory as a reduction, an attack-bound proof, or a commitment to a next version number.
