# Scramble proofs

Scramble stays a **teaching / lineage** hash. `scramble_v2` is current (`primitives/hash/scramble/`). This directory does not claim collision resistance, preimage resistance, or any other hash-security property.

## Birthday ceiling

The digest is a seated cube pose: about 65.2 bits, the order of the cube group. A single cube has a birthday collision ceiling around \(2^{32.6}\). The v2 SPEC also records a meet-in-the-middle second-preimage cost around \(2^{33}\). Those figures are honesty about the group size, not theorems in this tree, and not a reason to treat Scramble as a hash with a security level.

There is **no Scramble Lean** in this drop.

## Long-term hash story

A future **multi-cube sponge** is the long-term hash direction. Until that lands as a published primitive, do not read this placeholder as a reduction, an attack-bound proof, or a commitment to a next version number. This PR does not bump Scramble.
