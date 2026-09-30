<!-- Owns: the frozen MegaDreifach v1 Lean package (which v1 theorems survive, what was dropped when the main package moved to v2, how to build and check it). Maintenance rules: ../../../DOCS.md. This file is checked by check_axioms.py --selftest. -->
# MegaDreifach v1 proofs (frozen, deprecated)

Proofs about the deprecated MegaDreifach v1 ([`v1/SPEC.md`](../../../primitives/hash/megadreifach/v1/SPEC.md), [`v1/megadreifach.sudo`](../../../primitives/hash/megadreifach/v1/megadreifach.sudo)), kept after the main package [`../../megadreifach/`](../../megadreifach/README.md) moved to v2. **Nothing here is about v2.**

## Contents

`lean/` is a Lake package (`MegaDreifachV1`, Lean 4.14.0, core only, no Mathlib). It holds the three v1 grip-rule weakness modules and exactly their import closure (74 modules), copied from `proofs/megadreifach/lean` at 75f4d64, the last commit where that package modelled v1, with the namespace renamed `MegaDreifach` → `MegaDreifachV1`. Module docstrings are verbatim from 75f4d64, so file paths in them refer to that tree (for example `lean/MegaDreifach/Security/` is now `lean/MegaDreifachV1/Security/`). `lean/Generated/` is emitted from the frozen `v1/megadreifach.sudo` (`proofs/emit_lean.sh` target `megadreifach-v1`); see [`lean/Generated/README.md`](lean/Generated/README.md).

## What is proved (v1 only)

v1's E_m uses the v1 grip rule, Recipe A: it re-grips by reading one corner cubie, after the card's held-face, noon and Front turns. Measurements and scripts: [`../../megadreifach/security/REPORT.md`](../../megadreifach/security/REPORT.md). None of this is a security claim.

| Result | Status | Cause |
| --- | --- | --- |
| E_m is corner-driven: same corners ⇒ same left-multiplying word; the corner chain is its own ≈90.2-bit MD hash and fixes the top ≈90.2 digest bits | Proved (`emBlock_word`, `dmStep_word`, `foldl_dmBlock_sameCorners`, `digest_top_collision`; `Security/CornerDriven.lean`) | corner-only read |
| Pseudo-collisions of the compression function | Reduction proved: same corners and `(hW)² = (h'W)²` ⇒ equal `dm` outputs (`dmStep_collision_of_sq`, `dmStep_pseudo_collision`; `Security/FreeStart.lean`). That such pairs exist for every block and corner part is a paper argument, demonstrated by `proofs/megadreifach/security/pseudo_collision.py`; it is not a Lean theorem | corner-only read |
| An IV-anchored `Hash` collision: one 28-byte pair (digest `0084d6d1…c34e82`), cards 5 and 7 (Q♠, Q♦) swapped | Kernel-checked for the generated v1 `v_Hash` (`SwapCollision.v_Hash_swap_collision`; only 7-card prefixes are evaluated). The collision rate (≈2^12–2^13 compressions per collision) is measured, not proved: `proofs/megadreifach/security/suit_blind_collision.py` | read after the noon turn |

The closure also re-proves, for v1, the model, Link 2 up to `v_Hash_refines`, the MD reduction and the step-word and parity lemmas; the main package has the v2 versions of these.

## Dropped

When the main package moved to v2, these v1 results were not kept:

* the 8 v1 KAT kernel witnesses (`MegaDreifachHeavy/Kat.lean`; about 8 min of kernel time). No Lean checks the v1 KAT digests any more: the v1 sudo tests (Generated TAP, below) do not assert them, and only the Python `proofs/megadreifach/security/md.py` does;
* the v1 modules outside the closure: `G2`, `Vectors`, `VectorCheck`, `KatSpecCheck`, `Main`, `Security/DigestInj`, `Security/IdealCount`, `Link2/PhiInv`, `Link2/PeelWide`, `Link2/PeelOneThree`, `Link2/ToBePad` and the `Link2` root. All of them are grip-rule independent and live on, for v2, in the main package.

## Build and check

```sh
proofs/emit_lean.sh megadreifach-v1   # or --check
(cd proofs/deprecated/megadreifach-v1/lean/Generated && lake build && ./.lake/build/bin/megadreifach_test)
(cd proofs/deprecated/megadreifach-v1/lean && lake build)
python3 proofs/doubledeal/check_axioms.py megadreifach-v1-deprecated
python3 proofs/doubledeal/security/checks/scan_sorry.py --root proofs/deprecated/megadreifach-v1/lean --exclude Generated
```

The axiom gate audits every theorem of the package (`#audit_all MegaDreifachV1`; only `propext`, `Classical.choice`, `Quot.sound`) and requires the theorems cited above. CI job: `megadreifach-v1-deprecated` in [`proofs.yml`](../../../.github/workflows/proofs.yml).
