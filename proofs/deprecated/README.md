# Deprecated algorithms

Vulnerability proofs live here, next to the frozen artifact they attack (see [`../README.md`](../README.md) taxonomy). An algorithm is deprecated first; only then does it collect a vulnerability proof.

| Algorithm | Frozen artifact | Proof | Current replacement |
| --- | --- | --- | --- |
| DoubleDeal v8 | `primitives/cipher/doubledeal/v8/` | [`doubledeal-v8/`](doubledeal-v8/) — same-rank relabelling distinguisher; checkable witness (compiled check of emitted v8 `encrypt`) | DoubleDeal v9 (itself deprecated; see next row) |
| DoubleDeal v9 | `primitives/cipher/doubledeal/v9/` | [`doubledeal-v9/`](doubledeal-v9/) — K♣↔Q♥ swap distinguisher (≈3.5e-8 per pair on the full cipher, measured); kernel-checked witness on the emitted frozen v9 `encrypt` (`decide!`, stage by stage) | DoubleDeal v10 (`primitives/cipher/doubledeal/`): position-aware SumRanks (candidate W5c). Candidate history (analysis only): [`doubledeal-v9/candidates/CANDIDATES.md`](doubledeal-v9/candidates/CANDIDATES.md) and [`../doubledeal/analysis/v10-sumranks/`](../doubledeal/analysis/v10-sumranks/) (itself deprecated; see next row) |
| DoubleDeal v10 | `primitives/cipher/doubledeal/v10/` | [`doubledeal-v10/`](doubledeal-v10/) — GridCycle per-layer parity shortfall (K♣↔K♦ survives one GridCycle at 0.262, measured; 1311/1326 swaps above 1/64). **Not** a full-cipher attack (worst 6-round trail ≈2e-17, estimate). Kernel-checked single-deck witness on the emitted frozen v10 `mix_columns` (`decide!`) | DoubleDeal v11 (live `primitives/cipher/doubledeal/SPEC.md`): GridCycle rule 1 + tweak B. Analysis: [`proofs/doubledeal/analysis/v10-gridcycle/`](../doubledeal/analysis/v10-gridcycle/) |
