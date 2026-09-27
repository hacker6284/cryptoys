# Deprecated algorithms

Vulnerability proofs live here, next to the frozen artifact they attack (see [`../README.md`](../README.md) taxonomy). An algorithm is deprecated first; only then does it collect a vulnerability proof.

| Algorithm | Frozen artifact | Proof | Current replacement |
| --- | --- | --- | --- |
| DoubleDeal v8 | `primitives/cipher/doubledeal/v8/` | [`doubledeal-v8/`](doubledeal-v8/) — same-rank relabelling distinguisher; checkable witness (compiled check of emitted v8 `encrypt`) | DoubleDeal v9 (`primitives/cipher/doubledeal/`; v9 is deprecated, draft; no successor yet) |
| DoubleDeal v9 (**draft, awaiting decision**) | `primitives/cipher/doubledeal/v9/` | [`doubledeal-v9/`](doubledeal-v9/) — K♣↔Q♥ swap distinguisher (≈3.5e-8 per pair on the full cipher, measured); kernel-checked witness on the emitted frozen v9 `encrypt` (`decide!`, stage by stage) | **None yet.** `primitives/cipher/doubledeal/` still holds v9 until a successor is chosen; candidates (analysis only) in [`doubledeal-v9/candidates/CANDIDATES.md`](doubledeal-v9/candidates/CANDIDATES.md) |
