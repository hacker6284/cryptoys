# Deprecated algorithms

Vulnerability proofs live here, next to the frozen artifact they attack (see [`../README.md`](../README.md) taxonomy). An algorithm is deprecated first; only then does it collect a vulnerability proof.

| Algorithm | Frozen artifact | Proof | Current replacement |
| --- | --- | --- | --- |
| DoubleDeal v8 | `primitives/cipher/doubledeal/v8/` | [`doubledeal-v8/`](doubledeal-v8/) — same-rank relabelling distinguisher; checkable witness (compiled check of emitted v8 `encrypt`) | DoubleDeal v9 (`primitives/cipher/doubledeal/`) |
