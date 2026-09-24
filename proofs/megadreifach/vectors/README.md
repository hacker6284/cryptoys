# MegaDreifach known-answer metadata

`megaminx_hash_kats.json` is the exported KAT file from the soft-lock reference.

This drop checks **metadata** only (pad lengths, block counts, digest width, `|G|`, IV-COOK12 hex) from Lean (`lake exe megadreifach`) and from `primitives/hash/megadreifach/selfcheck.py`.

Full digest equality (stone M13) needs the abs-G2 + F3 runner and is **OPEN**.
