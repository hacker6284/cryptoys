# DoubleDeal-SCM proofs

Placeholder. DoubleDeal-SCM (and SMAC) are **not** the AEAD that landed. The published authenticated construction is **DoubleDeal-CBC-HMAC** under `primitives/aead/doubledeal-cbc-hmac/`. SCM / SMAC stay later.

This directory will hold an SCM proof ledger if that product is specified: correctness first, then any reduction or attack-bound that is actually earned. Until then there are no SCM theorems and no tag-security numbers here.

DoubleDeal-CBC-HMAC itself does not claim a MAC/PRF theorem. Its evidence is the sudo + JS KATs + Generated TAP under `proofs/doubledeal-cbc-hmac/`, not this folder.
