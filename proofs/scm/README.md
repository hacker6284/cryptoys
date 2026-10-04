<!-- Owns: the placeholder for a future DoubleDeal-SCM proof ledger. Maintenance rules: ../../DOCS.md. -->
# DoubleDeal-SCM proofs

Placeholder. DoubleDeal-SCM (and SMAC) are **not** the AEAD that landed. The published authenticated construction is **DoubleDeal-CBC-Sandwich v2** under [`primitives/aead/doubledeal-cbc-hmac/`](../../primitives/aead/doubledeal-cbc-hmac/README.md) (directory name kept from v1; v1, DoubleDeal-CBC-HMAC, is frozen there in `v1/`). SCM / SMAC stay later.

This directory will hold an SCM proof ledger if that product is specified: correctness first, then any reduction or attack-bound that is actually earned. Until then there are no SCM theorems and no tag-security numbers here.

DoubleDeal-CBC-Sandwich itself does not claim a proved MAC/PRF bound (its SPEC §8 gives the argument, relative to unproven heuristic assumptions on MegaDreifach v3, and why it gave no bound on v2). Its evidence is the sudo + JS KATs + Generated TAP under [`proofs/doubledeal-cbc-hmac/`](../doubledeal-cbc-hmac/README.md), not this folder.
